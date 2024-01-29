const std = @import("std");

const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

const BF_MEMORY = 0x8000;

// TODO: think about debug mode

const SUCCESS = 0;
const FAILURE = 255;

pub fn main() u8 {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer if (gpa.deinit() == .leak) {
        std.log.err("Leak detected!", .{});
    };
    const allocator = gpa.allocator();

    const source: []const u8 = blk: {
        var args = std.process.argsWithAllocator(allocator) catch @panic("OOM");
        defer args.deinit();

        _ = args.skip(); // argv[0]
        var file = if (args.next()) |filename|
            std.fs.cwd().openFile(filename, .{}) catch |err| {
                std.log.err("File open failed: {s}", .{@errorName(err)});
                return FAILURE;
            }
        else
            std.io.getStdIn();
        defer file.close();

        break :blk file.readToEndAlloc(
            allocator,
            std.math.maxInt(usize),
        ) catch |err| {
            std.log.err("File read failed: {s}", .{@errorName(err)});
            return FAILURE;
        };
    };
    defer allocator.free(source);

    var compile_diag: BFIR.Diagnostics = undefined;
    const compiled_source = BFIR.compile(
        source,
        allocator,
        &compile_diag,
    ) catch |err| switch (err) {
        BFIR.Error.OutOfMemory => {
            std.log.err("{s}", .{@errorName(err)});
            return FAILURE;
        },
        BFIR.Error.compileError => {
            std.log.scoped(.compile).err(
                "{s} at {}",
                .{ compile_diag.msg, compile_diag.byte_offset },
            );
            return FAILURE;
        },
    };
    defer allocator.free(compiled_source);

    var bf = BfMachine.init(allocator, BF_MEMORY) catch |err| {
        std.log.err("{s}", .{@errorName(err)});
        std.os.exit(FAILURE);
    };
    defer bf.deinit();

    IO.init();
    defer IO.deinit();

    bf.run(compiled_source, true) catch |err| switch (err) {
        BfMachine.Error.tapeOverrun => {
            std.log.scoped(.runtime).err("tape overrun", .{});
            return FAILURE;
        },
    };

    return SUCCESS;
}

const BfMachine = struct {
    allocator: std.mem.Allocator,
    pc: usize = 0,
    ptr: usize = 0,
    mem: []u8 = undefined,

    pub fn init(
        allocator: std.mem.Allocator,
        tape_length: usize,
    ) Allocator.Error!BfMachine {
        return .{
            .allocator = allocator,
            .mem = try allocator.alloc(u8, tape_length),
        };
    }

    pub fn deinit(self: *BfMachine) void {
        self.allocator.free(self.mem);
    }

    // TODO: think about adding diagnostics
    //  pros: error messages
    //  cons: offset into compiled_source is useless. Also, I can just read pc
    pub fn run(
        self: *BfMachine,
        compiled_source: []BFIR,
        clear_memory: bool,
    ) Error!void {
        if (clear_memory) @memset(self.mem, 0);

        while (self.pc < compiled_source.len) {
            try self.execute(compiled_source[self.pc]);
        }
    }

    fn execute(self: *BfMachine, op: BFIR) Error!void {
        switch (op) {
            .ptr_inc => |n| {
                if (self.ptr + n >= self.mem.len) return Error.tapeOverrun;
                self.ptr += n;
            },
            .ptr_dec => |n| {
                if (self.ptr < n) return Error.tapeOverrun;
                self.ptr -= n;
            },
            .mem_inc => |n| self.mem[self.ptr] +%= @intCast(n % std.math.maxInt(u8)),
            .mem_dec => |n| self.mem[self.ptr] -%= @intCast(n % std.math.maxInt(u8)),
            .out => IO.putc(self.mem[self.ptr]),
            .in => self.mem[self.ptr] = IO.getc(),
            .left_b => |n| if (self.mem[self.ptr] == 0) {
                self.pc = n;
            },
            .right_b => |n| if (self.mem[self.ptr] != 0) {
                self.pc = n;
            },
            .debug => self.debug_dump(),
        }
        self.pc += 1;
    }

    const Error = error{
        tapeOverrun,
    };

    fn debug_dump(self: BfMachine) void {
        std.debug.print("\n", .{});
        std.debug.print("REGS:\n", .{});
        std.debug.print("PC: {}\tPTR: {}\n", .{ self.pc, self.ptr });
        std.debug.print("MEMORY:\n", .{});
        std.debug.print("{any}\n", .{self.mem[self.ptr -| 10..self.ptr +| 10]});
        std.debug.print("CURRENT VALUE: {} {c}\n", .{
            self.mem[self.ptr],
            self.mem[self.ptr],
        });
    }
};

/// brainfuck intermediate representation
const BFIR = union(enum) {
    ptr_inc: usize,
    ptr_dec: usize,
    mem_inc: usize,
    mem_dec: usize,
    out,
    in,
    left_b: usize,
    right_b: usize,
    debug,

    fn compile(
        source: []const u8,
        allocator: std.mem.Allocator,
        diag: *Diagnostics,
    ) Error![]BFIR {
        var ir = ArrayList(BFIR).init(allocator);
        errdefer ir.deinit();
        try ir.ensureTotalCapacity(source.len);

        var bracket_stack = ArrayList(usize).init(allocator);
        defer bracket_stack.deinit();
        try bracket_stack.ensureTotalCapacity(source.len);

        var i: usize = 0;
        while (i < source.len) : (i += 1) {
            const op = source[i];
            const ir_op: BFIR = switch (op) {
                inline '>', '<', '+', '-' => |c| blk: {
                    const n = consumeWhile(source[i..], op);
                    i += n - 1;
                    break :blk charToOp(c, n);
                },
                '.' => .out,
                ',' => .in,
                '#' => .debug,
                '[' => blk: {
                    bracket_stack.appendAssumeCapacity(ir.items.len);
                    break :blk .{ .left_b = undefined };
                },
                ']' => blk: {
                    const left = bracket_stack.popOrNull() orelse {
                        diag.byte_offset = i;
                        diag.msg = "Unmatched ']'";
                        return Error.compileError;
                    };
                    ir.items[left].left_b = ir.items.len;
                    break :blk .{ .right_b = left };
                },
                else => continue,
            };

            ir.appendAssumeCapacity(ir_op);
        }

        if (bracket_stack.items.len != 0) {
            diag.byte_offset = i;
            diag.msg = "Unmatched '[' remaining";
            return error.compileError;
        }
        return try ir.toOwnedSlice();
    }

    const Diagnostics = struct {
        byte_offset: usize,
        msg: []const u8,
    };

    const Error = error{compileError} || Allocator.Error;

    fn charToOp(comptime c: u8, n: usize) BFIR {
        const field = switch (c) {
            '>' => "ptr_inc",
            '<' => "ptr_dec",
            '+' => "mem_inc",
            '-' => "mem_dec",
            else => unreachable,
        };
        return @unionInit(BFIR, field, n);
    }
};

fn consumeWhile(slice: []const u8, c: u8) usize {
    var n: usize = 0;
    while (n < slice.len and slice[n] == c) n += 1;

    return n;
}

const IO = struct {
    var buffered_reader: std.io.BufferedReader(
        4096,
        @TypeOf(std.io.getStdIn().reader()),
    ) = undefined;
    var buffered_writer: std.io.BufferedWriter(
        4096,
        @TypeOf(std.io.getStdOut().writer()),
    ) = undefined;

    pub fn init() void {
        buffered_writer = std.io.bufferedWriter(std.io.getStdOut().writer());
        buffered_reader = std.io.bufferedReader(std.io.getStdIn().reader());
    }

    pub fn deinit() void {
        buffered_writer.flush() catch {};
    }

    pub fn putc(c: u8) void {
        buffered_writer.writer().writeByte(c) catch {};
        if (c == '\n') buffered_writer.flush() catch {};
    }

    pub fn getc() u8 {
        buffered_writer.flush() catch {};
        return buffered_reader.reader().readByte() catch 0;
    }
};
