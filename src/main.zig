const std = @import("std");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer if (gpa.deinit() == .leak) {
        std.log.err("Leak detected!", .{});
    };
    const allocator = gpa.allocator();

    const source: []const u8 = blk: {
        var args = try std.process.argsWithAllocator(allocator);
        defer args.deinit();

        _ = args.skip(); // argv[0]
        var file = if (args.next()) |filename|
            try std.fs.cwd().openFile(filename, .{})
        else
            std.io.getStdIn();
        defer file.close();

        break :blk try file.readToEndAlloc(allocator, std.math.maxInt(usize));
    };
    defer allocator.free(source);

    var bf = BfMachine.init(allocator, 0x8000);
    defer bf.deinit();

    bf.run(source);
}

const BfMachine = struct {
    allocator: std.mem.Allocator,
    pc: usize = 0,
    ptr: usize = 0,
    mem: []u8 = undefined,

    pub fn init(allocator: std.mem.Allocator, tape_length: usize) BfMachine {
        return .{
            .allocator = allocator,
            .mem = allocator.alloc(u8, tape_length) catch @panic("OOM"),
        };
    }

    pub fn deinit(self: *BfMachine) void {
        self.allocator.free(self.mem);
    }

    pub fn run(self: *BfMachine, src: []const u8) void {
        @memset(self.mem, 0);
        const compiled_source = BFIR.compile(src, self.allocator);
        defer self.allocator.free(compiled_source);

        while (self.pc < compiled_source.len) {
            self.execute(compiled_source[self.pc]);
        }
    }

    fn execute(self: *BfMachine, op: BFIR) void {
        switch (op) {
            .ptr_inc => |n| {
                if (self.ptr + n >= self.mem.len) @panic("Tape overflow");
                self.ptr += n;
            },
            .ptr_dec => |n| {
                if (self.ptr < n) @panic("Tape underflow");
                self.ptr -= n;
            },
            .mem_inc => |n| self.mem[self.ptr] +%= @intCast(n % std.math.maxInt(u8)),
            .mem_dec => |n| self.mem[self.ptr] -%= @intCast(n % std.math.maxInt(u8)),
            .out => _ = std.io.getStdOut().write(self.mem[self.ptr .. self.ptr + 1]) catch @panic("Write failed"),
            .in => _ = std.io.getStdIn().read(self.mem[self.ptr .. self.ptr + 1]) catch @panic("Read failed"),
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

    fn debug_dump(self: BfMachine) void {
        std.debug.print("\n", .{});
        std.debug.print("REGS:\n", .{});
        std.debug.print("PC: {}\tPTR: {}\n", .{ self.pc, self.ptr });
        std.debug.print("MEMORY:\n", .{});
        std.debug.print("{any}\n", .{self.mem[self.ptr -| 10..self.ptr +| 10]});
        std.debug.print("CURRENT VALUE: {} {c}\n", .{ self.mem[self.ptr], self.mem[self.ptr] });
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

    fn compile(source: []const u8, allocator: std.mem.Allocator) []BFIR {
        var ir = std.ArrayList(BFIR).init(allocator);
        errdefer ir.deinit();

        var bracket_stack = std.ArrayList(usize).init(allocator);
        defer bracket_stack.deinit();

        var i: usize = 0;
        while (i < source.len) : (i += 1) {
            const op = source[i];
            const ir_op: BFIR = switch (op) {
                inline '>', '<', '+', '-' => |c| blk: {
                    const n = consumeWhile(source[i..], op);
                    i += n - 1;
                    break :blk char_to_op(c, n);
                },
                '.' => .out,
                ',' => .in,
                '#' => .debug,
                '[' => blk: {
                    bracket_stack.append(ir.items.len) catch |err| @panic(@errorName(err));
                    break :blk .{ .left_b = undefined };
                },
                ']' => blk: {
                    const left = bracket_stack.popOrNull() orelse
                        std.debug.panic("Unmatched bracket at {}", .{i});
                    ir.items[left].left_b = ir.items.len;
                    break :blk .{ .right_b = left };
                },
                else => continue,
            };

            ir.append(ir_op) catch |err| @panic(@errorName(err));
        }

        if (bracket_stack.items.len != 0) @panic("Unmatched left brackets remaining");

        return ir.toOwnedSlice() catch |err| @panic(@errorName(err));
    }

    fn char_to_op(comptime c: u8, n: usize) BFIR {
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
