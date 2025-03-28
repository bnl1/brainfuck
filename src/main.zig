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
        return FAILURE;
    };
    defer bf.deinit();

    IO.init();
    defer IO.deinit();

    const bin = Compiler.codegen(allocator, compiled_source) catch @panic("OOM");
    defer allocator.free(bin);

    const elf = Compiler.createElf(allocator, bin) catch @panic("OOM");
    defer allocator.free(elf);

    var out_file = std.fs.cwd().createFile("out.bin", .{}) catch @panic("FILE");
    defer out_file.close();

    out_file.writeAll(elf) catch |err| @panic(@errorName(err));

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
        @setRuntimeSafety(false);
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
                    const left = bracket_stack.pop() orelse {
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

const Compiler = struct {
    const MOV_RAX_IMM64 = &.{ 0x48, 0xB8 };
    const SUB_RSP_RAX = &.{ 0x48, 0x29, 0xC4 };
    const ADD_RSP_RAX = &.{ 0x48, 0x01, 0xC4 };
    const ADD_BYTE_RSP_AL = &.{ 0x00, 0x04, 0x24 };
    const SUB_BYTE_PTR_AL = &.{ 0x28, 0x04, 0x24 };
    const MOV_AL_BYTE_RSP = &.{ 0x8A, 0x04, 0x24 };
    const TEST_AL_AL = &.{ 0x84, 0xC0 };
    const JZ_REL32 = &.{ 0x0F, 0x84 };
    const JNZ_REL32 = &.{ 0x0F, 0x85 };
    const MOV_RAX_IMM32 = &.{0xB8};
    const MOV_RDI_IMM32 = &.{0xBF};
    const MOV_RSI_RSP = &.{ 0x48, 0x89, 0xE6 };
    const MOV_RDX_IMM32 = &.{0xBA};
    const SYSCALL = &.{ 0x0F, 0x05 };
    const MOV_EAX_IMM32 = &.{0xB8};
    const XOR_RDI_RDI = &.{ 0x48, 0x31, 0xFF };
    const MOV_ECX_IMM32 = &.{0xB9};
    const MOV_RAX_RCX = &.{ 0x48, 0x89, 0xC8 };
    const NEG_RAX = &.{ 0x48, 0xF7, 0xD8 };
    const MOV_BYTE_RSP_PLUS_RAX_PLUS_ONE_ZERO = &.{ 0xC6, 0x44, 0x04, 0x01, 0x00 };
    const LOOP_F3 = &.{ 0xE2, 0xF3 };
    const MOV_AL_IMM8 = &.{0xB0};

    const SYS_EXIT = 60;

    pub fn codegen(
        allocator: Allocator,
        ir_source: []const BFIR,
    ) Allocator.Error![]u8 {
        var bin = ArrayList(u8).init(allocator);
        errdefer bin.deinit();
        try bin.ensureTotalCapacity(0x10000);

        var addr = ArrayList(usize).init(allocator);
        defer addr.deinit();
        try addr.ensureTotalCapacity(0x10000);

        // TODO: don't use stack, we cannot control it's size
        // rsp - ptr
        // [rsp] - mem
        //

        // zeros out some stack memory
        bin.appendSliceAssumeCapacity(MOV_ECX_IMM32);
        bin.writer().writeInt(u32, 0xFFFF, .little) catch unreachable;
        bin.appendSliceAssumeCapacity(MOV_RAX_RCX);
        bin.appendSliceAssumeCapacity(NEG_RAX);
        bin.appendSliceAssumeCapacity(MOV_BYTE_RSP_PLUS_RAX_PLUS_ONE_ZERO);
        bin.appendSliceAssumeCapacity(LOOP_F3);

        for (ir_source) |op| {
            switch (op) {
                .ptr_inc => |val| {
                    bin.appendSliceAssumeCapacity(MOV_RAX_IMM64);
                    bin.writer().writeInt(usize, val, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(SUB_RSP_RAX);
                },
                .ptr_dec => |val| {
                    bin.appendSliceAssumeCapacity(MOV_RAX_IMM64);
                    bin.writer().writeInt(usize, val, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(ADD_RSP_RAX);
                },
                .mem_inc => |val| {
                    bin.appendSliceAssumeCapacity(MOV_AL_IMM8);
                    bin.writer().writeInt(u8, @intCast(val % 256), .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(ADD_BYTE_RSP_AL);
                },
                .mem_dec => |val| {
                    bin.appendSliceAssumeCapacity(MOV_AL_IMM8);
                    bin.writer().writeInt(u8, @intCast(val % 256), .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(SUB_BYTE_PTR_AL);
                },
                .left_b => {
                    bin.appendSliceAssumeCapacity(MOV_AL_BYTE_RSP);
                    bin.appendSliceAssumeCapacity(TEST_AL_AL);
                    bin.appendSliceAssumeCapacity(JZ_REL32);
                    addr.appendAssumeCapacity(bin.items.len);
                    bin.writer().writeInt(i32, 0, .little) catch unreachable;
                },
                .right_b => {
                    bin.appendSliceAssumeCapacity(MOV_AL_BYTE_RSP);
                    bin.appendSliceAssumeCapacity(TEST_AL_AL);
                    bin.appendSliceAssumeCapacity(JNZ_REL32);
                    const lbrace = addr.pop().?;
                    const rbrace = bin.items.len;
                    const lbrace_rel: i32 = @truncate(
                        @as(isize, @intCast(lbrace)) - @as(isize, @intCast(rbrace)),
                    );
                    bin.writer().writeInt(i32, lbrace_rel, .little) catch unreachable;
                    var array: [4]u8 = undefined;
                    std.mem.writeInt(u32, &array, @truncate(rbrace - lbrace), .little);
                    @memcpy(bin.items[lbrace .. lbrace + 4], array[0..4]);
                },
                .out => {
                    bin.appendSliceAssumeCapacity(MOV_RAX_IMM32);
                    bin.writer().writeInt(u32, 1, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(MOV_RDI_IMM32);
                    bin.writer().writeInt(u32, 1, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(MOV_RSI_RSP);
                    bin.appendSliceAssumeCapacity(MOV_RDX_IMM32);
                    bin.writer().writeInt(u32, 1, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(SYSCALL);
                },
                .in => {
                    bin.appendSliceAssumeCapacity(MOV_RAX_IMM32);
                    bin.writer().writeInt(u32, 0, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(MOV_RDI_IMM32);
                    bin.writer().writeInt(u32, 0, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(MOV_RSI_RSP);
                    bin.appendSliceAssumeCapacity(MOV_RDX_IMM32);
                    bin.writer().writeInt(u32, 1, .little) catch unreachable;
                    bin.appendSliceAssumeCapacity(SYSCALL);
                },
                .debug => std.log.scoped(.compile).warn("Compilation mode does not support '#'", .{}),
            }
        }

        // calling exit(0)
        bin.appendSliceAssumeCapacity(MOV_EAX_IMM32);
        bin.writer().writeInt(i32, SYS_EXIT, .little) catch unreachable;
        bin.appendSliceAssumeCapacity(XOR_RDI_RDI);
        bin.appendSliceAssumeCapacity(SYSCALL);

        return try bin.toOwnedSlice();
    }

    pub fn createElf(
        allocator: Allocator,
        binary: []const u8,
    ) Allocator.Error![]u8 {
        const elf = std.elf;

        var elf_bin = std.ArrayList(u8).init(allocator);
        errdefer elf_bin.deinit();
        try elf_bin.ensureTotalCapacity(
            binary.len + @sizeOf(elf.Elf64_Ehdr) + @sizeOf(elf.Elf64_Phdr) + 0x1000,
        );

        var ehdr: elf.Elf64_Ehdr = undefined;
        var phdr: elf.Elf64_Phdr = undefined;

        @memset(ehdr.e_ident[0..], 0);
        @memcpy(ehdr.e_ident[0..4], elf.MAGIC);
        ehdr.e_ident[elf.EI_CLASS] = elf.ELFCLASS64;
        ehdr.e_ident[elf.EI_DATA] = elf.ELFDATA2LSB;
        ehdr.e_ident[elf.EI_VERSION] = 0x01;
        ehdr.e_type = elf.ET.EXEC;
        ehdr.e_machine = elf.EM.X86_64;
        ehdr.e_version = 1;
        ehdr.e_entry = 0x10000;
        ehdr.e_phoff = @sizeOf(elf.Elf64_Ehdr);
        ehdr.e_shoff = 0;
        ehdr.e_flags = 0;
        ehdr.e_ehsize = @sizeOf(elf.Elf64_Ehdr);
        ehdr.e_phentsize = @sizeOf(elf.Elf64_Phdr);
        ehdr.e_phnum = 1;
        ehdr.e_shentsize = 0;
        ehdr.e_shnum = 0;
        ehdr.e_shstrndx = 0;

        phdr.p_type = elf.PT_LOAD;
        phdr.p_flags = elf.PF_X | elf.PF_R;
        phdr.p_offset = 0x1000;
        phdr.p_vaddr = 0x10000;
        phdr.p_paddr = phdr.p_vaddr;
        phdr.p_filesz = binary.len;
        phdr.p_memsz = binary.len;
        phdr.p_align = 0x1000;

        elf_bin.appendSliceAssumeCapacity(std.mem.asBytes(&ehdr));
        elf_bin.appendSliceAssumeCapacity(std.mem.asBytes(&phdr));
        elf_bin.appendNTimesAssumeCapacity(0, 0x1000 - elf_bin.items.len);

        elf_bin.appendSliceAssumeCapacity(binary);

        return try elf_bin.toOwnedSlice();
    }
};
