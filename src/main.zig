const std = @import("std");

const iter = @import("iter");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{}) = .{};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    var stdout_buffer: [1024]u8 = undefined;
    var stdout_writer = std.fs.File.stdout().writer(&stdout_buffer);
    const stdout = &stdout_writer.interface;

    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);
    if (args.len != 2) {
        return error.UsageError; // TODO: more verbose
    }
    const filename = args[1];

    var file = try std.fs.cwd().openFile(filename, .{});
    defer file.close();

    const prog = try file.readToEndAlloc(alloc, std.math.maxInt(u32));
    defer alloc.free(prog);

    const source = try iter.compile(alloc, prog, .{});
    defer alloc.free(source);

    try stdout.print("{s}", .{source});
    try stdout.flush();
}
