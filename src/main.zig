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
    const sub_path = args[1];

    const prog = try iter.preprocess(alloc, sub_path);
    defer alloc.free(prog);

    const source = try iter.compile(alloc, prog, .{});
    defer alloc.free(source);

    try stdout.print("{s}", .{source});
    try stdout.flush();
}
