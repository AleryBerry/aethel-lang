//! Root module for the Aethel compiler (Lexer, Parser/AST, Sema, MIR emitter, and Zig backend).
pub const lexer = @import("lexer.zig");
pub const ast = @import("ast.zig");
pub const parser = @import("parser.zig");
pub const int_range = @import("int_range.zig");
pub const layout = @import("layout.zig");
pub const sema = @import("sema.zig");
pub const mir = @import("mir.zig");
pub const codegen_zig = @import("codegen_zig.zig");

pub const Lexer = lexer.Lexer;
pub const Token = lexer.Token;
pub const Loc = lexer.Loc;
pub const LineCol = lexer.LineCol;
pub const computeLineCol = lexer.computeLineCol;
pub const ContextualKeyword = lexer.ContextualKeyword;
pub const IntWidth = lexer.IntWidth;
pub const parseIntWidth = lexer.parseIntWidth;
pub const PrimitiveType = lexer.PrimitiveType;
pub const Ast = ast.Ast;
pub const parse = parser.parse;
pub const CheckedModule = sema.CheckedModule;
pub const check = sema.analyze;
pub const emitMir = mir.emitMir;
pub const emitZig = codegen_zig.emitZig;

test {
    _ = @import("lexer_test.zig");
    _ = @import("parser_test.zig");
    _ = @import("sema_test.zig");
    _ = @import("codegen_test.zig");
}
