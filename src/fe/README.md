# Sisal Frontend Parser & Lexer (`src/fe`)

The Sisal 2.0 frontend parser and lexer implement the formal Sisal grammar and AST mapping:

1. **Sisal 1.2 / 2.0 Grammar & AST**:
   - The Menhir parser (`parse.mly`) and OCamllex lexer (`lex.mll`) implement the formal Sisal specification.
   - Converts source text directly into typed AST variant definitions (`src/ir/ast.ml`).

2. **Union Tag & Field Scoping**:
   - Tag names in `union` types and field names in `record` types are scoped within their respective algebraic type definitions.
   - Identical tag or field names may be reused across distinct union or record types without symbol conflicts.
