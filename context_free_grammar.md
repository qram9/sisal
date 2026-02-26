AI GENERATED
The following Context-Free Grammar (CFG) is extracted from the parse.mly file,
representing the language's syntax structure from top-level fragments down
to basic expressions and types.
Semantic actions and precedence declarations have been omitted for clarity.
1. Terminals (Tokens)

The grammar utilizes a wide range of tokens, including keywords (DEFINE, FUNCTION, IF, FOR), operators (PLUS, PIPE, CATENATE), and literals (INT, FLOAT, STRING, NAME).
2. Non-Terminals and Production Rules
Top-Level Structure

    main ::= compilation_unit

    compilation_unit ::= top_fragment_list EOF

    top_fragment_list ::= top_fragment | top_fragment_list top_fragment

    top_fragment ::= using_stmt | def_func_name_list | type_def_part | global_header_list | function_def_list | SEMICOLON

Imports and Definitions

    using_stmt ::= USING using_decl_list SEMICOLON

    using_decl_list ::= using_item | using_decl_list COMMA using_item

    using_item ::= STRING | STRING AS NAME

    def_func_name_list ::= DEFINE function_name_list

    global_header_list ::= GLOBAL function_header | global_header_list GLOBAL function_header

Functions

    function_def_list ::= function_def | function_def_list function_def

    function_def ::= FORWARD FUNCTION function_header | function_nest

    function_nest ::=

        FUNCTION function_header function_nest expression END FUNCTION

        FUNCTION function_header type_def_part opt_semicolon function_nest expression END FUNCTION

        FUNCTION function_header expression END FUNCTION

        FUNCTION function_header type_def_part opt_semicolon expression END FUNCTION

    function_header ::=

        function_name LPAREN RETURNS type_list RPAREN

        function_name LPAREN declids_spec_list RETURNS type_list RPAREN

Expressions

    expression ::= exp_list

    exp_list ::= simple_expression | exp_list COMMA simple_expression

    simple_expression ::=

        primary_part2

        simple_expression ( GT | GE | LT | LE | EQ | NE | PLUS | MINUS | OR | STAR | DIVIDE | AND | PIPE ) simple_expression

        PLUS simple_expression | MINUS simple_expression | NOT simple_expression

    primary_part2 ::= primary | array_ref | vec_type LPAREN expression RPAREN | mat_type LPAREN expression RPAREN | array_generator | stream_generator | record_ref | record_generator | union_test | union_generator | error_test | prefix_operation | conditional_exp | let_in_exp | tagcase_exp | iteration_exp

    primary ::= constant | OLD value_name | value_name | LPAREN expression RPAREN | invocation

Control Structures

    conditional_exp ::=

        conditional_ifexp conditional_else END IF

        conditional_ifexp conditional_elseif conditional_else END IF

    let_in_exp ::=

        LET decldef_part IN expression END LET

        LET REC decldef_part IN expression END LET

    tagcase_exp ::=

        TAGCASE simple_expression tag_list_colon_expression_list END TAGCASE

        TAGCASE simple_expression tag_list_colon_expression_list OTHERWISE COLON expression END TAGCASE

        TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list END TAGCASE

        TAGCASE value_name ASSIGN simple_expression tag_list_colon_expression_list OTHERWISE COLON expression END TAGCASE

Iterations and Loops

    iteration_exp ::=

        FOR INITIAL decldef_part iterator_terminator RETURNS return_exp_list END FOR

        FOR in_exp_list [decldef_part] RETURNS return_exp_list END FOR

    return_exp ::= VALUE OF [direction] [reduction_op] simple_expression | ARRAY OF simple_expression | STREAM OF simple_expression

Types and Definitions

    type_def_part ::= type_def | type_def_part SEMICOLON type_def

    type_def ::= TYPE type_name EQ type_spec opt_semicolon

    type_spec ::= basic_type_spec | compound_type_spec | type_name | vec_type | mat_type

    basic_type_spec ::= BOOLEAN | CHARACTER | DOUBLE_REAL | INTEGER | NULL | REAL | BYTE_TY | HALF_TY | UINT_TY | SHORT_TY | USHORT_TY | UBYTE_TY | LONG_TY | ULONG_TY | DOUBLE | UCHAR_TY

    compound_type_spec ::=

        ARRAY LBRACK type_spec RBRACK

        STREAM LBRACK type_spec RBRACK

        RECORD LBRACK tag_spec_list RBRACK

        UNION LBRACK tag_spec_list RBRACK | UNION LBRACK names RBRACK
