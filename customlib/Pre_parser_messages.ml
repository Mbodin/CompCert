
(* This file was auto-generated based on "handcrafted.messages". *)

(* Please note that the function [message] can raise [Not_found]. *)

let message =
  fun s ->
    match s with
    | 29 | 147 | 40 | 433 | 105 | 93 ->
        "Internal error when printing a syntax error message. Please report.\n"
    | 329 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n"
    | 320 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n"
    | 319 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a member-designator is expected.\n"
    | 318 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a colon ',' is expected\n"
    | 53 ->
        "Ill-formed __builtin_offsetof.\nAt this point, a struct or union name is expected.\n"
    | 52 ->
        "Ill-formed __builtin_offsetof.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 596 ->
        "Ill-formed K&R function definition.\nAt this point, one of the following is expected:\n  a declaration; or\n  an opening brace '{' (for the function body).\n"
    | 16 ->
        "Ill-formed declaration.\nThe following identifier is used as a type, but has not been defined as such:\n  $0\n"
    | 140 ->
        "Up to this point, a list of parameter declarations has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 141 ->
        "At this point, one of the following is expected:\n  a parameter declaration; or\n  an ellipsis '...'.\n"
    | 600 ->
        "Ill-formed declaration or function definition.\nUp to this point, a list of attribute specifiers has been recognized.\nIf this is a declaration,\n  then at this point, a semicolon ';' is expected.\nIf this is a function definition,\n  then at this point, an opening brace '{' is expected (for the function body).\nIf this is the parameter declaration of a K&R function definition,\n  then at this point, one of the following is expected:\n    a storage class specifier; or\n    a type qualifier; or\n    a type specifier.\n"
    | 587 ->
        "Ill-formed K&R parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 586 | 591 | 584 | 589 ->
        "Ill-formed K&R parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a list of declarators.\n"
    | 283 ->
        "Ill-formed K&R function definition.\nThe following type name is used as a K&R parameter name:\n  $0\n"
    | 282 ->
        "Ill-formed K&R function definition.\nAt this point, an identifier is expected.\n"
    | 243 ->
        "Up to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 551 ->
        "Ill-formed init declarator.\nAt this point, an initializer is expected.\n"
    | 367 ->
        "Ill-formed initializer.\nAt this point, an optional designation,\nfollowed with an initializer, is expected.\n"
    | 368 ->
        "Ill-formed initializer.\nUp to this point, a list of initializers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 369 ->
        "Ill-formed initializer list.\nAt this point, one of the following is expected:\n  an optional designation, followed with an initializer; or\n  a closing brace '}'.\n"
    | 323 ->
        "Ill-formed designator.\nAt this point, a constant expression is expected.\n"
    | 324 ->
        "Ill-formed designator.\nUp to this point, an opening bracket and an expression have been recognized:\n  $1 $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 326 ->
        "Ill-formed designator.\nAt this point, the name of a struct or union member is expected.\n"
    | 373 ->
        "Ill-formed designation.\nUp to this point, a list of designators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, an equals sign '=' is expected.\n"
    | 366 | 370 ->
        "Ill-formed initializer list.\nAt this point, an initializer is expected.\n"
    | 546 ->
        "Ill-formed declaration.\nAt this point, an init declarator is expected.\n"
    | 545 ->
        "Up to this point, a list of declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 219 ->
        "Ill-formed use of the sequencing operator ','.\nAt this point, an expression is expected.\n"
    | 568 ->
        "A type identifier has been recognized.\nAssuming this is the beginning of a declaration,\nat this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator, followed with a semicolon ';'.\n"
    | 431 ->
        "Up to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 428 ->
        "Ill-formed 'return' statement.\nAt this point, one of the following is expected:\n  an expression; or\n  a semicolon ';'.\n"
    | 427 ->
        "At this point, one of the following is expected:\n  a declaration; or\n  a statement; or\n  a pragma; or\n  a closing brace '}'.\n"
    | 483 ->
        "Ill-formed 'while' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 484 ->
        "Ill-formed 'while' statement.\nAt this point, an expression is expected.\n"
    | 485 ->
        "Ill-formed 'while' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 486 ->
        "Ill-formed 'while' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 499 ->
        "Ill-formed 'switch' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 500 ->
        "Ill-formed 'switch' statement.\nAt this point, an expression is expected.\n"
    | 501 ->
        "Ill-formed 'switch' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 502 ->
        "Ill-formed 'switch' statement.\nAt this point, a statement is expected.\nIt usually takes the form of a series of labeled statements,\nenclosed within braces '{' and '}'.\n"
    | 504 ->
        "Ill-formed 'if' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 505 ->
        "Ill-formed 'if' statement.\nAt this point, an expression is expected.\n"
    | 506 ->
        "Ill-formed 'if' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 508 ->
        "Ill-formed 'if' statement.\nAt this point, a statement is expected.\n"
    | 559 ->
        "Ill-formed 'if' ... 'else' statement.\nAt this point, a statement is expected.\n"
    | 436 ->
        "Ill-formed 'goto' statement.\nAt this point, an identifier (a 'goto' label) is expected.\n"
    | 511 ->
        "Ill-formed 'for' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 512 ->
        "Ill-formed 'for' statement.\nAt this point, one of the following is expected:\n  an optional expression\n    (evaluated once at the beginning),\n  followed with a semicolon ';'; or\n  a declaration.\n"
    | 531 ->
        "Ill-formed 'for' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 524 ->
        "Ill-formed 'for' statement.\nAt this point, an optional expression\n  (evaluated before each execution of the loop body),\nfollowed with a semicolon ';', is expected.\n"
    | 525 ->
        "Ill-formed 'for' statement.\nAt this point, an optional expression\n  (evaluated after each execution of the loop body),\nfollowed with a closing parenthesis ')', is expected.\n"
    | 529 ->
        "Ill-formed 'for' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 527 ->
        "Ill-formed 'for' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 557 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, a statement (the loop body) is expected.\n"
    | 561 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, a 'while' keyword is expected.\n"
    | 562 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 563 ->
        "Ill-formed 'do' ... 'while' statement.\nAt this point, an expression is expected.\n"
    | 564 ->
        "Ill-formed 'do' ... 'while' statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' and a semicolon ';' are expected.\n"
    | 439 | 493 ->
        "Ill-formed labeled statement.\nAt this point, a colon ':' is expected.\n"
    | 443 ->
        "Ill-formed labeled statement.\nAt this point, a constant expression is expected.\n"
    | 444 ->
        "Ill-formed labeled statement.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a colon ':' is expected.\n"
    | 445 | 440 | 494 ->
        "Ill-formed labeled statement.\nAt this point, a statement is expected.\n"
    | 446 | 441 | 565 | 437 | 478 ->
        "Ill-formed statement.\nAt this point, a semicolon ';' is expected.\n"
    | 454 ->
        "Ill-formed assembly statement.\nAt this point, a string literal, representing an instruction, is expected.\n"
    | 455 ->
        "Ill-formed assembly statement.\nAt this point, one of the following is expected:\n  a string literal, representing one more instruction; or\n  a colon ':', followed with a list of outputs; or\n  a closing parenthesis ')'.\n"
    | 464 ->
        "Ill-formed assembly operand.\nAt this point, an opening parenthesis '(',\nfollowed with an expression and a closing parenthesis ')', is expected.\n"
    | 465 ->
        "Ill-formed assembly operand.\nAt this point, an expression is expected.\n"
    | 466 ->
        "Ill-formed assembly operand.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 461 ->
        "Ill-formed assembly statement.\nAt this point, an assembly operand is expected.\n"
    | 457 ->
        "Ill-formed assembly operand.\nAt this point, an identifier is expected.\n"
    | 458 ->
        "Ill-formed assembly operand.\nAt this point, a closing bracket ']' is expected.\n"
    | 463 ->
        "Ill-formed assembly operand.\nAt this point, a string literal, representing a constraint, is expected.\n"
    | 470 ->
        "Ill-formed assembly statement.\nUp to this point, a list of outputs and a list of inputs have been recognized:\n  $2\n  $0\nIf the latter list is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a list of clobbered resources; or\n  a closing parenthesis ')'.\n"
    | 468 ->
        "Ill-formed assembly statement.\nUp to this point, a list of outputs has been recognized:\n  $0\nIf this list is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a list of inputs; or\n  a closing parenthesis ')'.\n"
    | 473 ->
        "Ill-formed assembly statement.\nUp to this point, a list of clobbered resources has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 474 | 471 ->
        "Ill-formed assembly statement.\nAt this point, a clobbered resource is expected.\nExamples of clobbered resources:\n  \"memory\"\n  \"eax\"\n"
    | 450 | 449 | 448 ->
        "Ill-formed assembly statement.\nAt this point, one of the following is expected:\n  an assembly attribute, such as 'volatile'; or\n  an opening parenthesis '('.\n"
    | 249 ->
        "At this point, a list of parameter declarations,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 535 ->
        "At this point, a declarator is expected.\n"
    | 534 ->
        "Up to this point, a list of declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 101 ->
        "Ill-formed declarator.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a star '*', possibly followed with type qualifiers; or\n  a direct declarator.\n"
    | 104 ->
        "Ill-formed function definition.\nAt this point, a list of parameter declarations,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 281 ->
        "Ill-formed K&R function definition.\nUp to this point, a list of identifiers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 98 ->
        "Ill-formed direct declarator.\nAt this point, a declarator is expected.\n"
    | 264 ->
        "Up to this point, a declarator has been recognized:\n  $0\nIf this declarator is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 72 ->
        "Ill-formed struct or union specifier.\nAt this point, one of the following is expected:\n  an attribute specifier; or\n  an identifier; or\n  an opening brace '{', followed with a list of members.\n"
    | 75 ->
        "At this point, one of the following is expected:\n  a struct declaration; or\n  a closing brace '}'.\n"
    | 86 ->
        "Ill-formed struct declaration.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a type specifier.\n"
    | 293 ->
        "Ill-formed struct declaration.\nUp to this point, a declarator has been recognized:\n  $0\nIf this declarator is complete,\nthen at this point, one of the following is expected:\n  a colon ':', followed with a constant expression; or\n  a comma ',', followed with a struct declarator; or\n  a semicolon ';'.\n"
    | 288 ->
        "Ill-formed struct declaration.\nAt this point, a struct declarator is expected.\n"
    | 291 ->
        "Ill-formed struct declarator.\nAt this point, a constant expression is expected.\n"
    | 287 ->
        "Ill-formed struct declaration.\nUp to this point, a list of struct declarators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a semicolon ';' is expected.\n"
    | 92 ->
        "Ill-formed struct declaration.\nUp to this point,\na list of type qualifiers and type specifiers has been recognized:\n  $0\nIf this list is complete, then \nat this point, one of the following is expected:\n  a struct declarator; or\n  a semicolon ';'.\n"
    | 515 | 520 | 517 | 522 ->
        "Ill-formed declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator.\n"
    | 518 ->
        "Ill-formed declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 409 ->
        "Ill-formed declaration or function definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 112 | 135 | 118 | 137 ->
        "Ill-formed parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a declarator; or\n  an abstract declarator; or\n  a comma ',', followed with a parameter declaration; or\n  a closing parenthesis ')'.\n"
    | 401 | 417 | 405 | 421 ->
        "Ill-formed declaration or function definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  an init declarator,\n    if this is a declaration; or\n  a declarator,\n    followed with a function body,\n    if this is a function definition.\n"
    | 133 ->
        "Ill-formed parameter declaration.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 9 | 411 ->
        "Ill-formed type definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a type specifier.\n"
    | 394 | 403 | 413 | 419 | 396 | 407 | 415 | 423 ->
        "Ill-formed type definition.\nAt this point, one of the following is expected:\n  a storage class specifier; or\n  a type qualifier; or\n  a list of declarators, followed with a semicolon ';'.\n"
    | 2 ->
        "At this point, one of the following is expected:\n  a function definition; or\n  a declaration; or\n  a pragma; or\n  the end of the file.\n"
    | 18 ->
        "Ill-formed $0 attribute.\nAt this point, an opening parenthesis '(',\nfollowed with a possibly empty list of expressions,\nis expected.\n"
    | 24 ->
        "Ill-formed expression.\nThe following identifier is used as a variable, but has been defined as a type:\n  $0\n"
    | 19 ->
        "Ill-formed $1 attribute.\nAt this point, a list of expressions is expected.\n"
    | 391 ->
        "Ill-formed $2 attribute.\nUp to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 218 ->
        "Ill-formed conditional expression.\nUp to this point, an expression, '?', and an expression have been recognized:\n  $2\n  $1\n  $0\nIf the last expression is complete,\nthen at this point, a colon ':' is expected.\n"
    | 222 | 200 ->
        "Ill-formed conditional expression.\nAt this point, an expression is expected.\n"
    | 161 ->
        "Ill-formed expression.\nAt this point, a list of expressions,\nfollowed with a closing parenthesis ')', is expected.\n"
    | 231 ->
        "Up to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 234 ->
        "Ill-formed expression.\nAt this point, an expression is expected.\n"
    | 235 ->
        "Ill-formed expression.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing bracket ']' is expected.\n"
    | 238 | 159 ->
        "Ill-formed use of the dereferencing operator $0.\nAt this point, the name of a struct or union member is expected.\n"
    | 232 ->
        "Ill-formed list of expressions.\nAt this point, an expression is expected.\n"
    | 174 ->
        "Ill-formed use of the assignment operator $0.\nAt this point, an expression is expected.\n"
    | 213 | 202 | 204 | 225 | 206 | 196 | 210 | 189 | 178 | 183 ->
        "Ill-formed use of the binary operator $0.\nAt this point, an expression is expected.\n"
    | 153 ->
        "Ill-formed use of the unary operator $0.\nAt this point, an expression is expected.\n"
    | 30 ->
        "Ill-formed expression.\nAn opening parenthesis '(' has just been recognized.\nAt this point, one of the following is expected:\n  a type name,   if this is a type cast or a compound literal; or\n  an expression, if this is a parenthesized expression.\n"
    | 386 ->
        "Ill-formed expression.\nUp to this point, a type name in parentheses has been recognized:\n  $2 $1 $0\nAt this point, one of the following is expected:\n  an expression,        if this is a type cast; or\n  an opening brace '{', if this is a compound literal.\n"
    | 365 ->
        "Ill-formed compound literal.\nAt this point, an initializer is expected.\n"
    | 379 ->
        "Ill-formed compound literal.\nUp to this point, a list of initializers has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 382 ->
        "Ill-formed expression.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 34 ->
        "Ill-formed expression.\nAt this point, one of the following is expected:\n  a type name (if this is the beginning of a compound literal); or\n  an expression.\n"
    | 364 ->
        "Ill-formed expression.\nUp to this point, a type name in parentheses has been recognized:\n  $2 $1 $0\nIf this is the beginning of a compound literal,\n  then at this point, an opening brace '{' is expected.\nIf this is intended to be the beginning of a cast expression,\n  then perhaps an opening parenthesis '(' was forgotten earlier.\n"
    | 48 | 33 ->
        "Ill-formed expression.\nAt this point, an expression is expected.\n"
    | 50 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 51 ->
        "Ill-formed use of $1.\nAt this point, an expression is expected.\n"
    | 332 ->
        "Ill-formed use of $3.\nAt this point, a type name is expected.\n"
    | 331 ->
        "Ill-formed use of $2.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a comma ',' is expected.\n"
    | 23 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected,\nfollowed with an expression or a type name.\n"
    | 64 ->
        "Ill-formed use of $0.\nAt this point, an opening parenthesis '(' is expected,\nfollowed with a type name.\n"
    | 65 | 28 ->
        "Ill-formed use of $1.\nAt this point, an expression is expected.\n"
    | 348 ->
        "Ill-formed enumeration specifier.\nAt this point, one of the following is expected:\n  an attribute specifier; or\n  an identifier; or\n  an opening brace '{'.\n"
    | 350 ->
        "Ill-formed enumeration specifier.\nAt this point, an enumerator is expected.\n"
    | 355 ->
        "Ill-formed enumeration specifier.\nAt this point, one of the following is expected:\n  an equals sign '=', followed with a constant expression; or\n  a comma ',', followed with an enumerator; or\n  a closing brace '}'.\n"
    | 356 ->
        "Ill-formed enumeration specifier.\nAt this point, a constant expression is expected.\n"
    | 352 ->
        "Ill-formed enumeration specifier.\nUp to this point, a list of enumerators has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing brace '}' is expected.\n"
    | 353 ->
        "Ill-formed enumeration specifier.\nAt this point, an enumerator is expected.\n"
    | 37 ->
        "Ill-formed gcc attribute specifier.\nAt this point, two opening parentheses '((' are expected.\n"
    | 38 ->
        "Ill-formed gcc attribute specifier.\nAt this point, a second opening parenthesis '(' is expected.\n"
    | 39 ->
        "Ill-formed gcc attribute specifier.\nAt this point, a gcc attribute is expected.\n"
    | 46 ->
        "Ill-formed gcc attribute specifier.\nUp to this point, an attribute has been recognized:\n  $0\nAt this point, one of the following is expected:\n  an opening parenthesis '(',\n    followed with a list of parameters for this attribute; or\n  a comma ',',\n    followed with another attribute; or\n  a closing parenthesis ')'.\n"
    | 47 ->
        "Ill-formed gcc attribute.\nAt this point, a list of expressions is expected.\n"
    | 336 ->
        "Ill-formed gcc attribute.\nAt this point, a comma ',' is expected.\n"
    | 337 ->
        "Ill-formed gcc attribute.\nAt this point, an expression is expected.\n"
    | 338 ->
        "Ill-formed gcc attribute.\nUp to this point, a list of expressions has been recognized:\n  $0\nIf this list is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 342 ->
        "Ill-formed attribute specifier.\nAt this point, one of the following is expected:\n  a comma ',', followed with a gcc attribute; or\n  two closing parentheses '))'.\n"
    | 343 ->
        "Ill-formed attribute specifier.\nAt this point, a second closing parenthesis ')' is expected.\n"
    | 345 ->
        "Ill-formed attribute specifier.\nAt this point, a gcc attribute is expected.\n"
    | 60 ->
        "Ill-formed _Alignas qualifier.\nAt this point, an opening parenthesis '(' is expected.\n"
    | 61 ->
        "Ill-formed _Alignas qualifier.\nAt this point, one of the following is expected:\n  an expression; or\n  a type name.\n"
    | 299 ->
        "Ill-formed type name.\nAt this point, one of the following is expected:\n  a type qualifier; or\n  a type specifier.\n"
    | 145 ->
        "An opening parenthesis '(' has been recognized.\nAt this point, one of the following is expected:\n  an abstract declarator or a declarator,\n    if this parenthesis is a delimiter; or\n  a list of parameter declarations,\n    if this parenthesis is the beginning of a function declarator.\n"
    | 307 ->
        "An opening parenthesis '(' has been recognized.\nAt this point, one of the following is expected:\n  an abstract declarator,\n    if this parenthesis is a delimiter; or\n  a list of parameter declarations,\n    if this parenthesis is the beginning of a function declarator.\n"
    | 266 ->
        "Up to this point, an abstract declarator has been recognized:\n  $0\nAt this point, a closing parenthesis ')' is expected.\n"
    | 268 | 251 | 285 ->
        "At this point, a closing parenthesis ')' is expected.\n"
    | 151 | 257 ->
        "Ill-formed array declarator.\nAt this point, one of the following is expected:\n  an expression, followed with a closing bracket ']'; or\n  a closing bracket ']'.\n"
    | 316 ->
        "Ill-formed _Alignas qualifier.\nUp to this point, an expression has been recognized:\n  $0\nIf this expression is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 385 ->
        "Up to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 363 ->
        "Ill-formed compound literal.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 333 ->
        "Ill-formed use of __builtin_va_arg.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 304 | 388 ->
        "Ill-formed use of $2.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | 314 ->
        "Ill-formed _Alignas qualifier.\nUp to this point, a type name has been recognized:\n  $0\nIf this type name is complete,\nthen at this point, a closing parenthesis ')' is expected.\n"
    | _ ->
        raise Not_found
