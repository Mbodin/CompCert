open Alphabet
open BinNums
open Cabs
open Datatypes
open Grammar
open Int0
open List0
open Main
open Nat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Coq__1 = struct
 type token =
 | XOR_ASSIGN of loc
 | WHILE of loc
 | VOLATILE of loc
 | VOID of loc
 | VAR_NAME of (String.t * loc)
 | UNSIGNED of loc
 | UNION of loc
 | UNDERSCORE_BOOL of loc
 | TYPEDEF_NAME of (String.t * loc)
 | TYPEDEF of loc
 | TILDE of loc
 | SWITCH of loc
 | SUB_ASSIGN of loc
 | STRUCT of loc
 | STRING_LITERAL of ((bool * char_code list) * loc)
 | STATIC of loc
 | STAR of loc
 | SLASH of loc
 | SIZEOF of loc
 | SIGNED of loc
 | SHORT of loc
 | SEMICOLON of loc
 | RPAREN of loc
 | RIGHT_ASSIGN of loc
 | RIGHT of loc
 | RETURN of loc
 | RESTRICT of loc
 | REGISTER of loc
 | RBRACK of loc
 | RBRACE of loc
 | QUESTION of loc
 | PTR of loc
 | PRAGMA of (String.t * loc)
 | PLUS of loc
 | PERCENT of loc
 | PACKED of loc
 | OTHER_NAME of (String.t * loc)
 | OR_ASSIGN of loc
 | NORETURN of loc
 | NEQ of loc
 | MUL_ASSIGN of loc
 | MOD_ASSIGN of loc
 | MINUS of loc
 | LT of loc
 | LPAREN of loc
 | LONG of loc
 | LEQ of loc
 | LEFT_ASSIGN of loc
 | LEFT of loc
 | LBRACK of loc
 | LBRACE of loc
 | INT of loc
 | INLINE of loc
 | INC of loc
 | IF_ of loc
 | HAT of loc
 | GT of loc
 | GOTO of loc
 | GEQ of loc
 | FOR of loc
 | FLOAT of loc
 | EXTERN of loc
 | EQEQ of loc
 | EQ of loc
 | EOF of unit
 | ENUM of loc
 | ELSE of loc
 | ELLIPSIS of loc
 | DOUBLE of loc
 | DOT of loc
 | DO of loc
 | DIV_ASSIGN of loc
 | DEFAULT of loc
 | DEC of loc
 | CONTINUE of loc
 | CONSTANT of (constant * loc)
 | CONST of loc
 | COMMA of loc
 | COLON of loc
 | CHAR of loc
 | CASE of loc
 | BUILTIN_VA_ARG of loc
 | BUILTIN_OFFSETOF of loc
 | BREAK of loc
 | BARBAR of loc
 | BAR of loc
 | BANG of loc
 | AUTO of loc
 | ATTRIBUTE of loc
 | ASM of loc
 | AND_ASSIGN of loc
 | ANDAND of loc
 | AND of loc
 | ALIGNOF of loc
 | ALIGNAS of loc
 | ADD_ASSIGN of loc
end
include Coq__1

module Gram =
 struct
  type terminal' =
  | ADD_ASSIGN't
  | ALIGNAS't
  | ALIGNOF't
  | AND't
  | ANDAND't
  | AND_ASSIGN't
  | ASM't
  | ATTRIBUTE't
  | AUTO't
  | BANG't
  | BAR't
  | BARBAR't
  | BREAK't
  | BUILTIN_OFFSETOF't
  | BUILTIN_VA_ARG't
  | CASE't
  | CHAR't
  | COLON't
  | COMMA't
  | CONST't
  | CONSTANT't
  | CONTINUE't
  | DEC't
  | DEFAULT't
  | DIV_ASSIGN't
  | DO't
  | DOT't
  | DOUBLE't
  | ELLIPSIS't
  | ELSE't
  | ENUM't
  | EOF't
  | EQ't
  | EQEQ't
  | EXTERN't
  | FLOAT't
  | FOR't
  | GEQ't
  | GOTO't
  | GT't
  | HAT't
  | IF_'t
  | INC't
  | INLINE't
  | INT't
  | LBRACE't
  | LBRACK't
  | LEFT't
  | LEFT_ASSIGN't
  | LEQ't
  | LONG't
  | LPAREN't
  | LT't
  | MINUS't
  | MOD_ASSIGN't
  | MUL_ASSIGN't
  | NEQ't
  | NORETURN't
  | OR_ASSIGN't
  | OTHER_NAME't
  | PACKED't
  | PERCENT't
  | PLUS't
  | PRAGMA't
  | PTR't
  | QUESTION't
  | RBRACE't
  | RBRACK't
  | REGISTER't
  | RESTRICT't
  | RETURN't
  | RIGHT't
  | RIGHT_ASSIGN't
  | RPAREN't
  | SEMICOLON't
  | SHORT't
  | SIGNED't
  | SIZEOF't
  | SLASH't
  | STAR't
  | STATIC't
  | STRING_LITERAL't
  | STRUCT't
  | SUB_ASSIGN't
  | SWITCH't
  | TILDE't
  | TYPEDEF't
  | TYPEDEF_NAME't
  | UNDERSCORE_BOOL't
  | UNION't
  | UNSIGNED't
  | VAR_NAME't
  | VOID't
  | VOLATILE't
  | WHILE't
  | XOR_ASSIGN't

  type terminal = terminal'

  (** val terminalNum : terminal coq_Numbered **)

  let terminalNum =
    { inj = (fun x ->
      match x with
      | ADD_ASSIGN't -> Coq_xH
      | ALIGNAS't -> Coq_xO Coq_xH
      | ALIGNOF't -> Coq_xI Coq_xH
      | AND't -> Coq_xO (Coq_xO Coq_xH)
      | ANDAND't -> Coq_xI (Coq_xO Coq_xH)
      | AND_ASSIGN't -> Coq_xO (Coq_xI Coq_xH)
      | ASM't -> Coq_xI (Coq_xI Coq_xH)
      | ATTRIBUTE't -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
      | AUTO't -> Coq_xI (Coq_xO (Coq_xO Coq_xH))
      | BANG't -> Coq_xO (Coq_xI (Coq_xO Coq_xH))
      | BAR't -> Coq_xI (Coq_xI (Coq_xO Coq_xH))
      | BARBAR't -> Coq_xO (Coq_xO (Coq_xI Coq_xH))
      | BREAK't -> Coq_xI (Coq_xO (Coq_xI Coq_xH))
      | BUILTIN_OFFSETOF't -> Coq_xO (Coq_xI (Coq_xI Coq_xH))
      | BUILTIN_VA_ARG't -> Coq_xI (Coq_xI (Coq_xI Coq_xH))
      | CASE't -> Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | CHAR't -> Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | COLON't -> Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | COMMA't -> Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | CONST't -> Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | CONSTANT't -> Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | CONTINUE't -> Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | DEC't -> Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | DEFAULT't -> Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | DIV_ASSIGN't -> Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | DO't -> Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | DOT't -> Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | DOUBLE't -> Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | ELLIPSIS't -> Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | ELSE't -> Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | ENUM't -> Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | EOF't -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | EQ't -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | EQEQ't -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | EXTERN't -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | FLOAT't -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | FOR't -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | GEQ't -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | GOTO't -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | GT't -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | HAT't -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | IF_'t -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | INC't -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | INLINE't -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | INT't -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | LBRACE't -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | LBRACK't -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | LEFT't -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | LEFT_ASSIGN't -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | LEQ't -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | LONG't -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | LPAREN't -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | LT't -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | MINUS't -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | MOD_ASSIGN't -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | MUL_ASSIGN't -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | NEQ't -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | NORETURN't -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | OR_ASSIGN't -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | OTHER_NAME't -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | PACKED't -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | PERCENT't -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | PLUS't -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | PRAGMA't -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | PTR't -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | QUESTION't ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | RBRACE't -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | RBRACK't -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | REGISTER't ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | RESTRICT't ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | RETURN't -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | RIGHT't -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | RIGHT_ASSIGN't ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | RPAREN't -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | SEMICOLON't ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | SHORT't -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | SIGNED't -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | SIZEOF't -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | SLASH't -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | STAR't -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | STATIC't -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | STRING_LITERAL't ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | STRUCT't -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | SUB_ASSIGN't ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | SWITCH't -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | TILDE't -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | TYPEDEF't ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | TYPEDEF_NAME't ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | UNDERSCORE_BOOL't ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | UNION't -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | UNSIGNED't ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | VAR_NAME't ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | VOID't -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | VOLATILE't ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | WHILE't -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | XOR_ASSIGN't ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))); surj =
      (fun n ->
      match n with
      | Coq_xI p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> WHILE't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> PLUS't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SLASH't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LBRACK't)
                  | Coq_xH -> ENUM't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> TYPEDEF't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> MOD_ASSIGN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RETURN't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> GOTO't)
                  | Coq_xH -> DEC't)
               | Coq_xH -> BUILTIN_VA_ARG't)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> UNSIGNED't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> OR_ASSIGN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SEMICOLON't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> INC't)
                  | Coq_xH -> DOT't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> STRUCT't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LONG't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RBRACE't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> EXTERN't)
                  | Coq_xH -> COMMA't)
               | Coq_xH -> BAR't)
            | Coq_xH -> ASM't)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> VOID't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> PACKED't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SIGNED't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> INT't)
                  | Coq_xH -> ELLIPSIS't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SWITCH't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LT't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> REGISTER't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> FOR't)
                  | Coq_xH -> CONSTANT't)
               | Coq_xH -> BREAK't)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> UNDERSCORE_BOOL't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> NEQ't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RIGHT_ASSIGN't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> HAT't)
                  | Coq_xH -> DIV_ASSIGN't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> STATIC't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LEFT_ASSIGN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> PTR't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> EQ't)
                  | Coq_xH -> CHAR't)
               | Coq_xH -> AUTO't)
            | Coq_xH -> ANDAND't)
         | Coq_xH -> ALIGNOF't)
      | Coq_xO p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> VOLATILE't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> PERCENT't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SIZEOF't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LBRACE't)
                  | Coq_xH -> ELSE't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> TILDE't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> MINUS't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RESTRICT't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> GEQ't)
                  | Coq_xH -> CONTINUE't)
               | Coq_xH -> BUILTIN_OFFSETOF't)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> UNION't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> NORETURN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RPAREN't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> IF_'t)
                  | Coq_xH -> DO't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> STRING_LITERAL't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LEQ't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> QUESTION't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> EQEQ't)
                  | Coq_xH -> COLON't)
               | Coq_xH -> BANG't)
            | Coq_xH -> AND_ASSIGN't)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> VAR_NAME't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> OTHER_NAME't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SHORT't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> INLINE't)
                  | Coq_xH -> DOUBLE't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> SUB_ASSIGN't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LPAREN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RBRACK't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> FLOAT't)
                  | Coq_xH -> CONST't)
               | Coq_xH -> BARBAR't)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> TYPEDEF_NAME't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> MUL_ASSIGN't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> RIGHT't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> GT't)
                  | Coq_xH -> DEFAULT't)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> ADD_ASSIGN't
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> STAR't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> LEFT't)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> XOR_ASSIGN't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> PRAGMA't
                        | _ -> ADD_ASSIGN't)
                     | Coq_xH -> EOF't)
                  | Coq_xH -> CASE't)
               | Coq_xH -> ATTRIBUTE't)
            | Coq_xH -> AND't)
         | Coq_xH -> ALIGNAS't)
      | Coq_xH -> ADD_ASSIGN't); inj_bound = (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xI Coq_xH)))))) }

  (** val coq_TerminalAlph : terminal coq_Alphabet **)

  let coq_TerminalAlph =
    coq_NumberedAlphabet terminalNum

  type nonterminal' =
  | AND_expression'nt
  | Coq_abstract_declarator'nt
  | Coq_additive_expression'nt
  | Coq_argument_expression_list'nt
  | Coq_asm_arguments'nt
  | Coq_asm_attributes'nt
  | Coq_asm_flags'nt
  | Coq_asm_op_name'nt
  | Coq_asm_operand'nt
  | Coq_asm_operands'nt
  | Coq_asm_operands_ne'nt
  | Coq_asm_statement'nt
  | Coq_assignment_expression'nt
  | Coq_assignment_operator'nt
  | Coq_attribute_specifier'nt
  | Coq_attribute_specifier_list'nt
  | Coq_block_item'nt
  | Coq_block_item_list'nt
  | Coq_c_initializer'nt
  | Coq_cast_expression'nt
  | Coq_compound_statement'nt
  | Coq_conditional_expression'nt
  | Coq_constant_expression'nt
  | Coq_declaration'nt
  | Coq_declaration_list'nt
  | Coq_declaration_specifiers'nt
  | Coq_declaration_specifiers_typespec_opt'nt
  | Coq_declarator'nt
  | Coq_declarator_noattrend'nt
  | Coq_designation'nt
  | Coq_designator'nt
  | Coq_designator_list'nt
  | Coq_direct_abstract_declarator'nt
  | Coq_direct_declarator'nt
  | Coq_enum_specifier'nt
  | Coq_enumeration_constant'nt
  | Coq_enumerator'nt
  | Coq_enumerator_list'nt
  | Coq_equality_expression'nt
  | Coq_exclusive_OR_expression'nt
  | Coq_expression'nt
  | Coq_expression_statement'nt
  | Coq_external_declaration'nt
  | Coq_function_definition'nt
  | Coq_function_specifier'nt
  | Coq_gcc_attribute'nt
  | Coq_gcc_attribute_list'nt
  | Coq_gcc_attribute_word'nt
  | Coq_identifier_list'nt
  | Coq_inclusive_OR_expression'nt
  | Coq_init_declarator'nt
  | Coq_init_declarator_list'nt
  | Coq_initializer_list'nt
  | Coq_iteration_statement_statement_dangerous_'nt
  | Coq_iteration_statement_statement_safe_'nt
  | Coq_jump_statement'nt
  | Coq_labeled_statement_statement_dangerous_'nt
  | Coq_labeled_statement_statement_safe_'nt
  | Coq_logical_AND_expression'nt
  | Coq_logical_OR_expression'nt
  | Coq_multiplicative_expression'nt
  | Coq_parameter_declaration'nt
  | Coq_parameter_list'nt
  | Coq_parameter_type_list'nt
  | Coq_pointer'nt
  | Coq_postfix_expression'nt
  | Coq_primary_expression'nt
  | Coq_relational_expression'nt
  | Coq_selection_statement_dangerous'nt
  | Coq_selection_statement_safe'nt
  | Coq_shift_expression'nt
  | Coq_specifier_qualifier_list'nt
  | Coq_statement_dangerous'nt
  | Coq_statement_safe'nt
  | Coq_storage_class_specifier'nt
  | Coq_struct_declaration'nt
  | Coq_struct_declaration_list'nt
  | Coq_struct_declarator'nt
  | Coq_struct_declarator_list'nt
  | Coq_struct_or_union'nt
  | Coq_struct_or_union_specifier'nt
  | Coq_translation_unit'nt
  | Coq_translation_unit_file'nt
  | Coq_type_name'nt
  | Coq_type_qualifier'nt
  | Coq_type_qualifier_list'nt
  | Coq_type_qualifier_noattr'nt
  | Coq_type_specifier'nt
  | Coq_unary_expression'nt
  | Coq_unary_operator'nt

  type nonterminal = nonterminal'

  (** val nonterminalNum : nonterminal coq_Numbered **)

  let nonterminalNum =
    { inj = (fun x ->
      match x with
      | AND_expression'nt -> Coq_xH
      | Coq_abstract_declarator'nt -> Coq_xO Coq_xH
      | Coq_additive_expression'nt -> Coq_xI Coq_xH
      | Coq_argument_expression_list'nt -> Coq_xO (Coq_xO Coq_xH)
      | Coq_asm_arguments'nt -> Coq_xI (Coq_xO Coq_xH)
      | Coq_asm_attributes'nt -> Coq_xO (Coq_xI Coq_xH)
      | Coq_asm_flags'nt -> Coq_xI (Coq_xI Coq_xH)
      | Coq_asm_op_name'nt -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
      | Coq_asm_operand'nt -> Coq_xI (Coq_xO (Coq_xO Coq_xH))
      | Coq_asm_operands'nt -> Coq_xO (Coq_xI (Coq_xO Coq_xH))
      | Coq_asm_operands_ne'nt -> Coq_xI (Coq_xI (Coq_xO Coq_xH))
      | Coq_asm_statement'nt -> Coq_xO (Coq_xO (Coq_xI Coq_xH))
      | Coq_assignment_expression'nt -> Coq_xI (Coq_xO (Coq_xI Coq_xH))
      | Coq_assignment_operator'nt -> Coq_xO (Coq_xI (Coq_xI Coq_xH))
      | Coq_attribute_specifier'nt -> Coq_xI (Coq_xI (Coq_xI Coq_xH))
      | Coq_attribute_specifier_list'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Coq_block_item'nt -> Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Coq_block_item_list'nt -> Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Coq_c_initializer'nt -> Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Coq_cast_expression'nt -> Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Coq_compound_statement'nt -> Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Coq_conditional_expression'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Coq_constant_expression'nt -> Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Coq_declaration'nt -> Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declaration_list'nt -> Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declaration_specifiers'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declaration_specifiers_typespec_opt'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declarator'nt -> Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Coq_declarator_noattrend'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Coq_designation'nt -> Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Coq_designator'nt -> Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Coq_designator_list'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_direct_abstract_declarator'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_direct_declarator'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_enum_specifier'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_enumeration_constant'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_enumerator'nt -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_enumerator_list'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_equality_expression'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_exclusive_OR_expression'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_expression'nt -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_expression_statement'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_external_declaration'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_function_definition'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_function_specifier'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_gcc_attribute'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_gcc_attribute_list'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_gcc_attribute_word'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_identifier_list'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_inclusive_OR_expression'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_init_declarator'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_init_declarator_list'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_initializer_list'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_iteration_statement_statement_dangerous_'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_iteration_statement_statement_safe_'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_jump_statement'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_labeled_statement_statement_dangerous_'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_labeled_statement_statement_safe_'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_logical_AND_expression'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_logical_OR_expression'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_multiplicative_expression'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_parameter_declaration'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_parameter_list'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_parameter_type_list'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_pointer'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_postfix_expression'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_primary_expression'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_relational_expression'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_selection_statement_dangerous'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_selection_statement_safe'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_shift_expression'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_specifier_qualifier_list'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_statement_dangerous'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_statement_safe'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_storage_class_specifier'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_struct_declaration'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_struct_declaration_list'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_struct_declarator'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_struct_declarator_list'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_struct_or_union'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_struct_or_union_specifier'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_translation_unit'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_translation_unit_file'nt ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_type_name'nt ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_type_qualifier'nt ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_type_qualifier_list'nt ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_type_qualifier_noattr'nt ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_type_specifier'nt ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_unary_expression'nt ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_unary_operator'nt ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))); surj =
      (fun n ->
      match n with
      | Coq_xI p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xH -> Coq_parameter_list'nt
                     | _ -> AND_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declarator_list'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_gcc_attribute_list'nt)
                  | Coq_xH -> Coq_designator'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_type_qualifier_noattr'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_iteration_statement_statement_safe_'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_shift_expression'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_equality_expression'nt)
                  | Coq_xH -> Coq_constant_expression'nt)
               | Coq_xH -> Coq_attribute_specifier'nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xH -> Coq_logical_AND_expression'nt
                     | _ -> AND_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_storage_class_specifier'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_external_declaration'nt)
                  | Coq_xH -> Coq_declaration_specifiers_typespec_opt'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_translation_unit_file'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_init_declarator'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_primary_expression'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_enum_specifier'nt)
                  | Coq_xH -> Coq_c_initializer'nt)
               | Coq_xH -> Coq_asm_operands_ne'nt)
            | Coq_xH -> Coq_asm_flags'nt)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xH -> Coq_multiplicative_expression'nt
                     | _ -> AND_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declaration_list'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_function_specifier'nt)
                  | Coq_xH -> Coq_declarator_noattrend'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_type_qualifier'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_initializer_list'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_selection_statement_dangerous'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_enumerator'nt)
                  | Coq_xH -> Coq_compound_statement'nt)
               | Coq_xH -> Coq_assignment_expression'nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_unary_expression'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_labeled_statement_statement_dangerous_'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_statement_dangerous'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_expression'nt)
                  | Coq_xH -> Coq_declaration_list'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_or_union_specifier'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_identifier_list'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_pointer'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_direct_abstract_declarator'nt)
                  | Coq_xH -> Coq_block_item'nt)
               | Coq_xH -> Coq_asm_operand'nt)
            | Coq_xH -> Coq_asm_arguments'nt)
         | Coq_xH -> Coq_additive_expression'nt)
      | Coq_xO p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xH -> Coq_parameter_declaration'nt
                     | _ -> AND_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declarator'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_gcc_attribute'nt)
                  | Coq_xH -> Coq_designation'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_type_qualifier_list'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH ->
                       Coq_iteration_statement_statement_dangerous_'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_selection_statement_safe'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_enumerator_list'nt)
                  | Coq_xH -> Coq_conditional_expression'nt)
               | Coq_xH -> Coq_assignment_operator'nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_unary_operator'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_labeled_statement_statement_safe_'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_statement_safe'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_expression_statement'nt)
                  | Coq_xH -> Coq_declaration_specifiers'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_translation_unit'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_inclusive_OR_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_postfix_expression'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_direct_declarator'nt)
                  | Coq_xH -> Coq_block_item_list'nt)
               | Coq_xH -> Coq_asm_operands'nt)
            | Coq_xH -> Coq_asm_attributes'nt)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xH -> Coq_logical_OR_expression'nt
                     | _ -> AND_expression'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declaration'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_function_definition'nt)
                  | Coq_xH -> Coq_declarator'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_type_name'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_init_declarator_list'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_relational_expression'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_enumeration_constant'nt)
                  | Coq_xH -> Coq_cast_expression'nt)
               | Coq_xH -> Coq_asm_statement'nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_type_specifier'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_jump_statement'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_specifier_qualifier_list'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_exclusive_OR_expression'nt)
                  | Coq_xH -> Coq_declaration'nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_or_union'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_gcc_attribute_word'nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI _ -> AND_expression'nt
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_parameter_type_list'nt
                        | _ -> AND_expression'nt)
                     | Coq_xH -> Coq_designator_list'nt)
                  | Coq_xH -> Coq_attribute_specifier_list'nt)
               | Coq_xH -> Coq_asm_op_name'nt)
            | Coq_xH -> Coq_argument_expression_list'nt)
         | Coq_xH -> Coq_abstract_declarator'nt)
      | Coq_xH -> AND_expression'nt); inj_bound = (Coq_xO (Coq_xI (Coq_xO
      (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))) }

  (** val coq_NonTerminalAlph : nonterminal coq_Alphabet **)

  let coq_NonTerminalAlph =
    coq_NumberedAlphabet nonterminalNum

  type symbol =
  | T of terminal
  | NT of nonterminal

  (** val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rect f f0 = function
  | T x -> f x
  | NT x -> f0 x

  (** val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)

  let symbol_rec f f0 = function
  | T x -> f x
  | NT x -> f0 x

  (** val coq_SymbolAlph : symbol coq_Alphabet **)

  let coq_SymbolAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | T x0 ->
        (match y with
         | T y0 -> compare coq_TerminalAlph.coq_AlphabetComparable x0 y0
         | NT _ -> Gt)
      | NT x0 ->
        (match y with
         | T _ -> Lt
         | NT y0 -> compare coq_NonTerminalAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app
        (map (fun x -> T x) (all_list coq_TerminalAlph.coq_AlphabetFinite))
        (map (fun x -> NT x)
          (all_list coq_NonTerminalAlph.coq_AlphabetFinite))) }

  type terminal_semantic_type = __

  type nonterminal_semantic_type = __

  type symbol_semantic_type = __

  type token = Coq__1.token

  (** val token_term : token -> terminal **)

  let token_term = function
  | XOR_ASSIGN _ -> XOR_ASSIGN't
  | WHILE _ -> WHILE't
  | VOLATILE _ -> VOLATILE't
  | VOID _ -> VOID't
  | VAR_NAME _ -> VAR_NAME't
  | UNSIGNED _ -> UNSIGNED't
  | UNION _ -> UNION't
  | UNDERSCORE_BOOL _ -> UNDERSCORE_BOOL't
  | TYPEDEF_NAME _ -> TYPEDEF_NAME't
  | TYPEDEF _ -> TYPEDEF't
  | TILDE _ -> TILDE't
  | SWITCH _ -> SWITCH't
  | SUB_ASSIGN _ -> SUB_ASSIGN't
  | STRUCT _ -> STRUCT't
  | STRING_LITERAL _ -> STRING_LITERAL't
  | STATIC _ -> STATIC't
  | STAR _ -> STAR't
  | SLASH _ -> SLASH't
  | SIZEOF _ -> SIZEOF't
  | SIGNED _ -> SIGNED't
  | SHORT _ -> SHORT't
  | SEMICOLON _ -> SEMICOLON't
  | RPAREN _ -> RPAREN't
  | RIGHT_ASSIGN _ -> RIGHT_ASSIGN't
  | RIGHT _ -> RIGHT't
  | RETURN _ -> RETURN't
  | RESTRICT _ -> RESTRICT't
  | REGISTER _ -> REGISTER't
  | RBRACK _ -> RBRACK't
  | RBRACE _ -> RBRACE't
  | QUESTION _ -> QUESTION't
  | PTR _ -> PTR't
  | PRAGMA _ -> PRAGMA't
  | PLUS _ -> PLUS't
  | PERCENT _ -> PERCENT't
  | PACKED _ -> PACKED't
  | OTHER_NAME _ -> OTHER_NAME't
  | OR_ASSIGN _ -> OR_ASSIGN't
  | NORETURN _ -> NORETURN't
  | NEQ _ -> NEQ't
  | MUL_ASSIGN _ -> MUL_ASSIGN't
  | MOD_ASSIGN _ -> MOD_ASSIGN't
  | MINUS _ -> MINUS't
  | LT _ -> LT't
  | LPAREN _ -> LPAREN't
  | LONG _ -> LONG't
  | LEQ _ -> LEQ't
  | LEFT_ASSIGN _ -> LEFT_ASSIGN't
  | LEFT _ -> LEFT't
  | LBRACK _ -> LBRACK't
  | LBRACE _ -> LBRACE't
  | INT _ -> INT't
  | INLINE _ -> INLINE't
  | INC _ -> INC't
  | IF_ _ -> IF_'t
  | HAT _ -> HAT't
  | GT _ -> GT't
  | GOTO _ -> GOTO't
  | GEQ _ -> GEQ't
  | FOR _ -> FOR't
  | FLOAT _ -> FLOAT't
  | EXTERN _ -> EXTERN't
  | EQEQ _ -> EQEQ't
  | EQ _ -> EQ't
  | EOF _ -> EOF't
  | ENUM _ -> ENUM't
  | ELSE _ -> ELSE't
  | ELLIPSIS _ -> ELLIPSIS't
  | DOUBLE _ -> DOUBLE't
  | DOT _ -> DOT't
  | DO _ -> DO't
  | DIV_ASSIGN _ -> DIV_ASSIGN't
  | DEFAULT _ -> DEFAULT't
  | DEC _ -> DEC't
  | CONTINUE _ -> CONTINUE't
  | CONSTANT _ -> CONSTANT't
  | CONST _ -> CONST't
  | COMMA _ -> COMMA't
  | COLON _ -> COLON't
  | CHAR _ -> CHAR't
  | CASE _ -> CASE't
  | BUILTIN_VA_ARG _ -> BUILTIN_VA_ARG't
  | BUILTIN_OFFSETOF _ -> BUILTIN_OFFSETOF't
  | BREAK _ -> BREAK't
  | BARBAR _ -> BARBAR't
  | BAR _ -> BAR't
  | BANG _ -> BANG't
  | AUTO _ -> AUTO't
  | ATTRIBUTE _ -> ATTRIBUTE't
  | ASM _ -> ASM't
  | AND_ASSIGN _ -> AND_ASSIGN't
  | ANDAND _ -> ANDAND't
  | AND _ -> AND't
  | ALIGNOF _ -> ALIGNOF't
  | ALIGNAS _ -> ALIGNAS't
  | ADD_ASSIGN _ -> ADD_ASSIGN't

  (** val token_sem : token -> symbol_semantic_type **)

  let token_sem = function
  | XOR_ASSIGN x -> Obj.magic x
  | WHILE x -> Obj.magic x
  | VOLATILE x -> Obj.magic x
  | VOID x -> Obj.magic x
  | VAR_NAME x -> Obj.magic x
  | UNSIGNED x -> Obj.magic x
  | UNION x -> Obj.magic x
  | UNDERSCORE_BOOL x -> Obj.magic x
  | TYPEDEF_NAME x -> Obj.magic x
  | TYPEDEF x -> Obj.magic x
  | TILDE x -> Obj.magic x
  | SWITCH x -> Obj.magic x
  | SUB_ASSIGN x -> Obj.magic x
  | STRUCT x -> Obj.magic x
  | STRING_LITERAL x -> Obj.magic x
  | STATIC x -> Obj.magic x
  | STAR x -> Obj.magic x
  | SLASH x -> Obj.magic x
  | SIZEOF x -> Obj.magic x
  | SIGNED x -> Obj.magic x
  | SHORT x -> Obj.magic x
  | SEMICOLON x -> Obj.magic x
  | RPAREN x -> Obj.magic x
  | RIGHT_ASSIGN x -> Obj.magic x
  | RIGHT x -> Obj.magic x
  | RETURN x -> Obj.magic x
  | RESTRICT x -> Obj.magic x
  | REGISTER x -> Obj.magic x
  | RBRACK x -> Obj.magic x
  | RBRACE x -> Obj.magic x
  | QUESTION x -> Obj.magic x
  | PTR x -> Obj.magic x
  | PRAGMA x -> Obj.magic x
  | PLUS x -> Obj.magic x
  | PERCENT x -> Obj.magic x
  | PACKED x -> Obj.magic x
  | OTHER_NAME x -> Obj.magic x
  | OR_ASSIGN x -> Obj.magic x
  | NORETURN x -> Obj.magic x
  | NEQ x -> Obj.magic x
  | MUL_ASSIGN x -> Obj.magic x
  | MOD_ASSIGN x -> Obj.magic x
  | MINUS x -> Obj.magic x
  | LT x -> Obj.magic x
  | LPAREN x -> Obj.magic x
  | LONG x -> Obj.magic x
  | LEQ x -> Obj.magic x
  | LEFT_ASSIGN x -> Obj.magic x
  | LEFT x -> Obj.magic x
  | LBRACK x -> Obj.magic x
  | LBRACE x -> Obj.magic x
  | INT x -> Obj.magic x
  | INLINE x -> Obj.magic x
  | INC x -> Obj.magic x
  | IF_ x -> Obj.magic x
  | HAT x -> Obj.magic x
  | GT x -> Obj.magic x
  | GOTO x -> Obj.magic x
  | GEQ x -> Obj.magic x
  | FOR x -> Obj.magic x
  | FLOAT x -> Obj.magic x
  | EXTERN x -> Obj.magic x
  | EQEQ x -> Obj.magic x
  | EQ x -> Obj.magic x
  | EOF x -> Obj.magic x
  | ENUM x -> Obj.magic x
  | ELSE x -> Obj.magic x
  | ELLIPSIS x -> Obj.magic x
  | DOUBLE x -> Obj.magic x
  | DOT x -> Obj.magic x
  | DO x -> Obj.magic x
  | DIV_ASSIGN x -> Obj.magic x
  | DEFAULT x -> Obj.magic x
  | DEC x -> Obj.magic x
  | CONTINUE x -> Obj.magic x
  | CONSTANT x -> Obj.magic x
  | CONST x -> Obj.magic x
  | COMMA x -> Obj.magic x
  | COLON x -> Obj.magic x
  | CHAR x -> Obj.magic x
  | CASE x -> Obj.magic x
  | BUILTIN_VA_ARG x -> Obj.magic x
  | BUILTIN_OFFSETOF x -> Obj.magic x
  | BREAK x -> Obj.magic x
  | BARBAR x -> Obj.magic x
  | BAR x -> Obj.magic x
  | BANG x -> Obj.magic x
  | AUTO x -> Obj.magic x
  | ATTRIBUTE x -> Obj.magic x
  | ASM x -> Obj.magic x
  | AND_ASSIGN x -> Obj.magic x
  | ANDAND x -> Obj.magic x
  | AND x -> Obj.magic x
  | ALIGNOF x -> Obj.magic x
  | ALIGNAS x -> Obj.magic x
  | ADD_ASSIGN x -> Obj.magic x

  type production' =
  | Prod'unary_operator'5
  | Prod'unary_operator'4
  | Prod'unary_operator'3
  | Prod'unary_operator'2
  | Prod'unary_operator'1
  | Prod'unary_operator'0
  | Prod'unary_expression'6
  | Prod'unary_expression'5
  | Prod'unary_expression'4
  | Prod'unary_expression'3
  | Prod'unary_expression'2
  | Prod'unary_expression'1
  | Prod'unary_expression'0
  | Prod'type_specifier'12
  | Prod'type_specifier'11
  | Prod'type_specifier'10
  | Prod'type_specifier'9
  | Prod'type_specifier'8
  | Prod'type_specifier'7
  | Prod'type_specifier'6
  | Prod'type_specifier'5
  | Prod'type_specifier'4
  | Prod'type_specifier'3
  | Prod'type_specifier'2
  | Prod'type_specifier'1
  | Prod'type_specifier'0
  | Prod'type_qualifier_noattr'2
  | Prod'type_qualifier_noattr'1
  | Prod'type_qualifier_noattr'0
  | Prod'type_qualifier_list'1
  | Prod'type_qualifier_list'0
  | Prod'type_qualifier'1
  | Prod'type_qualifier'0
  | Prod'type_name'1
  | Prod'type_name'0
  | Prod'translation_unit_file'1
  | Prod'translation_unit_file'0
  | Prod'translation_unit'3
  | Prod'translation_unit'2
  | Prod'translation_unit'1
  | Prod'translation_unit'0
  | Prod'struct_or_union_specifier'2
  | Prod'struct_or_union_specifier'1
  | Prod'struct_or_union_specifier'0
  | Prod'struct_or_union'1
  | Prod'struct_or_union'0
  | Prod'struct_declarator_list'1
  | Prod'struct_declarator_list'0
  | Prod'struct_declarator'2
  | Prod'struct_declarator'1
  | Prod'struct_declarator'0
  | Prod'struct_declaration_list'1
  | Prod'struct_declaration_list'0
  | Prod'struct_declaration'1
  | Prod'struct_declaration'0
  | Prod'storage_class_specifier'4
  | Prod'storage_class_specifier'3
  | Prod'storage_class_specifier'2
  | Prod'storage_class_specifier'1
  | Prod'storage_class_specifier'0
  | Prod'statement_safe'6
  | Prod'statement_safe'5
  | Prod'statement_safe'4
  | Prod'statement_safe'3
  | Prod'statement_safe'2
  | Prod'statement_safe'1
  | Prod'statement_safe'0
  | Prod'statement_dangerous'6
  | Prod'statement_dangerous'5
  | Prod'statement_dangerous'4
  | Prod'statement_dangerous'3
  | Prod'statement_dangerous'2
  | Prod'statement_dangerous'1
  | Prod'statement_dangerous'0
  | Prod'specifier_qualifier_list'3
  | Prod'specifier_qualifier_list'2
  | Prod'specifier_qualifier_list'1
  | Prod'specifier_qualifier_list'0
  | Prod'shift_expression'2
  | Prod'shift_expression'1
  | Prod'shift_expression'0
  | Prod'selection_statement_safe'1
  | Prod'selection_statement_safe'0
  | Prod'selection_statement_dangerous'2
  | Prod'selection_statement_dangerous'1
  | Prod'selection_statement_dangerous'0
  | Prod'relational_expression'4
  | Prod'relational_expression'3
  | Prod'relational_expression'2
  | Prod'relational_expression'1
  | Prod'relational_expression'0
  | Prod'primary_expression'3
  | Prod'primary_expression'2
  | Prod'primary_expression'1
  | Prod'primary_expression'0
  | Prod'postfix_expression'12
  | Prod'postfix_expression'11
  | Prod'postfix_expression'10
  | Prod'postfix_expression'9
  | Prod'postfix_expression'8
  | Prod'postfix_expression'7
  | Prod'postfix_expression'6
  | Prod'postfix_expression'5
  | Prod'postfix_expression'4
  | Prod'postfix_expression'3
  | Prod'postfix_expression'2
  | Prod'postfix_expression'1
  | Prod'postfix_expression'0
  | Prod'pointer'3
  | Prod'pointer'2
  | Prod'pointer'1
  | Prod'pointer'0
  | Prod'parameter_type_list'1
  | Prod'parameter_type_list'0
  | Prod'parameter_list'1
  | Prod'parameter_list'0
  | Prod'parameter_declaration'2
  | Prod'parameter_declaration'1
  | Prod'parameter_declaration'0
  | Prod'multiplicative_expression'3
  | Prod'multiplicative_expression'2
  | Prod'multiplicative_expression'1
  | Prod'multiplicative_expression'0
  | Prod'logical_OR_expression'1
  | Prod'logical_OR_expression'0
  | Prod'logical_AND_expression'1
  | Prod'logical_AND_expression'0
  | Prod'labeled_statement_statement_safe_'2
  | Prod'labeled_statement_statement_safe_'1
  | Prod'labeled_statement_statement_safe_'0
  | Prod'labeled_statement_statement_dangerous_'2
  | Prod'labeled_statement_statement_dangerous_'1
  | Prod'labeled_statement_statement_dangerous_'0
  | Prod'jump_statement'4
  | Prod'jump_statement'3
  | Prod'jump_statement'2
  | Prod'jump_statement'1
  | Prod'jump_statement'0
  | Prod'iteration_statement_statement_safe_'13
  | Prod'iteration_statement_statement_safe_'12
  | Prod'iteration_statement_statement_safe_'11
  | Prod'iteration_statement_statement_safe_'10
  | Prod'iteration_statement_statement_safe_'9
  | Prod'iteration_statement_statement_safe_'8
  | Prod'iteration_statement_statement_safe_'7
  | Prod'iteration_statement_statement_safe_'6
  | Prod'iteration_statement_statement_safe_'5
  | Prod'iteration_statement_statement_safe_'4
  | Prod'iteration_statement_statement_safe_'3
  | Prod'iteration_statement_statement_safe_'2
  | Prod'iteration_statement_statement_safe_'1
  | Prod'iteration_statement_statement_safe_'0
  | Prod'iteration_statement_statement_dangerous_'13
  | Prod'iteration_statement_statement_dangerous_'12
  | Prod'iteration_statement_statement_dangerous_'11
  | Prod'iteration_statement_statement_dangerous_'10
  | Prod'iteration_statement_statement_dangerous_'9
  | Prod'iteration_statement_statement_dangerous_'8
  | Prod'iteration_statement_statement_dangerous_'7
  | Prod'iteration_statement_statement_dangerous_'6
  | Prod'iteration_statement_statement_dangerous_'5
  | Prod'iteration_statement_statement_dangerous_'4
  | Prod'iteration_statement_statement_dangerous_'3
  | Prod'iteration_statement_statement_dangerous_'2
  | Prod'iteration_statement_statement_dangerous_'1
  | Prod'iteration_statement_statement_dangerous_'0
  | Prod'initializer_list'3
  | Prod'initializer_list'2
  | Prod'initializer_list'1
  | Prod'initializer_list'0
  | Prod'init_declarator_list'1
  | Prod'init_declarator_list'0
  | Prod'init_declarator'1
  | Prod'init_declarator'0
  | Prod'inclusive_OR_expression'1
  | Prod'inclusive_OR_expression'0
  | Prod'identifier_list'1
  | Prod'identifier_list'0
  | Prod'gcc_attribute_word'2
  | Prod'gcc_attribute_word'1
  | Prod'gcc_attribute_word'0
  | Prod'gcc_attribute_list'1
  | Prod'gcc_attribute_list'0
  | Prod'gcc_attribute'3
  | Prod'gcc_attribute'2
  | Prod'gcc_attribute'1
  | Prod'gcc_attribute'0
  | Prod'function_specifier'1
  | Prod'function_specifier'0
  | Prod'function_definition'1
  | Prod'function_definition'0
  | Prod'external_declaration'2
  | Prod'external_declaration'1
  | Prod'external_declaration'0
  | Prod'expression_statement'1
  | Prod'expression_statement'0
  | Prod'expression'1
  | Prod'expression'0
  | Prod'exclusive_OR_expression'1
  | Prod'exclusive_OR_expression'0
  | Prod'equality_expression'2
  | Prod'equality_expression'1
  | Prod'equality_expression'0
  | Prod'enumerator_list'1
  | Prod'enumerator_list'0
  | Prod'enumerator'1
  | Prod'enumerator'0
  | Prod'enumeration_constant'0
  | Prod'enum_specifier'4
  | Prod'enum_specifier'3
  | Prod'enum_specifier'2
  | Prod'enum_specifier'1
  | Prod'enum_specifier'0
  | Prod'direct_declarator'8
  | Prod'direct_declarator'7
  | Prod'direct_declarator'6
  | Prod'direct_declarator'5
  | Prod'direct_declarator'4
  | Prod'direct_declarator'3
  | Prod'direct_declarator'2
  | Prod'direct_declarator'1
  | Prod'direct_declarator'0
  | Prod'direct_abstract_declarator'12
  | Prod'direct_abstract_declarator'11
  | Prod'direct_abstract_declarator'10
  | Prod'direct_abstract_declarator'9
  | Prod'direct_abstract_declarator'8
  | Prod'direct_abstract_declarator'7
  | Prod'direct_abstract_declarator'6
  | Prod'direct_abstract_declarator'5
  | Prod'direct_abstract_declarator'4
  | Prod'direct_abstract_declarator'3
  | Prod'direct_abstract_declarator'2
  | Prod'direct_abstract_declarator'1
  | Prod'direct_abstract_declarator'0
  | Prod'designator_list'1
  | Prod'designator_list'0
  | Prod'designator'1
  | Prod'designator'0
  | Prod'designation'0
  | Prod'declarator_noattrend'1
  | Prod'declarator_noattrend'0
  | Prod'declarator'0
  | Prod'declaration_specifiers_typespec_opt'4
  | Prod'declaration_specifiers_typespec_opt'3
  | Prod'declaration_specifiers_typespec_opt'2
  | Prod'declaration_specifiers_typespec_opt'1
  | Prod'declaration_specifiers_typespec_opt'0
  | Prod'declaration_specifiers'4
  | Prod'declaration_specifiers'3
  | Prod'declaration_specifiers'2
  | Prod'declaration_specifiers'1
  | Prod'declaration_specifiers'0
  | Prod'declaration_list'1
  | Prod'declaration_list'0
  | Prod'declaration'1
  | Prod'declaration'0
  | Prod'constant_expression'0
  | Prod'conditional_expression'1
  | Prod'conditional_expression'0
  | Prod'compound_statement'1
  | Prod'compound_statement'0
  | Prod'cast_expression'1
  | Prod'cast_expression'0
  | Prod'c_initializer'2
  | Prod'c_initializer'1
  | Prod'c_initializer'0
  | Prod'block_item_list'1
  | Prod'block_item_list'0
  | Prod'block_item'2
  | Prod'block_item'1
  | Prod'block_item'0
  | Prod'attribute_specifier_list'1
  | Prod'attribute_specifier_list'0
  | Prod'attribute_specifier'3
  | Prod'attribute_specifier'2
  | Prod'attribute_specifier'1
  | Prod'attribute_specifier'0
  | Prod'assignment_operator'10
  | Prod'assignment_operator'9
  | Prod'assignment_operator'8
  | Prod'assignment_operator'7
  | Prod'assignment_operator'6
  | Prod'assignment_operator'5
  | Prod'assignment_operator'4
  | Prod'assignment_operator'3
  | Prod'assignment_operator'2
  | Prod'assignment_operator'1
  | Prod'assignment_operator'0
  | Prod'assignment_expression'1
  | Prod'assignment_expression'0
  | Prod'asm_statement'0
  | Prod'asm_operands_ne'1
  | Prod'asm_operands_ne'0
  | Prod'asm_operands'1
  | Prod'asm_operands'0
  | Prod'asm_operand'0
  | Prod'asm_op_name'1
  | Prod'asm_op_name'0
  | Prod'asm_flags'1
  | Prod'asm_flags'0
  | Prod'asm_attributes'2
  | Prod'asm_attributes'1
  | Prod'asm_attributes'0
  | Prod'asm_arguments'3
  | Prod'asm_arguments'2
  | Prod'asm_arguments'1
  | Prod'asm_arguments'0
  | Prod'argument_expression_list'1
  | Prod'argument_expression_list'0
  | Prod'additive_expression'2
  | Prod'additive_expression'1
  | Prod'additive_expression'0
  | Prod'abstract_declarator'2
  | Prod'abstract_declarator'1
  | Prod'abstract_declarator'0
  | Prod'AND_expression'1
  | Prod'AND_expression'0

  type production = production'

  (** val productionNum : production coq_Numbered **)

  let productionNum =
    { inj = (fun x ->
      match x with
      | Prod'unary_operator'5 -> Coq_xH
      | Prod'unary_operator'4 -> Coq_xO Coq_xH
      | Prod'unary_operator'3 -> Coq_xI Coq_xH
      | Prod'unary_operator'2 -> Coq_xO (Coq_xO Coq_xH)
      | Prod'unary_operator'1 -> Coq_xI (Coq_xO Coq_xH)
      | Prod'unary_operator'0 -> Coq_xO (Coq_xI Coq_xH)
      | Prod'unary_expression'6 -> Coq_xI (Coq_xI Coq_xH)
      | Prod'unary_expression'5 -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
      | Prod'unary_expression'4 -> Coq_xI (Coq_xO (Coq_xO Coq_xH))
      | Prod'unary_expression'3 -> Coq_xO (Coq_xI (Coq_xO Coq_xH))
      | Prod'unary_expression'2 -> Coq_xI (Coq_xI (Coq_xO Coq_xH))
      | Prod'unary_expression'1 -> Coq_xO (Coq_xO (Coq_xI Coq_xH))
      | Prod'unary_expression'0 -> Coq_xI (Coq_xO (Coq_xI Coq_xH))
      | Prod'type_specifier'12 -> Coq_xO (Coq_xI (Coq_xI Coq_xH))
      | Prod'type_specifier'11 -> Coq_xI (Coq_xI (Coq_xI Coq_xH))
      | Prod'type_specifier'10 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Prod'type_specifier'9 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Prod'type_specifier'8 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Prod'type_specifier'7 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Prod'type_specifier'6 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Prod'type_specifier'5 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Prod'type_specifier'4 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Prod'type_specifier'3 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Prod'type_specifier'2 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Prod'type_specifier'1 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Prod'type_specifier'0 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Prod'type_qualifier_noattr'2 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Prod'type_qualifier_noattr'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Prod'type_qualifier_noattr'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Prod'type_qualifier_list'1 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Prod'type_qualifier_list'0 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Prod'type_qualifier'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod'type_qualifier'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod'type_name'1 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod'type_name'0 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod'translation_unit_file'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod'translation_unit_file'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod'translation_unit'3 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod'translation_unit'2 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod'translation_unit'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod'translation_unit'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_or_union_specifier'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_or_union_specifier'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_or_union_specifier'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_or_union'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_or_union'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_declarator_list'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod'struct_declarator_list'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declarator'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declarator'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declarator'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declaration_list'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declaration_list'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declaration'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod'struct_declaration'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod'storage_class_specifier'4 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod'storage_class_specifier'3 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod'storage_class_specifier'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod'storage_class_specifier'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod'storage_class_specifier'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod'statement_safe'6 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod'statement_safe'5 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod'statement_safe'4 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod'statement_safe'3 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_safe'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_safe'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_safe'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'6 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'5 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'4 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'3 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'2 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'statement_dangerous'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'specifier_qualifier_list'3 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'specifier_qualifier_list'2 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'specifier_qualifier_list'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'specifier_qualifier_list'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'shift_expression'2 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod'shift_expression'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'shift_expression'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'selection_statement_safe'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'selection_statement_safe'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'selection_statement_dangerous'2 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'selection_statement_dangerous'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'selection_statement_dangerous'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'relational_expression'4 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'relational_expression'3 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'relational_expression'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'relational_expression'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'relational_expression'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'primary_expression'3 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'primary_expression'2 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'primary_expression'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'primary_expression'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod'postfix_expression'12 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'11 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'10 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'9 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'8 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'7 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'6 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'5 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'4 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'3 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'postfix_expression'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'pointer'3 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'pointer'2 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'pointer'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod'pointer'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_type_list'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_type_list'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_list'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_list'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_declaration'2 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_declaration'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'parameter_declaration'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'multiplicative_expression'3 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'multiplicative_expression'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'multiplicative_expression'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'multiplicative_expression'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'logical_OR_expression'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'logical_OR_expression'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'logical_AND_expression'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'logical_AND_expression'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod'labeled_statement_statement_safe_'2 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'labeled_statement_statement_safe_'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'labeled_statement_statement_safe_'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'labeled_statement_statement_dangerous_'2 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'labeled_statement_statement_dangerous_'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'labeled_statement_statement_dangerous_'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'jump_statement'4 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'jump_statement'3 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'jump_statement'2 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'jump_statement'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'jump_statement'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'13 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'12 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'11 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'10 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'9 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'8 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'7 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'6 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'5 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'4 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'3 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'2 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_safe_'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'13 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'12 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'11 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'10 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'9 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'8 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'7 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'6 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'5 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'4 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'3 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'2 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'iteration_statement_statement_dangerous_'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'initializer_list'3 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'initializer_list'2 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'initializer_list'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'initializer_list'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'init_declarator_list'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'init_declarator_list'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'init_declarator'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'init_declarator'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'inclusive_OR_expression'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'inclusive_OR_expression'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'identifier_list'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'identifier_list'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute_word'2 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute_word'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute_word'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute_list'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute_list'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute'3 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'gcc_attribute'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'function_specifier'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'function_specifier'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'function_definition'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'function_definition'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod'external_declaration'2 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'external_declaration'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'external_declaration'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'expression_statement'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'expression_statement'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'expression'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'expression'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'exclusive_OR_expression'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'exclusive_OR_expression'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'equality_expression'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'equality_expression'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'equality_expression'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enumerator_list'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enumerator_list'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enumerator'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enumerator'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enumeration_constant'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enum_specifier'4 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enum_specifier'3 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enum_specifier'2 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enum_specifier'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'enum_specifier'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'8 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'7 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'6 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'5 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'4 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'3 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'2 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_declarator'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'12 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'11 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'10 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'9 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'8 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'7 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'6 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'5 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'4 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'3 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'direct_abstract_declarator'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'designator_list'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'designator_list'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'designator'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'designator'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'designation'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declarator_noattrend'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declarator_noattrend'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declarator'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers_typespec_opt'4 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers_typespec_opt'3 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers_typespec_opt'2 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers_typespec_opt'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers_typespec_opt'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers'4 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers'3 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers'2 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_specifiers'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_list'1 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration_list'0 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod'declaration'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'declaration'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'constant_expression'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'conditional_expression'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'conditional_expression'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'compound_statement'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'compound_statement'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'cast_expression'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'cast_expression'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'c_initializer'2 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'c_initializer'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'c_initializer'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'block_item_list'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'block_item_list'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'block_item'2 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'block_item'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'block_item'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier_list'1 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier_list'0 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier'3 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier'2 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'attribute_specifier'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'10 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'9 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'8 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'7 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'6 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'5 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'4 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'3 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'2 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_operator'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_expression'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'assignment_expression'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_statement'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_operands_ne'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_operands_ne'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_operands'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_operands'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_operand'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_op_name'1 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_op_name'0 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_flags'1 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_flags'0 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_attributes'2 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_attributes'1 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_attributes'0 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_arguments'3 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_arguments'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_arguments'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'asm_arguments'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'argument_expression_list'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'argument_expression_list'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'additive_expression'2 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'additive_expression'1 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'additive_expression'0 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'abstract_declarator'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'abstract_declarator'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'abstract_declarator'0 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'AND_expression'1 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod'AND_expression'0 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))); surj = (fun n ->
      match n with
      | Coq_xI p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_list'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'function_definition'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xH -> Prod'logical_AND_expression'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'12
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'7)
                        | Coq_xH -> Prod'primary_expression'0)
                     | Coq_xH -> Prod'statement_safe'4)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'designator'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_attributes'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'inclusive_OR_expression'1)
                        | Coq_xH -> Prod'pointer'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enumerator'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'block_item'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'9)
                        | Coq_xH -> Prod'shift_expression'2)
                     | Coq_xH -> Prod'struct_declarator_list'1)
                  | Coq_xH -> Prod'type_qualifier_list'0)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH ->
                             Prod'declaration_specifiers_typespec_opt'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'additive_expression'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute_list'0)
                        | Coq_xH -> Prod'parameter_declaration'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'7
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'10
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'1)
                        | Coq_xH -> Prod'relational_expression'4)
                     | Coq_xH -> Prod'struct_declaration'0)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'4
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_operands'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'initializer_list'3)
                        | Coq_xH -> Prod'postfix_expression'5)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'exclusive_OR_expression'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'cast_expression'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'jump_statement'3)
                        | Coq_xH -> Prod'statement_dangerous'3)
                     | Coq_xH -> Prod'translation_unit'2)
                  | Coq_xH -> Prod'type_specifier'3)
               | Coq_xH -> Prod'type_specifier'11)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_specifiers'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'abstract_declarator'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute'0)
                        | Coq_xH -> Prod'multiplicative_expression'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'3
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'6
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'11)
                        | Coq_xH -> Prod'relational_expression'0)
                     | Coq_xH -> Prod'storage_class_specifier'1)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_op_name'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'init_declarator_list'1)
                        | Coq_xH -> Prod'postfix_expression'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'equality_expression'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'c_initializer'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'13)
                        | Coq_xH -> Prod'specifier_qualifier_list'3)
                     | Coq_xH -> Prod'struct_or_union_specifier'1)
                  | Coq_xH -> Prod'type_qualifier_noattr'2)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declarator'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_arguments'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute_word'2)
                        | Coq_xH -> Prod'parameter_list'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enum_specifier'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier'3
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'5)
                        | Coq_xH -> Prod'selection_statement_safe'0)
                     | Coq_xH -> Prod'struct_declarator'0)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'8
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'3)
                        | Coq_xH -> Prod'postfix_expression'9)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'expression_statement'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'conditional_expression'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_dangerous_'2)
                        | Coq_xH -> Prod'statement_safe'0)
                     | Coq_xH -> Prod'type_name'0)
                  | Coq_xH -> Prod'type_specifier'7)
               | Coq_xH -> Prod'unary_expression'2)
            | Coq_xH -> Prod'unary_expression'6)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_specifiers'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'AND_expression'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'function_specifier'0)
                        | Coq_xH -> Prod'logical_OR_expression'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'4
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'9)
                        | Coq_xH -> Prod'primary_expression'2)
                     | Coq_xH -> Prod'statement_safe'6)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'designator_list'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_flags'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'init_declarator'1)
                        | Coq_xH -> Prod'pointer'3)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enumerator_list'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'block_item_list'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'11)
                        | Coq_xH -> Prod'specifier_qualifier_list'1)
                     | Coq_xH -> Prod'struct_or_union'1)
                  | Coq_xH -> Prod'type_qualifier_noattr'0)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH ->
                             Prod'declaration_specifiers_typespec_opt'3
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'argument_expression_list'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute_word'0)
                        | Coq_xH -> Prod'parameter_declaration'2)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enum_specifier'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'3)
                        | Coq_xH -> Prod'selection_statement_dangerous'1)
                     | Coq_xH -> Prod'struct_declaration_list'0)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'6
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_operands_ne'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'1)
                        | Coq_xH -> Prod'postfix_expression'7)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'expression'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'compound_statement'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_dangerous_'0)
                        | Coq_xH -> Prod'statement_dangerous'5)
                     | Coq_xH -> Prod'translation_unit_file'0)
                  | Coq_xH -> Prod'type_specifier'5)
               | Coq_xH -> Prod'unary_expression'0)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_specifiers'4
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'additive_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute'2)
                        | Coq_xH -> Prod'multiplicative_expression'2)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'5
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'8
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'13)
                        | Coq_xH -> Prod'relational_expression'2)
                     | Coq_xH -> Prod'storage_class_specifier'3)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_operand'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'initializer_list'1)
                        | Coq_xH -> Prod'postfix_expression'3)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'equality_expression'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'c_initializer'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'jump_statement'1)
                        | Coq_xH -> Prod'statement_dangerous'1)
                     | Coq_xH -> Prod'translation_unit'0)
                  | Coq_xH -> Prod'type_specifier'1)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declarator_noattrend'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_arguments'3
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'identifier_list'1)
                        | Coq_xH -> Prod'parameter_type_list'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enum_specifier'4
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier_list'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'7)
                        | Coq_xH -> Prod'shift_expression'0)
                     | Coq_xH -> Prod'struct_declarator'2)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'10
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'5)
                        | Coq_xH -> Prod'postfix_expression'11)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'external_declaration'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'declaration'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_safe_'1)
                        | Coq_xH -> Prod'statement_safe'2)
                     | Coq_xH -> Prod'type_qualifier'0)
                  | Coq_xH -> Prod'type_specifier'9)
               | Coq_xH -> Prod'unary_expression'4)
            | Coq_xH -> Prod'unary_operator'1)
         | Coq_xH -> Prod'unary_operator'3)
      | Coq_xO p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_list'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'AND_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'function_definition'1)
                        | Coq_xH -> Prod'logical_AND_expression'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'3
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'8)
                        | Coq_xH -> Prod'primary_expression'1)
                     | Coq_xH -> Prod'statement_safe'5)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'designator'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_attributes'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'init_declarator'0)
                        | Coq_xH -> Prod'pointer'2)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enumerator'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'block_item'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'10)
                        | Coq_xH -> Prod'specifier_qualifier_list'0)
                     | Coq_xH -> Prod'struct_or_union'0)
                  | Coq_xH -> Prod'type_qualifier_list'1)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH ->
                             Prod'declaration_specifiers_typespec_opt'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'argument_expression_list'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute_list'1)
                        | Coq_xH -> Prod'parameter_declaration'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'8
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'2)
                        | Coq_xH -> Prod'selection_statement_dangerous'0)
                     | Coq_xH -> Prod'struct_declaration'1)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'5
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_operands_ne'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'0)
                        | Coq_xH -> Prod'postfix_expression'6)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'expression'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'compound_statement'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'jump_statement'4)
                        | Coq_xH -> Prod'statement_dangerous'4)
                     | Coq_xH -> Prod'translation_unit'3)
                  | Coq_xH -> Prod'type_specifier'4)
               | Coq_xH -> Prod'type_specifier'12)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_specifiers'3
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'abstract_declarator'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute'1)
                        | Coq_xH -> Prod'multiplicative_expression'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'4
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'7
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'12)
                        | Coq_xH -> Prod'relational_expression'1)
                     | Coq_xH -> Prod'storage_class_specifier'2)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_op_name'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'initializer_list'0)
                        | Coq_xH -> Prod'postfix_expression'2)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'equality_expression'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'c_initializer'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'jump_statement'0)
                        | Coq_xH -> Prod'statement_dangerous'0)
                     | Coq_xH -> Prod'struct_or_union_specifier'2)
                  | Coq_xH -> Prod'type_specifier'0)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declarator_noattrend'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_arguments'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'identifier_list'0)
                        | Coq_xH -> Prod'parameter_type_list'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enum_specifier'3
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier_list'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'6)
                        | Coq_xH -> Prod'selection_statement_safe'1)
                     | Coq_xH -> Prod'struct_declarator'1)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'9
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_expression'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'4)
                        | Coq_xH -> Prod'postfix_expression'10)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'external_declaration'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'constant_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_safe_'0)
                        | Coq_xH -> Prod'statement_safe'1)
                     | Coq_xH -> Prod'type_name'1)
                  | Coq_xH -> Prod'type_specifier'8)
               | Coq_xH -> Prod'unary_expression'3)
            | Coq_xH -> Prod'unary_operator'0)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'declaration_specifiers'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'abstract_declarator'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'function_specifier'1)
                        | Coq_xH -> Prod'logical_OR_expression'1)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'5
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'10)
                        | Coq_xH -> Prod'primary_expression'3)
                     | Coq_xH -> Prod'storage_class_specifier'0)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'designator_list'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_flags'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'init_declarator_list'0)
                        | Coq_xH -> Prod'postfix_expression'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enumerator_list'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'block_item_list'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'12)
                        | Coq_xH -> Prod'specifier_qualifier_list'2)
                     | Coq_xH -> Prod'struct_or_union_specifier'0)
                  | Coq_xH -> Prod'type_qualifier_noattr'1)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH ->
                             Prod'declaration_specifiers_typespec_opt'4
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_arguments'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute_word'1)
                        | Coq_xH -> Prod'parameter_list'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enum_specifier'1
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'attribute_specifier'2
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'4)
                        | Coq_xH -> Prod'selection_statement_dangerous'2)
                     | Coq_xH -> Prod'struct_declaration_list'1)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'7
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_statement'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'2)
                        | Coq_xH -> Prod'postfix_expression'8)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'expression_statement'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'conditional_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_dangerous_'1)
                        | Coq_xH -> Prod'statement_dangerous'6)
                     | Coq_xH -> Prod'translation_unit_file'1)
                  | Coq_xH -> Prod'type_specifier'6)
               | Coq_xH -> Prod'unary_expression'1)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH ->
                             Prod'declaration_specifiers_typespec_opt'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'additive_expression'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'gcc_attribute'3)
                        | Coq_xH -> Prod'multiplicative_expression'3)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_declarator'6
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'9
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'0)
                        | Coq_xH -> Prod'relational_expression'3)
                     | Coq_xH -> Prod'storage_class_specifier'4)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'3
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_operands'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'initializer_list'2)
                        | Coq_xH -> Prod'postfix_expression'4)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'exclusive_OR_expression'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'cast_expression'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'jump_statement'2)
                        | Coq_xH -> Prod'statement_dangerous'2)
                     | Coq_xH -> Prod'translation_unit'1)
                  | Coq_xH -> Prod'type_specifier'2)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'designation'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'asm_attributes'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH -> Prod'inclusive_OR_expression'0)
                        | Coq_xH -> Prod'pointer'0)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'enumeration_constant'0
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'block_item'0
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_safe_'8)
                        | Coq_xH -> Prod'shift_expression'1)
                     | Coq_xH -> Prod'struct_declarator_list'0)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'direct_abstract_declarator'11
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'assignment_operator'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'iteration_statement_statement_dangerous_'6)
                        | Coq_xH -> Prod'postfix_expression'12)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xH -> Prod'external_declaration'2
                           | _ -> Prod'unary_operator'5)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI _ -> Prod'unary_operator'5
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod'declaration'1
                              | _ -> Prod'unary_operator'5)
                           | Coq_xH ->
                             Prod'labeled_statement_statement_safe_'2)
                        | Coq_xH -> Prod'statement_safe'3)
                     | Coq_xH -> Prod'type_qualifier'1)
                  | Coq_xH -> Prod'type_specifier'10)
               | Coq_xH -> Prod'unary_expression'5)
            | Coq_xH -> Prod'unary_operator'2)
         | Coq_xH -> Prod'unary_operator'4)
      | Coq_xH -> Prod'unary_operator'5); inj_bound = (Coq_xO (Coq_xI (Coq_xI
      (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))))) }

  (** val coq_ProductionAlph : production coq_Alphabet **)

  let coq_ProductionAlph =
    coq_NumberedAlphabet productionNum

  (** val prod_contents :
      production -> (nonterminal * symbol list, symbol_semantic_type
      arrows_right) sigT **)

  let prod_contents p =
    let box = fun x x0 -> Coq_existT (x, x0) in
    (match p with
     | Prod'unary_operator'5 ->
       Obj.magic box (Coq_unary_operator'nt, ((T BANG't) :: [])) (fun loc0 ->
         (NOT, loc0))
     | Prod'unary_operator'4 ->
       Obj.magic box (Coq_unary_operator'nt, ((T TILDE't) :: []))
         (fun loc0 -> (BNOT, loc0))
     | Prod'unary_operator'3 ->
       Obj.magic box (Coq_unary_operator'nt, ((T MINUS't) :: []))
         (fun loc0 -> (Cabs.MINUS, loc0))
     | Prod'unary_operator'2 ->
       Obj.magic box (Coq_unary_operator'nt, ((T PLUS't) :: [])) (fun loc0 ->
         (Cabs.PLUS, loc0))
     | Prod'unary_operator'1 ->
       Obj.magic box (Coq_unary_operator'nt, ((T STAR't) :: [])) (fun loc0 ->
         (MEMOF, loc0))
     | Prod'unary_operator'0 ->
       Obj.magic box (Coq_unary_operator'nt, ((T AND't) :: [])) (fun loc0 ->
         (ADDROF, loc0))
     | Prod'unary_expression'6 ->
       Obj.magic box (Coq_unary_expression'nt, ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: ((T ALIGNOF't) :: [])))))
         (fun _ typ _ loc0 -> ((Cabs.ALIGNOF typ), loc0))
     | Prod'unary_expression'5 ->
       Obj.magic box (Coq_unary_expression'nt, ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: ((T SIZEOF't) :: [])))))
         (fun _ typ _ loc0 -> ((TYPE_SIZEOF typ), loc0))
     | Prod'unary_expression'4 ->
       Obj.magic box (Coq_unary_expression'nt, ((NT
         Coq_unary_expression'nt) :: ((T SIZEOF't) :: []))) (fun expr loc0 ->
         ((EXPR_SIZEOF (fst expr)), loc0))
     | Prod'unary_expression'3 ->
       Obj.magic box (Coq_unary_expression'nt, ((NT
         Coq_cast_expression'nt) :: ((NT Coq_unary_operator'nt) :: [])))
         (fun expr op -> ((UNARY ((fst op), (fst expr))), (snd op)))
     | Prod'unary_expression'2 ->
       Obj.magic box (Coq_unary_expression'nt, ((NT
         Coq_unary_expression'nt) :: ((T DEC't) :: []))) (fun expr loc0 ->
         ((UNARY (PREDECR, (fst expr))), loc0))
     | Prod'unary_expression'1 ->
       Obj.magic box (Coq_unary_expression'nt, ((NT
         Coq_unary_expression'nt) :: ((T INC't) :: []))) (fun expr loc0 ->
         ((UNARY (PREINCR, (fst expr))), loc0))
     | Prod'unary_expression'0 ->
       Obj.magic box (Coq_unary_expression'nt, ((NT
         Coq_postfix_expression'nt) :: [])) (fun expr -> expr)
     | Prod'type_specifier'12 ->
       Obj.magic box (Coq_type_specifier'nt, ((T TYPEDEF_NAME't) :: []))
         (fun id -> ((Tnamed (fst id)), (snd id)))
     | Prod'type_specifier'11 ->
       Obj.magic box (Coq_type_specifier'nt, ((NT
         Coq_enum_specifier'nt) :: [])) (fun spec -> spec)
     | Prod'type_specifier'10 ->
       Obj.magic box (Coq_type_specifier'nt, ((NT
         Coq_struct_or_union_specifier'nt) :: [])) (fun spec -> spec)
     | Prod'type_specifier'9 ->
       Obj.magic box (Coq_type_specifier'nt, ((T UNDERSCORE_BOOL't) :: []))
         (fun loc0 -> (T_Bool, loc0))
     | Prod'type_specifier'8 ->
       Obj.magic box (Coq_type_specifier'nt, ((T UNSIGNED't) :: []))
         (fun loc0 -> (Tunsigned, loc0))
     | Prod'type_specifier'7 ->
       Obj.magic box (Coq_type_specifier'nt, ((T SIGNED't) :: []))
         (fun loc0 -> (Tsigned, loc0))
     | Prod'type_specifier'6 ->
       Obj.magic box (Coq_type_specifier'nt, ((T DOUBLE't) :: []))
         (fun loc0 -> (Tdouble, loc0))
     | Prod'type_specifier'5 ->
       Obj.magic box (Coq_type_specifier'nt, ((T FLOAT't) :: []))
         (fun loc0 -> (Tfloat, loc0))
     | Prod'type_specifier'4 ->
       Obj.magic box (Coq_type_specifier'nt, ((T LONG't) :: [])) (fun loc0 ->
         (Tlong, loc0))
     | Prod'type_specifier'3 ->
       Obj.magic box (Coq_type_specifier'nt, ((T INT't) :: [])) (fun loc0 ->
         (Tint, loc0))
     | Prod'type_specifier'2 ->
       Obj.magic box (Coq_type_specifier'nt, ((T SHORT't) :: []))
         (fun loc0 -> (Tshort, loc0))
     | Prod'type_specifier'1 ->
       Obj.magic box (Coq_type_specifier'nt, ((T CHAR't) :: [])) (fun loc0 ->
         (Tchar, loc0))
     | Prod'type_specifier'0 ->
       Obj.magic box (Coq_type_specifier'nt, ((T VOID't) :: [])) (fun loc0 ->
         (Tvoid, loc0))
     | Prod'type_qualifier_noattr'2 ->
       Obj.magic box (Coq_type_qualifier_noattr'nt, ((T VOLATILE't) :: []))
         (fun loc0 -> (CV_VOLATILE, loc0))
     | Prod'type_qualifier_noattr'1 ->
       Obj.magic box (Coq_type_qualifier_noattr'nt, ((T RESTRICT't) :: []))
         (fun loc0 -> (CV_RESTRICT, loc0))
     | Prod'type_qualifier_noattr'0 ->
       Obj.magic box (Coq_type_qualifier_noattr'nt, ((T CONST't) :: []))
         (fun loc0 -> (CV_CONST, loc0))
     | Prod'type_qualifier_list'1 ->
       Obj.magic box (Coq_type_qualifier_list'nt, ((NT
         Coq_type_qualifier'nt) :: ((NT Coq_type_qualifier_list'nt) :: [])))
         (fun qualt qualq -> (fst qualt) :: qualq)
     | Prod'type_qualifier_list'0 ->
       Obj.magic box (Coq_type_qualifier_list'nt, ((NT
         Coq_type_qualifier'nt) :: [])) (fun qual -> (fst qual) :: [])
     | Prod'type_qualifier'1 ->
       Obj.magic box (Coq_type_qualifier'nt, ((NT
         Coq_attribute_specifier'nt) :: [])) (fun attr -> ((CV_ATTR
         (fst attr)), (snd attr)))
     | Prod'type_qualifier'0 ->
       Obj.magic box (Coq_type_qualifier'nt, ((NT
         Coq_type_qualifier_noattr'nt) :: [])) (fun qual -> qual)
     | Prod'type_name'1 ->
       Obj.magic box (Coq_type_name'nt, ((NT
         Coq_abstract_declarator'nt) :: ((NT
         Coq_specifier_qualifier_list'nt) :: []))) (fun typ specqual ->
         ((fst specqual), typ))
     | Prod'type_name'0 ->
       Obj.magic box (Coq_type_name'nt, ((NT
         Coq_specifier_qualifier_list'nt) :: [])) (fun specqual ->
         ((fst specqual), JUSTBASE))
     | Prod'translation_unit_file'1 ->
       Obj.magic box (Coq_translation_unit_file'nt, ((T EOF't) :: []))
         (fun _ -> [])
     | Prod'translation_unit_file'0 ->
       Obj.magic box (Coq_translation_unit_file'nt, ((T EOF't) :: ((NT
         Coq_translation_unit'nt) :: []))) (fun _ -> rev')
     | Prod'translation_unit'3 ->
       Obj.magic box (Coq_translation_unit'nt, ((T SEMICOLON't) :: []))
         (fun _ -> [])
     | Prod'translation_unit'2 ->
       Obj.magic box (Coq_translation_unit'nt, ((T SEMICOLON't) :: ((NT
         Coq_translation_unit'nt) :: []))) (fun _ tu -> tu)
     | Prod'translation_unit'1 ->
       Obj.magic box (Coq_translation_unit'nt, ((NT
         Coq_external_declaration'nt) :: ((NT
         Coq_translation_unit'nt) :: []))) (fun deft defq -> deft :: defq)
     | Prod'translation_unit'0 ->
       Obj.magic box (Coq_translation_unit'nt, ((NT
         Coq_external_declaration'nt) :: [])) (fun def -> def :: [])
     | Prod'struct_or_union_specifier'2 ->
       Obj.magic box (Coq_struct_or_union_specifier'nt, ((T
         OTHER_NAME't) :: ((NT Coq_attribute_specifier_list'nt) :: ((NT
         Coq_struct_or_union'nt) :: [])))) (fun id attrs str_uni ->
         ((Tstruct_union ((fst str_uni), (Some (fst id)), None, attrs)),
         (snd str_uni)))
     | Prod'struct_or_union_specifier'1 ->
       Obj.magic box (Coq_struct_or_union_specifier'nt, ((T RBRACE't) :: ((NT
         Coq_struct_declaration_list'nt) :: ((T LBRACE't) :: ((NT
         Coq_attribute_specifier_list'nt) :: ((NT
         Coq_struct_or_union'nt) :: [])))))) (fun _ decls _ attrs str_uni ->
         ((Tstruct_union ((fst str_uni), None, (Some (rev' decls)), attrs)),
         (snd str_uni)))
     | Prod'struct_or_union_specifier'0 ->
       Obj.magic box (Coq_struct_or_union_specifier'nt, ((T RBRACE't) :: ((NT
         Coq_struct_declaration_list'nt) :: ((T LBRACE't) :: ((T
         OTHER_NAME't) :: ((NT Coq_attribute_specifier_list'nt) :: ((NT
         Coq_struct_or_union'nt) :: [])))))))
         (fun _ decls _ id attrs str_uni -> ((Tstruct_union ((fst str_uni),
         (Some (fst id)), (Some (rev' decls)), attrs)), (snd str_uni)))
     | Prod'struct_or_union'1 ->
       Obj.magic box (Coq_struct_or_union'nt, ((T UNION't) :: []))
         (fun loc0 -> (Cabs.UNION, loc0))
     | Prod'struct_or_union'0 ->
       Obj.magic box (Coq_struct_or_union'nt, ((T STRUCT't) :: []))
         (fun loc0 -> (Cabs.STRUCT, loc0))
     | Prod'struct_declarator_list'1 ->
       Obj.magic box (Coq_struct_declarator_list'nt, ((NT
         Coq_struct_declarator'nt) :: ((T COMMA't) :: ((NT
         Coq_struct_declarator_list'nt) :: [])))) (fun declt _ declq ->
         declt :: declq)
     | Prod'struct_declarator_list'0 ->
       Obj.magic box (Coq_struct_declarator_list'nt, ((NT
         Coq_struct_declarator'nt) :: [])) (fun decl -> decl :: [])
     | Prod'struct_declarator'2 ->
       Obj.magic box (Coq_struct_declarator'nt, ((NT
         Coq_constant_expression'nt) :: ((T COLON't) :: []))) (fun expr _ ->
         (None, (Some (fst expr))))
     | Prod'struct_declarator'1 ->
       Obj.magic box (Coq_struct_declarator'nt, ((NT
         Coq_constant_expression'nt) :: ((T COLON't) :: ((NT
         Coq_declarator'nt) :: [])))) (fun expr _ decl -> ((Some decl), (Some
         (fst expr))))
     | Prod'struct_declarator'0 ->
       Obj.magic box (Coq_struct_declarator'nt, ((NT
         Coq_declarator'nt) :: [])) (fun decl -> ((Some decl), None))
     | Prod'struct_declaration_list'1 ->
       Obj.magic box (Coq_struct_declaration_list'nt, ((NT
         Coq_struct_declaration'nt) :: ((NT
         Coq_struct_declaration_list'nt) :: []))) (fun tdecls qdecls ->
         tdecls :: qdecls)
     | Prod'struct_declaration_list'0 ->
       Obj.magic box (Coq_struct_declaration_list'nt, []) []
     | Prod'struct_declaration'1 ->
       Obj.magic box (Coq_struct_declaration'nt, ((T SEMICOLON't) :: ((NT
         Coq_specifier_qualifier_list'nt) :: []))) (fun _ decspec ->
         Field_group ((fst decspec), ((None, None) :: []), (snd decspec)))
     | Prod'struct_declaration'0 ->
       Obj.magic box (Coq_struct_declaration'nt, ((T SEMICOLON't) :: ((NT
         Coq_struct_declarator_list'nt) :: ((NT
         Coq_specifier_qualifier_list'nt) :: [])))) (fun _ decls decspec ->
         Field_group ((fst decspec), (rev' decls), (snd decspec)))
     | Prod'storage_class_specifier'4 ->
       Obj.magic box (Coq_storage_class_specifier'nt, ((T REGISTER't) :: []))
         (fun loc0 -> (Cabs.REGISTER, loc0))
     | Prod'storage_class_specifier'3 ->
       Obj.magic box (Coq_storage_class_specifier'nt, ((T AUTO't) :: []))
         (fun loc0 -> (Cabs.AUTO, loc0))
     | Prod'storage_class_specifier'2 ->
       Obj.magic box (Coq_storage_class_specifier'nt, ((T STATIC't) :: []))
         (fun loc0 -> (Cabs.STATIC, loc0))
     | Prod'storage_class_specifier'1 ->
       Obj.magic box (Coq_storage_class_specifier'nt, ((T EXTERN't) :: []))
         (fun loc0 -> (Cabs.EXTERN, loc0))
     | Prod'storage_class_specifier'0 ->
       Obj.magic box (Coq_storage_class_specifier'nt, ((T TYPEDEF't) :: []))
         (fun loc0 -> (Cabs.TYPEDEF, loc0))
     | Prod'statement_safe'6 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_asm_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_safe'5 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_jump_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_safe'4 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_iteration_statement_statement_safe_'nt) :: [])) (fun stmt ->
         stmt)
     | Prod'statement_safe'3 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_selection_statement_safe'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_safe'2 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_expression_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_safe'1 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_compound_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_safe'0 ->
       Obj.magic box (Coq_statement_safe'nt, ((NT
         Coq_labeled_statement_statement_safe_'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'6 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_asm_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'5 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_jump_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'4 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_iteration_statement_statement_dangerous_'nt) :: []))
         (fun stmt -> stmt)
     | Prod'statement_dangerous'3 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_selection_statement_dangerous'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'2 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_expression_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'1 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_compound_statement'nt) :: [])) (fun stmt -> stmt)
     | Prod'statement_dangerous'0 ->
       Obj.magic box (Coq_statement_dangerous'nt, ((NT
         Coq_labeled_statement_statement_dangerous_'nt) :: [])) (fun stmt ->
         stmt)
     | Prod'specifier_qualifier_list'3 ->
       Obj.magic box (Coq_specifier_qualifier_list'nt, ((NT
         Coq_type_qualifier'nt) :: [])) (fun qual -> (((SpecCV
         (fst qual)) :: []), (snd qual)))
     | Prod'specifier_qualifier_list'2 ->
       Obj.magic box (Coq_specifier_qualifier_list'nt, ((NT
         Coq_specifier_qualifier_list'nt) :: ((NT
         Coq_type_qualifier'nt) :: []))) (fun rest qual -> (((SpecCV
         (fst qual)) :: (fst rest)), (snd qual)))
     | Prod'specifier_qualifier_list'1 ->
       Obj.magic box (Coq_specifier_qualifier_list'nt, ((NT
         Coq_type_specifier'nt) :: [])) (fun typ -> (((SpecType
         (fst typ)) :: []), (snd typ)))
     | Prod'specifier_qualifier_list'0 ->
       Obj.magic box (Coq_specifier_qualifier_list'nt, ((NT
         Coq_specifier_qualifier_list'nt) :: ((NT
         Coq_type_specifier'nt) :: []))) (fun rest typ -> (((SpecType
         (fst typ)) :: (fst rest)), (snd typ)))
     | Prod'shift_expression'2 ->
       Obj.magic box (Coq_shift_expression'nt, ((NT
         Coq_additive_expression'nt) :: ((T RIGHT't) :: ((NT
         Coq_shift_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (SHR, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'shift_expression'1 ->
       Obj.magic box (Coq_shift_expression'nt, ((NT
         Coq_additive_expression'nt) :: ((T LEFT't) :: ((NT
         Coq_shift_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (SHL, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'shift_expression'0 ->
       Obj.magic box (Coq_shift_expression'nt, ((NT
         Coq_additive_expression'nt) :: [])) (fun expr -> expr)
     | Prod'selection_statement_safe'1 ->
       Obj.magic box (Coq_selection_statement_safe'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T SWITCH't) :: []))))))
         (fun stmt _ expr _ loc0 -> Cabs.SWITCH ((fst expr), stmt, loc0))
     | Prod'selection_statement_safe'0 ->
       Obj.magic box (Coq_selection_statement_safe'nt, ((NT
         Coq_statement_safe'nt) :: ((T ELSE't) :: ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T IF_'t) :: []))))))))
         (fun stmt2 _ stmt1 _ expr _ loc0 -> If ((fst expr), stmt1, (Some
         stmt2), loc0))
     | Prod'selection_statement_dangerous'2 ->
       Obj.magic box (Coq_selection_statement_dangerous'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T SWITCH't) :: []))))))
         (fun stmt _ expr _ loc0 -> Cabs.SWITCH ((fst expr), stmt, loc0))
     | Prod'selection_statement_dangerous'1 ->
       Obj.magic box (Coq_selection_statement_dangerous'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T ELSE't) :: ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T IF_'t) :: []))))))))
         (fun stmt2 _ stmt1 _ expr _ loc0 -> If ((fst expr), stmt1, (Some
         stmt2), loc0))
     | Prod'selection_statement_dangerous'0 ->
       Obj.magic box (Coq_selection_statement_dangerous'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T IF_'t) :: []))))))
         (fun stmt _ expr _ loc0 -> If ((fst expr), stmt, None, loc0))
     | Prod'relational_expression'4 ->
       Obj.magic box (Coq_relational_expression'nt, ((NT
         Coq_shift_expression'nt) :: ((T GEQ't) :: ((NT
         Coq_relational_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (GE, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'relational_expression'3 ->
       Obj.magic box (Coq_relational_expression'nt, ((NT
         Coq_shift_expression'nt) :: ((T LEQ't) :: ((NT
         Coq_relational_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (LE, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'relational_expression'2 ->
       Obj.magic box (Coq_relational_expression'nt, ((NT
         Coq_shift_expression'nt) :: ((T GT't) :: ((NT
         Coq_relational_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (Cabs.GT, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'relational_expression'1 ->
       Obj.magic box (Coq_relational_expression'nt, ((NT
         Coq_shift_expression'nt) :: ((T LT't) :: ((NT
         Coq_relational_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (Cabs.LT, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'relational_expression'0 ->
       Obj.magic box (Coq_relational_expression'nt, ((NT
         Coq_shift_expression'nt) :: [])) (fun expr -> expr)
     | Prod'primary_expression'3 ->
       Obj.magic box (Coq_primary_expression'nt, ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: [])))) (fun _ expr loc0 ->
         ((fst expr), loc0))
     | Prod'primary_expression'2 ->
       Obj.magic box (Coq_primary_expression'nt, ((T
         STRING_LITERAL't) :: [])) (fun str ->
         let (p0, loc0) = str in
         let (wide, chars) = p0 in
         ((Cabs.CONSTANT (CONST_STRING (wide, chars))), loc0))
     | Prod'primary_expression'1 ->
       Obj.magic box (Coq_primary_expression'nt, ((T CONSTANT't) :: []))
         (fun cst -> ((Cabs.CONSTANT (fst cst)), (snd cst)))
     | Prod'primary_expression'0 ->
       Obj.magic box (Coq_primary_expression'nt, ((T VAR_NAME't) :: []))
         (fun var -> ((VARIABLE (fst var)), (snd var)))
     | Prod'postfix_expression'12 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RPAREN't) :: ((T
         OTHER_NAME't) :: ((T COMMA't) :: ((NT Coq_type_name'nt) :: ((T
         LPAREN't) :: ((T BUILTIN_OFFSETOF't) :: [])))))))
         (fun _ mem0 _ typ _ loc0 -> ((Cabs.BUILTIN_OFFSETOF (typ,
         ((INFIELD_INIT (fst mem0)) :: []))), loc0))
     | Prod'postfix_expression'11 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RPAREN't) :: ((NT
         Coq_designator_list'nt) :: ((T OTHER_NAME't) :: ((T COMMA't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: ((T
         BUILTIN_OFFSETOF't) :: [])))))))) (fun _ mems id _ typ _ loc0 ->
         ((Cabs.BUILTIN_OFFSETOF (typ, ((INFIELD_INIT
         (fst id)) :: (rev mems)))), loc0))
     | Prod'postfix_expression'10 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RBRACE't) :: ((T
         COMMA't) :: ((NT Coq_initializer_list'nt) :: ((T LBRACE't) :: ((T
         RPAREN't) :: ((NT Coq_type_name'nt) :: ((T LPAREN't) :: []))))))))
         (fun _ _ init _ _ typ loc0 -> ((CAST (typ, (COMPOUND_INIT
         (rev' init)))), loc0))
     | Prod'postfix_expression'9 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RBRACE't) :: ((NT
         Coq_initializer_list'nt) :: ((T LBRACE't) :: ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: [])))))))
         (fun _ init _ _ typ loc0 -> ((CAST (typ, (COMPOUND_INIT
         (rev' init)))), loc0))
     | Prod'postfix_expression'8 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T DEC't) :: ((NT
         Coq_postfix_expression'nt) :: []))) (fun _ expr -> ((UNARY (POSDECR,
         (fst expr))), (snd expr)))
     | Prod'postfix_expression'7 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T INC't) :: ((NT
         Coq_postfix_expression'nt) :: []))) (fun _ expr -> ((UNARY (POSINCR,
         (fst expr))), (snd expr)))
     | Prod'postfix_expression'6 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T OTHER_NAME't) :: ((T
         PTR't) :: ((NT Coq_postfix_expression'nt) :: []))))
         (fun mem0 _ expr -> ((MEMBEROFPTR ((fst expr), (fst mem0))),
         (snd expr)))
     | Prod'postfix_expression'5 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T OTHER_NAME't) :: ((T
         DOT't) :: ((NT Coq_postfix_expression'nt) :: []))))
         (fun mem0 _ expr -> ((MEMBEROF ((fst expr), (fst mem0))),
         (snd expr)))
     | Prod'postfix_expression'4 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T COMMA't) :: ((NT
         Coq_assignment_expression'nt) :: ((T LPAREN't) :: ((T
         BUILTIN_VA_ARG't) :: []))))))) (fun _ ty _ expr _ loc0 ->
         ((Cabs.BUILTIN_VA_ARG ((fst expr), ty)), loc0))
     | Prod'postfix_expression'3 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RPAREN't) :: ((T
         LPAREN't) :: ((NT Coq_postfix_expression'nt) :: []))))
         (fun _ _ expr -> ((CALL ((fst expr), [])), (snd expr)))
     | Prod'postfix_expression'2 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RPAREN't) :: ((NT
         Coq_argument_expression_list'nt) :: ((T LPAREN't) :: ((NT
         Coq_postfix_expression'nt) :: []))))) (fun _ args _ expr -> ((CALL
         ((fst expr), (rev' args))), (snd expr)))
     | Prod'postfix_expression'1 ->
       Obj.magic box (Coq_postfix_expression'nt, ((T RBRACK't) :: ((NT
         Coq_expression'nt) :: ((T LBRACK't) :: ((NT
         Coq_postfix_expression'nt) :: []))))) (fun _ index _ expr -> ((INDEX
         ((fst expr), (fst index))), (snd expr)))
     | Prod'postfix_expression'0 ->
       Obj.magic box (Coq_postfix_expression'nt, ((NT
         Coq_primary_expression'nt) :: [])) (fun expr -> expr)
     | Prod'pointer'3 ->
       Obj.magic box (Coq_pointer'nt, ((NT Coq_pointer'nt) :: ((NT
         Coq_type_qualifier_list'nt) :: ((T STAR't) :: []))))
         (fun pt quallst loc0 -> ((fun typ -> Cabs.PTR ((rev' quallst),
         (fst pt typ))), loc0))
     | Prod'pointer'2 ->
       Obj.magic box (Coq_pointer'nt, ((NT Coq_pointer'nt) :: ((T
         STAR't) :: []))) (fun pt loc0 -> ((fun typ -> Cabs.PTR ([],
         (fst pt typ))), loc0))
     | Prod'pointer'1 ->
       Obj.magic box (Coq_pointer'nt, ((NT Coq_type_qualifier_list'nt) :: ((T
         STAR't) :: []))) (fun quallst loc0 -> ((fun typ -> Cabs.PTR
         ((rev' quallst), typ)), loc0))
     | Prod'pointer'0 ->
       Obj.magic box (Coq_pointer'nt, ((T STAR't) :: [])) (fun loc0 ->
         ((fun typ -> Cabs.PTR ([], typ)), loc0))
     | Prod'parameter_type_list'1 ->
       Obj.magic box (Coq_parameter_type_list'nt, ((T ELLIPSIS't) :: ((T
         COMMA't) :: ((NT Coq_parameter_list'nt) :: [])))) (fun _ _ lst ->
         ((rev' lst), true))
     | Prod'parameter_type_list'0 ->
       Obj.magic box (Coq_parameter_type_list'nt, ((NT
         Coq_parameter_list'nt) :: [])) (fun lst -> ((rev' lst), false))
     | Prod'parameter_list'1 ->
       Obj.magic box (Coq_parameter_list'nt, ((NT
         Coq_parameter_declaration'nt) :: ((T COMMA't) :: ((NT
         Coq_parameter_list'nt) :: [])))) (fun paramt _ paramq ->
         paramt :: paramq)
     | Prod'parameter_list'0 ->
       Obj.magic box (Coq_parameter_list'nt, ((NT
         Coq_parameter_declaration'nt) :: [])) (fun param -> param :: [])
     | Prod'parameter_declaration'2 ->
       Obj.magic box (Coq_parameter_declaration'nt, ((NT
         Coq_declaration_specifiers'nt) :: [])) (fun specs -> PARAM
         ((fst specs), None, JUSTBASE, [], (snd specs)))
     | Prod'parameter_declaration'1 ->
       Obj.magic box (Coq_parameter_declaration'nt, ((NT
         Coq_abstract_declarator'nt) :: ((NT
         Coq_declaration_specifiers'nt) :: []))) (fun decl specs -> PARAM
         ((fst specs), None, decl, [], (snd specs)))
     | Prod'parameter_declaration'0 ->
       Obj.magic box (Coq_parameter_declaration'nt, ((NT
         Coq_declarator'nt) :: ((NT Coq_declaration_specifiers'nt) :: [])))
         (fun decl specs ->
         let Name (name, typ, attr, _) = decl in
         PARAM ((fst specs), (Some name), typ, attr, (snd specs)))
     | Prod'multiplicative_expression'3 ->
       Obj.magic box (Coq_multiplicative_expression'nt, ((NT
         Coq_cast_expression'nt) :: ((T PERCENT't) :: ((NT
         Coq_multiplicative_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (MOD, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'multiplicative_expression'2 ->
       Obj.magic box (Coq_multiplicative_expression'nt, ((NT
         Coq_cast_expression'nt) :: ((T SLASH't) :: ((NT
         Coq_multiplicative_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (DIV, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'multiplicative_expression'1 ->
       Obj.magic box (Coq_multiplicative_expression'nt, ((NT
         Coq_cast_expression'nt) :: ((T STAR't) :: ((NT
         Coq_multiplicative_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (MUL, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'multiplicative_expression'0 ->
       Obj.magic box (Coq_multiplicative_expression'nt, ((NT
         Coq_cast_expression'nt) :: [])) (fun expr -> expr)
     | Prod'logical_OR_expression'1 ->
       Obj.magic box (Coq_logical_OR_expression'nt, ((NT
         Coq_logical_AND_expression'nt) :: ((T BARBAR't) :: ((NT
         Coq_logical_OR_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (OR, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'logical_OR_expression'0 ->
       Obj.magic box (Coq_logical_OR_expression'nt, ((NT
         Coq_logical_AND_expression'nt) :: [])) (fun expr -> expr)
     | Prod'logical_AND_expression'1 ->
       Obj.magic box (Coq_logical_AND_expression'nt, ((NT
         Coq_inclusive_OR_expression'nt) :: ((T ANDAND't) :: ((NT
         Coq_logical_AND_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (Cabs.AND, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'logical_AND_expression'0 ->
       Obj.magic box (Coq_logical_AND_expression'nt, ((NT
         Coq_inclusive_OR_expression'nt) :: [])) (fun expr -> expr)
     | Prod'labeled_statement_statement_safe_'2 ->
       Obj.magic box (Coq_labeled_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T COLON't) :: ((T DEFAULT't) :: []))))
         (fun stmt _ loc0 -> Cabs.DEFAULT (stmt, loc0))
     | Prod'labeled_statement_statement_safe_'1 ->
       Obj.magic box (Coq_labeled_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T COLON't) :: ((NT
         Coq_constant_expression'nt) :: ((T CASE't) :: [])))))
         (fun stmt _ expr loc0 -> Cabs.CASE ((fst expr), stmt, loc0))
     | Prod'labeled_statement_statement_safe_'0 ->
       Obj.magic box (Coq_labeled_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T COLON't) :: ((T
         OTHER_NAME't) :: [])))) (fun stmt _ lbl -> LABEL ((fst lbl), stmt,
         (snd lbl)))
     | Prod'labeled_statement_statement_dangerous_'2 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T COLON't) :: ((T
         DEFAULT't) :: [])))) (fun stmt _ loc0 -> Cabs.DEFAULT (stmt, loc0))
     | Prod'labeled_statement_statement_dangerous_'1 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T COLON't) :: ((NT
         Coq_constant_expression'nt) :: ((T CASE't) :: [])))))
         (fun stmt _ expr loc0 -> Cabs.CASE ((fst expr), stmt, loc0))
     | Prod'labeled_statement_statement_dangerous_'0 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T COLON't) :: ((T
         OTHER_NAME't) :: [])))) (fun stmt _ lbl -> LABEL ((fst lbl), stmt,
         (snd lbl)))
     | Prod'jump_statement'4 ->
       Obj.magic box (Coq_jump_statement'nt, ((T SEMICOLON't) :: ((T
         RETURN't) :: []))) (fun _ loc0 -> Cabs.RETURN (None, loc0))
     | Prod'jump_statement'3 ->
       Obj.magic box (Coq_jump_statement'nt, ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T RETURN't) :: [])))) (fun _ expr loc0 ->
         Cabs.RETURN ((Some (fst expr)), loc0))
     | Prod'jump_statement'2 ->
       Obj.magic box (Coq_jump_statement'nt, ((T SEMICOLON't) :: ((T
         BREAK't) :: []))) (fun _ loc0 -> Cabs.BREAK loc0)
     | Prod'jump_statement'1 ->
       Obj.magic box (Coq_jump_statement'nt, ((T SEMICOLON't) :: ((T
         CONTINUE't) :: []))) (fun _ loc0 -> Cabs.CONTINUE loc0)
     | Prod'jump_statement'0 ->
       Obj.magic box (Coq_jump_statement'nt, ((T SEMICOLON't) :: ((T
         OTHER_NAME't) :: ((T GOTO't) :: [])))) (fun _ id loc0 -> Cabs.GOTO
         ((fst id), loc0))
     | Prod'iteration_statement_statement_safe_'13 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((T
         SEMICOLON't) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))
         (fun stmt _ _ _ _ loc0 -> Cabs.FOR (None, None, None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'12 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((NT
         Coq_declaration'nt) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))
         (fun stmt _ _ decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL decl1)),
         None, None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'11 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((T
         SEMICOLON't) :: ((NT Coq_expression'nt) :: ((T LPAREN't) :: ((T
         FOR't) :: [])))))))) (fun stmt _ _ _ expr1 _ loc0 -> Cabs.FOR ((Some
         (FC_EXP (fst expr1))), None, None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'10 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T LPAREN't) :: ((T
         FOR't) :: [])))))))) (fun stmt _ _ expr2 _ _ loc0 -> Cabs.FOR (None,
         (Some (fst expr2)), None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'9 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((NT Coq_declaration'nt) :: ((T
         LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ _ expr2 decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'8 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ _ expr2 _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), None, stmt, loc0))
     | Prod'iteration_statement_statement_safe_'7 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T SEMICOLON't) :: ((T
         LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ expr3 _ _ _ loc0 -> Cabs.FOR (None, None, (Some
         (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'6 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_declaration'nt) :: ((T LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ expr3 _ decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), None, (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'5 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ expr3 _ _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), None, (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'4 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T LPAREN't) :: ((T
         FOR't) :: []))))))))) (fun stmt _ expr3 _ expr2 _ _ loc0 -> Cabs.FOR
         (None, (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'3 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((NT Coq_declaration'nt) :: ((T
         LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ expr3 _ expr2 decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'2 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: []))))))))))
         (fun stmt _ expr3 _ expr2 _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'1 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((T
         SEMICOLON't) :: ((T RPAREN't) :: ((NT Coq_expression'nt) :: ((T
         LPAREN't) :: ((T WHILE't) :: ((NT Coq_statement_dangerous'nt) :: ((T
         DO't) :: [])))))))) (fun _ _ expr _ _ stmt loc0 -> DOWHILE
         ((fst expr), stmt, loc0))
     | Prod'iteration_statement_statement_safe_'0 ->
       Obj.magic box (Coq_iteration_statement_statement_safe_'nt, ((NT
         Coq_statement_safe'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T WHILE't) :: []))))))
         (fun stmt _ expr _ loc0 -> Cabs.WHILE ((fst expr), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'13 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((T SEMICOLON't) :: ((T LPAREN't) :: ((T
         FOR't) :: []))))))) (fun stmt _ _ _ _ loc0 -> Cabs.FOR (None, None,
         None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'12 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((NT Coq_declaration'nt) :: ((T LPAREN't) :: ((T
         FOR't) :: []))))))) (fun stmt _ _ decl1 _ loc0 -> Cabs.FOR ((Some
         (FC_DECL decl1)), None, None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'11 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((T SEMICOLON't) :: ((NT Coq_expression'nt) :: ((T
         LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ _ _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), None, None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'10 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((NT Coq_expression'nt) :: ((T SEMICOLON't) :: ((T
         LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ _ expr2 _ _ loc0 -> Cabs.FOR (None, (Some (fst expr2)),
         None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'9 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((NT Coq_expression'nt) :: ((NT
         Coq_declaration'nt) :: ((T LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ _ expr2 decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'8 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((T
         SEMICOLON't) :: ((NT Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ _ expr2 _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), None, stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'7 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T SEMICOLON't) :: ((T
         LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ expr3 _ _ _ loc0 -> Cabs.FOR (None, None, (Some
         (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'6 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_declaration'nt) :: ((T LPAREN't) :: ((T FOR't) :: []))))))))
         (fun stmt _ expr3 _ decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), None, (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'5 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ expr3 _ _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), None, (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'4 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((T LPAREN't) :: ((T
         FOR't) :: []))))))))) (fun stmt _ expr3 _ expr2 _ _ loc0 -> Cabs.FOR
         (None, (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'3 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((NT Coq_declaration'nt) :: ((T
         LPAREN't) :: ((T FOR't) :: [])))))))))
         (fun stmt _ expr3 _ expr2 decl1 _ loc0 -> Cabs.FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'2 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T FOR't) :: []))))))))))
         (fun stmt _ expr3 _ expr2 _ expr1 _ loc0 -> Cabs.FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), (Some (fst expr3)), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'1 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((T
         SEMICOLON't) :: ((T RPAREN't) :: ((NT Coq_expression'nt) :: ((T
         LPAREN't) :: ((T WHILE't) :: ((NT Coq_statement_dangerous'nt) :: ((T
         DO't) :: [])))))))) (fun _ _ expr _ _ stmt loc0 -> DOWHILE
         ((fst expr), stmt, loc0))
     | Prod'iteration_statement_statement_dangerous_'0 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous_'nt, ((NT
         Coq_statement_dangerous'nt) :: ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T WHILE't) :: []))))))
         (fun stmt _ expr _ loc0 -> Cabs.WHILE ((fst expr), stmt, loc0))
     | Prod'initializer_list'3 ->
       Obj.magic box (Coq_initializer_list'nt, ((NT
         Coq_c_initializer'nt) :: ((T COMMA't) :: ((NT
         Coq_initializer_list'nt) :: [])))) (fun init _ initq -> ([],
         init) :: initq)
     | Prod'initializer_list'2 ->
       Obj.magic box (Coq_initializer_list'nt, ((NT
         Coq_c_initializer'nt) :: ((NT Coq_designation'nt) :: ((T
         COMMA't) :: ((NT Coq_initializer_list'nt) :: [])))))
         (fun init design _ initq -> (design, init) :: initq)
     | Prod'initializer_list'1 ->
       Obj.magic box (Coq_initializer_list'nt, ((NT
         Coq_c_initializer'nt) :: [])) (fun init -> ([], init) :: [])
     | Prod'initializer_list'0 ->
       Obj.magic box (Coq_initializer_list'nt, ((NT
         Coq_c_initializer'nt) :: ((NT Coq_designation'nt) :: [])))
         (fun init design -> (design, init) :: [])
     | Prod'init_declarator_list'1 ->
       Obj.magic box (Coq_init_declarator_list'nt, ((NT
         Coq_init_declarator'nt) :: ((T COMMA't) :: ((NT
         Coq_init_declarator_list'nt) :: [])))) (fun initt _ initq ->
         initt :: initq)
     | Prod'init_declarator_list'0 ->
       Obj.magic box (Coq_init_declarator_list'nt, ((NT
         Coq_init_declarator'nt) :: [])) (fun init -> init :: [])
     | Prod'init_declarator'1 ->
       Obj.magic box (Coq_init_declarator'nt, ((NT
         Coq_c_initializer'nt) :: ((T EQ't) :: ((NT
         Coq_declarator'nt) :: [])))) (fun init _ name -> Init_name (name,
         init))
     | Prod'init_declarator'0 ->
       Obj.magic box (Coq_init_declarator'nt, ((NT Coq_declarator'nt) :: []))
         (fun name -> Init_name (name, NO_INIT))
     | Prod'inclusive_OR_expression'1 ->
       Obj.magic box (Coq_inclusive_OR_expression'nt, ((NT
         Coq_exclusive_OR_expression'nt) :: ((T BAR't) :: ((NT
         Coq_inclusive_OR_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (BOR, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'inclusive_OR_expression'0 ->
       Obj.magic box (Coq_inclusive_OR_expression'nt, ((NT
         Coq_exclusive_OR_expression'nt) :: [])) (fun expr -> expr)
     | Prod'identifier_list'1 ->
       Obj.magic box (Coq_identifier_list'nt, ((T VAR_NAME't) :: ((T
         COMMA't) :: ((NT Coq_identifier_list'nt) :: [])))) (fun id _ idl ->
         (fst id) :: idl)
     | Prod'identifier_list'0 ->
       Obj.magic box (Coq_identifier_list'nt, ((T VAR_NAME't) :: []))
         (fun id -> (fst id) :: [])
     | Prod'gcc_attribute_word'2 ->
       Obj.magic box (Coq_gcc_attribute_word'nt, ((T PACKED't) :: []))
         (fun _ -> GCC_ATTR_PACKED)
     | Prod'gcc_attribute_word'1 ->
       Obj.magic box (Coq_gcc_attribute_word'nt, ((T CONST't) :: []))
         (fun _ -> GCC_ATTR_CONST)
     | Prod'gcc_attribute_word'0 ->
       Obj.magic box (Coq_gcc_attribute_word'nt, ((T OTHER_NAME't) :: []))
         (fun i -> GCC_ATTR_IDENT (fst i))
     | Prod'gcc_attribute_list'1 ->
       Obj.magic box (Coq_gcc_attribute_list'nt, ((NT
         Coq_gcc_attribute'nt) :: ((T COMMA't) :: ((NT
         Coq_gcc_attribute_list'nt) :: [])))) (fun t0 _ q -> t0 :: q)
     | Prod'gcc_attribute_list'0 ->
       Obj.magic box (Coq_gcc_attribute_list'nt, ((NT
         Coq_gcc_attribute'nt) :: [])) (fun a -> a :: [])
     | Prod'gcc_attribute'3 ->
       Obj.magic box (Coq_gcc_attribute'nt, ((T RPAREN't) :: ((NT
         Coq_argument_expression_list'nt) :: ((T LPAREN't) :: ((NT
         Coq_gcc_attribute_word'nt) :: []))))) (fun _ args _ w ->
         GCC_ATTR_ARGS (w, (rev' args)))
     | Prod'gcc_attribute'2 ->
       Obj.magic box (Coq_gcc_attribute'nt, ((T RPAREN't) :: ((T
         LPAREN't) :: ((NT Coq_gcc_attribute_word'nt) :: [])))) (fun _ _ w ->
         GCC_ATTR_ARGS (w, []))
     | Prod'gcc_attribute'1 ->
       Obj.magic box (Coq_gcc_attribute'nt, ((NT
         Coq_gcc_attribute_word'nt) :: [])) (fun w -> GCC_ATTR_NOARGS w)
     | Prod'gcc_attribute'0 ->
       Obj.magic box (Coq_gcc_attribute'nt, []) GCC_ATTR_EMPTY
     | Prod'function_specifier'1 ->
       Obj.magic box (Coq_function_specifier'nt, ((T NORETURN't) :: []))
         (fun loc0 -> (Cabs.NORETURN, loc0))
     | Prod'function_specifier'0 ->
       Obj.magic box (Coq_function_specifier'nt, ((T INLINE't) :: []))
         (fun loc0 -> (Cabs.INLINE, loc0))
     | Prod'function_definition'1 ->
       Obj.magic box (Coq_function_definition'nt, ((NT
         Coq_compound_statement'nt) :: ((NT Coq_declarator'nt) :: ((NT
         Coq_declaration_specifiers'nt) :: [])))) (fun stmt decl specs ->
         FUNDEF ((fst specs), decl, [], stmt, (snd specs)))
     | Prod'function_definition'0 ->
       Obj.magic box (Coq_function_definition'nt, ((NT
         Coq_compound_statement'nt) :: ((NT Coq_declaration_list'nt) :: ((NT
         Coq_declarator_noattrend'nt) :: ((NT
         Coq_declaration_specifiers'nt) :: [])))))
         (fun stmt dlist decl specs -> FUNDEF ((fst specs), decl,
         (rev' dlist), stmt, (snd specs)))
     | Prod'external_declaration'2 ->
       Obj.magic box (Coq_external_declaration'nt, ((T PRAGMA't) :: []))
         (fun p0 -> Cabs.PRAGMA ((fst p0), (snd p0)))
     | Prod'external_declaration'1 ->
       Obj.magic box (Coq_external_declaration'nt, ((NT
         Coq_declaration'nt) :: [])) (fun def -> def)
     | Prod'external_declaration'0 ->
       Obj.magic box (Coq_external_declaration'nt, ((NT
         Coq_function_definition'nt) :: [])) (fun def -> def)
     | Prod'expression_statement'1 ->
       Obj.magic box (Coq_expression_statement'nt, ((T SEMICOLON't) :: []))
         (fun loc0 -> NOP loc0)
     | Prod'expression_statement'0 ->
       Obj.magic box (Coq_expression_statement'nt, ((T SEMICOLON't) :: ((NT
         Coq_expression'nt) :: []))) (fun _ expr -> COMPUTATION ((fst expr),
         (snd expr)))
     | Prod'expression'1 ->
       Obj.magic box (Coq_expression'nt, ((NT
         Coq_assignment_expression'nt) :: ((T COMMA't) :: ((NT
         Coq_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (Cabs.COMMA, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'expression'0 ->
       Obj.magic box (Coq_expression'nt, ((NT
         Coq_assignment_expression'nt) :: [])) (fun expr -> expr)
     | Prod'exclusive_OR_expression'1 ->
       Obj.magic box (Coq_exclusive_OR_expression'nt, ((NT
         AND_expression'nt) :: ((T HAT't) :: ((NT
         Coq_exclusive_OR_expression'nt) :: [])))) (fun expr2 _ expr1 ->
         ((BINARY (XOR, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'exclusive_OR_expression'0 ->
       Obj.magic box (Coq_exclusive_OR_expression'nt, ((NT
         AND_expression'nt) :: [])) (fun expr -> expr)
     | Prod'equality_expression'2 ->
       Obj.magic box (Coq_equality_expression'nt, ((NT
         Coq_relational_expression'nt) :: ((T NEQ't) :: ((NT
         Coq_equality_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (NE, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'equality_expression'1 ->
       Obj.magic box (Coq_equality_expression'nt, ((NT
         Coq_relational_expression'nt) :: ((T EQEQ't) :: ((NT
         Coq_equality_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (Cabs.EQ, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'equality_expression'0 ->
       Obj.magic box (Coq_equality_expression'nt, ((NT
         Coq_relational_expression'nt) :: [])) (fun expr -> expr)
     | Prod'enumerator_list'1 ->
       Obj.magic box (Coq_enumerator_list'nt, ((NT Coq_enumerator'nt) :: ((T
         COMMA't) :: ((NT Coq_enumerator_list'nt) :: []))))
         (fun enumst _ enumsq -> enumst :: enumsq)
     | Prod'enumerator_list'0 ->
       Obj.magic box (Coq_enumerator_list'nt, ((NT Coq_enumerator'nt) :: []))
         (fun enum -> enum :: [])
     | Prod'enumerator'1 ->
       Obj.magic box (Coq_enumerator'nt, ((NT
         Coq_constant_expression'nt) :: ((T EQ't) :: ((NT
         Coq_enumeration_constant'nt) :: [])))) (fun expr _ cst ->
         (((fst cst), (Some (fst expr))), (snd cst)))
     | Prod'enumerator'0 ->
       Obj.magic box (Coq_enumerator'nt, ((NT
         Coq_enumeration_constant'nt) :: [])) (fun cst -> (((fst cst), None),
         (snd cst)))
     | Prod'enumeration_constant'0 ->
       Obj.magic box (Coq_enumeration_constant'nt, ((T VAR_NAME't) :: []))
         (fun cst -> cst)
     | Prod'enum_specifier'4 ->
       Obj.magic box (Coq_enum_specifier'nt, ((T OTHER_NAME't) :: ((NT
         Coq_attribute_specifier_list'nt) :: ((T ENUM't) :: []))))
         (fun name attrs loc0 -> ((Tenum ((Some (fst name)), None, attrs)),
         loc0))
     | Prod'enum_specifier'3 ->
       Obj.magic box (Coq_enum_specifier'nt, ((T RBRACE't) :: ((T
         COMMA't) :: ((NT Coq_enumerator_list'nt) :: ((T LBRACE't) :: ((NT
         Coq_attribute_specifier_list'nt) :: ((T ENUM't) :: [])))))))
         (fun _ _ enum_list _ attrs loc0 -> ((Tenum (None, (Some
         (rev' enum_list)), attrs)), loc0))
     | Prod'enum_specifier'2 ->
       Obj.magic box (Coq_enum_specifier'nt, ((T RBRACE't) :: ((T
         COMMA't) :: ((NT Coq_enumerator_list'nt) :: ((T LBRACE't) :: ((T
         OTHER_NAME't) :: ((NT Coq_attribute_specifier_list'nt) :: ((T
         ENUM't) :: [])))))))) (fun _ _ enum_list _ name attrs loc0 ->
         ((Tenum ((Some (fst name)), (Some (rev' enum_list)), attrs)), loc0))
     | Prod'enum_specifier'1 ->
       Obj.magic box (Coq_enum_specifier'nt, ((T RBRACE't) :: ((NT
         Coq_enumerator_list'nt) :: ((T LBRACE't) :: ((NT
         Coq_attribute_specifier_list'nt) :: ((T ENUM't) :: []))))))
         (fun _ enum_list _ attrs loc0 -> ((Tenum (None, (Some
         (rev' enum_list)), attrs)), loc0))
     | Prod'enum_specifier'0 ->
       Obj.magic box (Coq_enum_specifier'nt, ((T RBRACE't) :: ((NT
         Coq_enumerator_list'nt) :: ((T LBRACE't) :: ((T
         OTHER_NAME't) :: ((NT Coq_attribute_specifier_list'nt) :: ((T
         ENUM't) :: []))))))) (fun _ enum_list _ name attrs loc0 -> ((Tenum
         ((Some (fst name)), (Some (rev' enum_list)), attrs)), loc0))
     | Prod'direct_declarator'8 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RPAREN't) :: ((NT
         Coq_identifier_list'nt) :: ((T LPAREN't) :: ((NT
         Coq_direct_declarator'nt) :: []))))) (fun _ params _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (PROTO_OLD (typ, (rev' params))), attr, loc0))
     | Prod'direct_declarator'7 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RPAREN't) :: ((T
         LPAREN't) :: ((NT Coq_direct_declarator'nt) :: []))))
         (fun _ _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (PROTO_OLD (typ, [])), attr, loc0))
     | Prod'direct_declarator'6 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RPAREN't) :: ((NT
         Coq_parameter_type_list'nt) :: ((T LPAREN't) :: ((NT
         Coq_direct_declarator'nt) :: []))))) (fun _ params _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (PROTO (typ, params)), attr, loc0))
     | Prod'direct_declarator'5 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RBRACK't) :: ((T
         LBRACK't) :: ((NT Coq_direct_declarator'nt) :: []))))
         (fun _ _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (ARRAY (typ, [], None)), attr, loc0))
     | Prod'direct_declarator'4 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RBRACK't) :: ((NT
         Coq_type_qualifier_list'nt) :: ((T LBRACK't) :: ((NT
         Coq_direct_declarator'nt) :: []))))) (fun _ quallst _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (ARRAY (typ, (rev' quallst), None)), attr, loc0))
     | Prod'direct_declarator'3 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RBRACK't) :: ((NT
         Coq_assignment_expression'nt) :: ((T LBRACK't) :: ((NT
         Coq_direct_declarator'nt) :: []))))) (fun _ expr _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (ARRAY (typ, [], (Some (fst expr)))), attr, loc0))
     | Prod'direct_declarator'2 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RBRACK't) :: ((NT
         Coq_assignment_expression'nt) :: ((NT
         Coq_type_qualifier_list'nt) :: ((T LBRACK't) :: ((NT
         Coq_direct_declarator'nt) :: [])))))) (fun _ expr quallst _ decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, (ARRAY (typ, (rev' quallst), (Some (fst expr)))), attr,
         loc0))
     | Prod'direct_declarator'1 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T RPAREN't) :: ((NT
         Coq_declarator'nt) :: ((T LPAREN't) :: [])))) (fun _ decl _ -> decl)
     | Prod'direct_declarator'0 ->
       Obj.magic box (Coq_direct_declarator'nt, ((T VAR_NAME't) :: []))
         (fun id -> Name ((fst id), JUSTBASE, [], (snd id)))
     | Prod'direct_abstract_declarator'12 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T RPAREN't) :: ((T
         LPAREN't) :: []))) (fun _ _ -> PROTO (JUSTBASE, ([], false)))
     | Prod'direct_abstract_declarator'11 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T RPAREN't) :: ((T
         LPAREN't) :: ((NT Coq_direct_abstract_declarator'nt) :: []))))
         (fun _ _ typ -> PROTO (typ, ([], false)))
     | Prod'direct_abstract_declarator'10 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RPAREN't) :: ((NT Coq_parameter_type_list'nt) :: ((T
         LPAREN't) :: [])))) (fun _ params _ -> PROTO (JUSTBASE, params))
     | Prod'direct_abstract_declarator'9 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RPAREN't) :: ((NT Coq_parameter_type_list'nt) :: ((T
         LPAREN't) :: ((NT Coq_direct_abstract_declarator'nt) :: [])))))
         (fun _ params _ typ -> PROTO (typ, params))
     | Prod'direct_abstract_declarator'8 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T RBRACK't) :: ((T
         LBRACK't) :: []))) (fun _ _ -> ARRAY (JUSTBASE, [], None))
     | Prod'direct_abstract_declarator'7 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T RBRACK't) :: ((T
         LBRACK't) :: ((NT Coq_direct_abstract_declarator'nt) :: []))))
         (fun _ _ typ -> ARRAY (typ, [], None))
     | Prod'direct_abstract_declarator'6 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_type_qualifier_list'nt) :: ((T
         LBRACK't) :: [])))) (fun _ cvspec _ -> ARRAY (JUSTBASE, cvspec,
         None))
     | Prod'direct_abstract_declarator'5 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_type_qualifier_list'nt) :: ((T
         LBRACK't) :: ((NT Coq_direct_abstract_declarator'nt) :: [])))))
         (fun _ cvspec _ typ -> ARRAY (typ, cvspec, None))
     | Prod'direct_abstract_declarator'4 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_assignment_expression'nt) :: ((T
         LBRACK't) :: [])))) (fun _ expr _ -> ARRAY (JUSTBASE, [], (Some
         (fst expr))))
     | Prod'direct_abstract_declarator'3 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_assignment_expression'nt) :: ((T
         LBRACK't) :: ((NT Coq_direct_abstract_declarator'nt) :: [])))))
         (fun _ expr _ typ -> ARRAY (typ, [], (Some (fst expr))))
     | Prod'direct_abstract_declarator'2 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_assignment_expression'nt) :: ((NT
         Coq_type_qualifier_list'nt) :: ((T LBRACK't) :: [])))))
         (fun _ expr cvspec _ -> ARRAY (JUSTBASE, cvspec, (Some (fst expr))))
     | Prod'direct_abstract_declarator'1 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RBRACK't) :: ((NT Coq_assignment_expression'nt) :: ((NT
         Coq_type_qualifier_list'nt) :: ((T LBRACK't) :: ((NT
         Coq_direct_abstract_declarator'nt) :: []))))))
         (fun _ expr cvspec _ typ -> ARRAY (typ, cvspec, (Some (fst expr))))
     | Prod'direct_abstract_declarator'0 ->
       Obj.magic box (Coq_direct_abstract_declarator'nt, ((T
         RPAREN't) :: ((NT Coq_abstract_declarator'nt) :: ((T
         LPAREN't) :: [])))) (fun _ typ _ -> typ)
     | Prod'designator_list'1 ->
       Obj.magic box (Coq_designator_list'nt, ((NT Coq_designator'nt) :: ((NT
         Coq_designator_list'nt) :: []))) (fun designt designq ->
         designt :: designq)
     | Prod'designator_list'0 ->
       Obj.magic box (Coq_designator_list'nt, ((NT Coq_designator'nt) :: []))
         (fun design -> design :: [])
     | Prod'designator'1 ->
       Obj.magic box (Coq_designator'nt, ((T OTHER_NAME't) :: ((T
         DOT't) :: []))) (fun id _ -> INFIELD_INIT (fst id))
     | Prod'designator'0 ->
       Obj.magic box (Coq_designator'nt, ((T RBRACK't) :: ((NT
         Coq_constant_expression'nt) :: ((T LBRACK't) :: []))))
         (fun _ expr _ -> ATINDEX_INIT (fst expr))
     | Prod'designation'0 ->
       Obj.magic box (Coq_designation'nt, ((T EQ't) :: ((NT
         Coq_designator_list'nt) :: []))) (fun _ -> rev')
     | Prod'declarator_noattrend'1 ->
       Obj.magic box (Coq_declarator_noattrend'nt, ((NT
         Coq_direct_declarator'nt) :: ((NT Coq_pointer'nt) :: [])))
         (fun decl pt ->
         let Name (name, typ, attr, _) = decl in
         Name (name, (fst pt typ), attr, (snd pt)))
     | Prod'declarator_noattrend'0 ->
       Obj.magic box (Coq_declarator_noattrend'nt, ((NT
         Coq_direct_declarator'nt) :: [])) (fun decl -> decl)
     | Prod'declarator'0 ->
       Obj.magic box (Coq_declarator'nt, ((NT
         Coq_attribute_specifier_list'nt) :: ((NT
         Coq_declarator_noattrend'nt) :: []))) (fun attrs decl ->
         let Name (name, typ, attr, loc0) = decl in
         Name (name, typ, (app attr attrs), loc0))
     | Prod'declaration_specifiers_typespec_opt'4 ->
       Obj.magic box (Coq_declaration_specifiers_typespec_opt'nt, []) []
     | Prod'declaration_specifiers_typespec_opt'3 ->
       Obj.magic box (Coq_declaration_specifiers_typespec_opt'nt, ((NT
         Coq_declaration_specifiers_typespec_opt'nt) :: ((NT
         Coq_function_specifier'nt) :: []))) (fun rest func -> (SpecFunction
         (fst func)) :: rest)
     | Prod'declaration_specifiers_typespec_opt'2 ->
       Obj.magic box (Coq_declaration_specifiers_typespec_opt'nt, ((NT
         Coq_declaration_specifiers_typespec_opt'nt) :: ((NT
         Coq_type_qualifier'nt) :: []))) (fun rest qual -> (SpecCV
         (fst qual)) :: rest)
     | Prod'declaration_specifiers_typespec_opt'1 ->
       Obj.magic box (Coq_declaration_specifiers_typespec_opt'nt, ((NT
         Coq_declaration_specifiers_typespec_opt'nt) :: ((NT
         Coq_type_specifier'nt) :: []))) (fun rest typ -> (SpecType
         (fst typ)) :: rest)
     | Prod'declaration_specifiers_typespec_opt'0 ->
       Obj.magic box (Coq_declaration_specifiers_typespec_opt'nt, ((NT
         Coq_declaration_specifiers_typespec_opt'nt) :: ((NT
         Coq_storage_class_specifier'nt) :: []))) (fun rest storage ->
         (SpecStorage (fst storage)) :: rest)
     | Prod'declaration_specifiers'4 ->
       Obj.magic box (Coq_declaration_specifiers'nt, ((NT
         Coq_declaration_specifiers'nt) :: ((NT
         Coq_function_specifier'nt) :: []))) (fun rest func ->
         (((SpecFunction (fst func)) :: (fst rest)), (snd func)))
     | Prod'declaration_specifiers'3 ->
       Obj.magic box (Coq_declaration_specifiers'nt, ((NT
         Coq_declaration_specifiers'nt) :: ((NT
         Coq_attribute_specifier'nt) :: []))) (fun rest attr -> (((SpecCV
         (CV_ATTR (fst attr))) :: (fst rest)), (snd attr)))
     | Prod'declaration_specifiers'2 ->
       Obj.magic box (Coq_declaration_specifiers'nt, ((NT
         Coq_declaration_specifiers'nt) :: ((NT
         Coq_type_qualifier_noattr'nt) :: []))) (fun rest qual -> (((SpecCV
         (fst qual)) :: (fst rest)), (snd qual)))
     | Prod'declaration_specifiers'1 ->
       Obj.magic box (Coq_declaration_specifiers'nt, ((NT
         Coq_declaration_specifiers_typespec_opt'nt) :: ((NT
         Coq_type_specifier'nt) :: []))) (fun rest typ -> (((SpecType
         (fst typ)) :: rest), (snd typ)))
     | Prod'declaration_specifiers'0 ->
       Obj.magic box (Coq_declaration_specifiers'nt, ((NT
         Coq_declaration_specifiers'nt) :: ((NT
         Coq_storage_class_specifier'nt) :: []))) (fun rest storage ->
         (((SpecStorage (fst storage)) :: (fst rest)), (snd storage)))
     | Prod'declaration_list'1 ->
       Obj.magic box (Coq_declaration_list'nt, ((NT
         Coq_declaration'nt) :: ((NT Coq_declaration_list'nt) :: [])))
         (fun d dl -> d :: dl)
     | Prod'declaration_list'0 ->
       Obj.magic box (Coq_declaration_list'nt, ((NT
         Coq_declaration'nt) :: [])) (fun d -> d :: [])
     | Prod'declaration'1 ->
       Obj.magic box (Coq_declaration'nt, ((T SEMICOLON't) :: ((NT
         Coq_declaration_specifiers'nt) :: []))) (fun _ decspec -> DECDEF
         (((fst decspec), []), (snd decspec)))
     | Prod'declaration'0 ->
       Obj.magic box (Coq_declaration'nt, ((T SEMICOLON't) :: ((NT
         Coq_init_declarator_list'nt) :: ((NT
         Coq_declaration_specifiers'nt) :: [])))) (fun _ decls decspec ->
         DECDEF (((fst decspec), (rev' decls)), (snd decspec)))
     | Prod'constant_expression'0 ->
       Obj.magic box (Coq_constant_expression'nt, ((NT
         Coq_conditional_expression'nt) :: [])) (fun expr -> expr)
     | Prod'conditional_expression'1 ->
       Obj.magic box (Coq_conditional_expression'nt, ((NT
         Coq_conditional_expression'nt) :: ((T COLON't) :: ((NT
         Coq_expression'nt) :: ((T QUESTION't) :: ((NT
         Coq_logical_OR_expression'nt) :: []))))))
         (fun expr3 _ expr2 _ expr1 -> ((Cabs.QUESTION ((fst expr1),
         (fst expr2), (fst expr3))), (snd expr1)))
     | Prod'conditional_expression'0 ->
       Obj.magic box (Coq_conditional_expression'nt, ((NT
         Coq_logical_OR_expression'nt) :: [])) (fun expr -> expr)
     | Prod'compound_statement'1 ->
       Obj.magic box (Coq_compound_statement'nt, ((T RBRACE't) :: ((T
         LBRACE't) :: []))) (fun _ loc0 -> BLOCK ([], loc0))
     | Prod'compound_statement'0 ->
       Obj.magic box (Coq_compound_statement'nt, ((T RBRACE't) :: ((NT
         Coq_block_item_list'nt) :: ((T LBRACE't) :: []))))
         (fun _ lst loc0 -> BLOCK ((rev' lst), loc0))
     | Prod'cast_expression'1 ->
       Obj.magic box (Coq_cast_expression'nt, ((NT
         Coq_cast_expression'nt) :: ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: [])))))
         (fun expr _ typ loc0 -> ((CAST (typ, (SINGLE_INIT (fst expr)))),
         loc0))
     | Prod'cast_expression'0 ->
       Obj.magic box (Coq_cast_expression'nt, ((NT
         Coq_unary_expression'nt) :: [])) (fun expr -> expr)
     | Prod'c_initializer'2 ->
       Obj.magic box (Coq_c_initializer'nt, ((T RBRACE't) :: ((T
         COMMA't) :: ((NT Coq_initializer_list'nt) :: ((T
         LBRACE't) :: []))))) (fun _ _ init _ -> COMPOUND_INIT (rev' init))
     | Prod'c_initializer'1 ->
       Obj.magic box (Coq_c_initializer'nt, ((T RBRACE't) :: ((NT
         Coq_initializer_list'nt) :: ((T LBRACE't) :: [])))) (fun _ init _ ->
         COMPOUND_INIT (rev' init))
     | Prod'c_initializer'0 ->
       Obj.magic box (Coq_c_initializer'nt, ((NT
         Coq_assignment_expression'nt) :: [])) (fun expr -> SINGLE_INIT
         (fst expr))
     | Prod'block_item_list'1 ->
       Obj.magic box (Coq_block_item_list'nt, ((NT Coq_block_item'nt) :: ((NT
         Coq_block_item_list'nt) :: []))) (fun stmtt stmtq -> stmtt :: stmtq)
     | Prod'block_item_list'0 ->
       Obj.magic box (Coq_block_item_list'nt, ((NT Coq_block_item'nt) :: []))
         (fun stmt -> stmt :: [])
     | Prod'block_item'2 ->
       Obj.magic box (Coq_block_item'nt, ((T PRAGMA't) :: [])) (fun p0 ->
         DEFINITION (Cabs.PRAGMA ((fst p0), (snd p0))))
     | Prod'block_item'1 ->
       Obj.magic box (Coq_block_item'nt, ((NT
         Coq_statement_dangerous'nt) :: [])) (fun stmt -> stmt)
     | Prod'block_item'0 ->
       Obj.magic box (Coq_block_item'nt, ((NT Coq_declaration'nt) :: []))
         (fun decl -> DEFINITION decl)
     | Prod'attribute_specifier_list'1 ->
       Obj.magic box (Coq_attribute_specifier_list'nt, ((NT
         Coq_attribute_specifier_list'nt) :: ((NT
         Coq_attribute_specifier'nt) :: []))) (fun attrs attr ->
         (fst attr) :: attrs)
     | Prod'attribute_specifier_list'0 ->
       Obj.magic box (Coq_attribute_specifier_list'nt, []) []
     | Prod'attribute_specifier'3 ->
       Obj.magic box (Coq_attribute_specifier'nt, ((T RPAREN't) :: ((NT
         Coq_type_name'nt) :: ((T LPAREN't) :: ((T ALIGNAS't) :: [])))))
         (fun _ typ _ loc0 -> ((ALIGNAS_ATTR (((Cabs.ALIGNOF typ) :: []),
         loc0)), loc0))
     | Prod'attribute_specifier'2 ->
       Obj.magic box (Coq_attribute_specifier'nt, ((T RPAREN't) :: ((NT
         Coq_argument_expression_list'nt) :: ((T LPAREN't) :: ((T
         ALIGNAS't) :: []))))) (fun _ args _ loc0 -> ((ALIGNAS_ATTR
         ((rev' args), loc0)), loc0))
     | Prod'attribute_specifier'1 ->
       Obj.magic box (Coq_attribute_specifier'nt, ((T RPAREN't) :: ((NT
         Coq_argument_expression_list'nt) :: ((T LPAREN't) :: ((T
         PACKED't) :: []))))) (fun _ args _ loc0 -> ((PACKED_ATTR
         ((rev' args), loc0)), loc0))
     | Prod'attribute_specifier'0 ->
       Obj.magic box (Coq_attribute_specifier'nt, ((T RPAREN't) :: ((T
         RPAREN't) :: ((NT Coq_gcc_attribute_list'nt) :: ((T LPAREN't) :: ((T
         LPAREN't) :: ((T ATTRIBUTE't) :: []))))))) (fun _ _ attr _ _ loc0 ->
         ((GCC_ATTR ((rev' attr), loc0)), loc0))
     | Prod'assignment_operator'10 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T AND_ASSIGN't) :: []))
         (fun _ -> BAND_ASSIGN)
     | Prod'assignment_operator'9 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T OR_ASSIGN't) :: []))
         (fun _ -> BOR_ASSIGN)
     | Prod'assignment_operator'8 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T XOR_ASSIGN't) :: []))
         (fun _ -> Cabs.XOR_ASSIGN)
     | Prod'assignment_operator'7 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T RIGHT_ASSIGN't) :: []))
         (fun _ -> SHR_ASSIGN)
     | Prod'assignment_operator'6 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T LEFT_ASSIGN't) :: []))
         (fun _ -> SHL_ASSIGN)
     | Prod'assignment_operator'5 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T SUB_ASSIGN't) :: []))
         (fun _ -> Cabs.SUB_ASSIGN)
     | Prod'assignment_operator'4 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T ADD_ASSIGN't) :: []))
         (fun _ -> Cabs.ADD_ASSIGN)
     | Prod'assignment_operator'3 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T MOD_ASSIGN't) :: []))
         (fun _ -> Cabs.MOD_ASSIGN)
     | Prod'assignment_operator'2 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T DIV_ASSIGN't) :: []))
         (fun _ -> Cabs.DIV_ASSIGN)
     | Prod'assignment_operator'1 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T MUL_ASSIGN't) :: []))
         (fun _ -> Cabs.MUL_ASSIGN)
     | Prod'assignment_operator'0 ->
       Obj.magic box (Coq_assignment_operator'nt, ((T EQ't) :: [])) (fun _ ->
         ASSIGN)
     | Prod'assignment_expression'1 ->
       Obj.magic box (Coq_assignment_expression'nt, ((NT
         Coq_assignment_expression'nt) :: ((NT
         Coq_assignment_operator'nt) :: ((NT
         Coq_unary_expression'nt) :: [])))) (fun expr2 op expr1 -> ((BINARY
         (op, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'assignment_expression'0 ->
       Obj.magic box (Coq_assignment_expression'nt, ((NT
         Coq_conditional_expression'nt) :: [])) (fun expr -> expr)
     | Prod'asm_statement'0 ->
       Obj.magic box (Coq_asm_statement'nt, ((T SEMICOLON't) :: ((T
         RPAREN't) :: ((NT Coq_asm_arguments'nt) :: ((T
         STRING_LITERAL't) :: ((T LPAREN't) :: ((NT
         Coq_asm_attributes'nt) :: ((T ASM't) :: []))))))))
         (fun _ _ args template _ attr loc0 ->
         let (p0, _) = template in
         let (wide, chars) = p0 in
         let (p1, flags) = args in
         let (outputs, inputs) = p1 in
         Cabs.ASM (attr, wide, chars, outputs, inputs, flags, loc0))
     | Prod'asm_operands_ne'1 ->
       Obj.magic box (Coq_asm_operands_ne'nt, ((NT
         Coq_asm_operand'nt) :: [])) (fun o -> o :: [])
     | Prod'asm_operands_ne'0 ->
       Obj.magic box (Coq_asm_operands_ne'nt, ((NT Coq_asm_operand'nt) :: ((T
         COMMA't) :: ((NT Coq_asm_operands_ne'nt) :: [])))) (fun o _ ol ->
         o :: ol)
     | Prod'asm_operands'1 ->
       Obj.magic box (Coq_asm_operands'nt, ((NT
         Coq_asm_operands_ne'nt) :: [])) rev'
     | Prod'asm_operands'0 -> Obj.magic box (Coq_asm_operands'nt, []) []
     | Prod'asm_operand'0 ->
       Obj.magic box (Coq_asm_operand'nt, ((T RPAREN't) :: ((NT
         Coq_expression'nt) :: ((T LPAREN't) :: ((T STRING_LITERAL't) :: ((NT
         Coq_asm_op_name'nt) :: [])))))) (fun _ e _ cstr n ->
         let (p0, _) = cstr in
         let (wide, s) = p0 in ASMOPERAND (n, wide, s, (fst e)))
     | Prod'asm_op_name'1 ->
       Obj.magic box (Coq_asm_op_name'nt, ((T RBRACK't) :: ((T
         OTHER_NAME't) :: ((T LBRACK't) :: [])))) (fun _ n _ -> Some 
         (fst n))
     | Prod'asm_op_name'0 -> Obj.magic box (Coq_asm_op_name'nt, []) None
     | Prod'asm_flags'1 ->
       Obj.magic box (Coq_asm_flags'nt, ((NT Coq_asm_flags'nt) :: ((T
         COMMA't) :: ((T STRING_LITERAL't) :: [])))) (fun fl _ f ->
         let (p0, _) = f in let (wide, s) = p0 in (wide, s) :: fl)
     | Prod'asm_flags'0 ->
       Obj.magic box (Coq_asm_flags'nt, ((T STRING_LITERAL't) :: []))
         (fun f -> let (p0, _) = f in let (wide, s) = p0 in (wide, s) :: [])
     | Prod'asm_attributes'2 ->
       Obj.magic box (Coq_asm_attributes'nt, ((NT
         Coq_asm_attributes'nt) :: ((T VOLATILE't) :: []))) (fun attr _ ->
         CV_VOLATILE :: attr)
     | Prod'asm_attributes'1 ->
       Obj.magic box (Coq_asm_attributes'nt, ((NT
         Coq_asm_attributes'nt) :: ((T CONST't) :: []))) (fun attr _ ->
         CV_CONST :: attr)
     | Prod'asm_attributes'0 -> Obj.magic box (Coq_asm_attributes'nt, []) []
     | Prod'asm_arguments'3 ->
       Obj.magic box (Coq_asm_arguments'nt, ((NT Coq_asm_flags'nt) :: ((T
         COLON't) :: ((NT Coq_asm_operands'nt) :: ((T COLON't) :: ((NT
         Coq_asm_operands'nt) :: ((T COLON't) :: [])))))))
         (fun f _ i _ o _ -> ((o, i), f))
     | Prod'asm_arguments'2 ->
       Obj.magic box (Coq_asm_arguments'nt, ((NT Coq_asm_operands'nt) :: ((T
         COLON't) :: ((NT Coq_asm_operands'nt) :: ((T COLON't) :: [])))))
         (fun i _ o _ -> ((o, i), []))
     | Prod'asm_arguments'1 ->
       Obj.magic box (Coq_asm_arguments'nt, ((NT Coq_asm_operands'nt) :: ((T
         COLON't) :: []))) (fun o _ -> ((o, []), []))
     | Prod'asm_arguments'0 ->
       Obj.magic box (Coq_asm_arguments'nt, []) (([], []), [])
     | Prod'argument_expression_list'1 ->
       Obj.magic box (Coq_argument_expression_list'nt, ((NT
         Coq_assignment_expression'nt) :: ((T COMMA't) :: ((NT
         Coq_argument_expression_list'nt) :: [])))) (fun exprt _ exprq ->
         (fst exprt) :: exprq)
     | Prod'argument_expression_list'0 ->
       Obj.magic box (Coq_argument_expression_list'nt, ((NT
         Coq_assignment_expression'nt) :: [])) (fun expr -> (fst expr) :: [])
     | Prod'additive_expression'2 ->
       Obj.magic box (Coq_additive_expression'nt, ((NT
         Coq_multiplicative_expression'nt) :: ((T MINUS't) :: ((NT
         Coq_additive_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (SUB, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'additive_expression'1 ->
       Obj.magic box (Coq_additive_expression'nt, ((NT
         Coq_multiplicative_expression'nt) :: ((T PLUS't) :: ((NT
         Coq_additive_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY
         (ADD, (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'additive_expression'0 ->
       Obj.magic box (Coq_additive_expression'nt, ((NT
         Coq_multiplicative_expression'nt) :: [])) (fun expr -> expr)
     | Prod'abstract_declarator'2 ->
       Obj.magic box (Coq_abstract_declarator'nt, ((NT
         Coq_direct_abstract_declarator'nt) :: [])) (fun typ -> typ)
     | Prod'abstract_declarator'1 ->
       Obj.magic box (Coq_abstract_declarator'nt, ((NT
         Coq_direct_abstract_declarator'nt) :: ((NT Coq_pointer'nt) :: [])))
         (fun typ pt -> fst pt typ)
     | Prod'abstract_declarator'0 ->
       Obj.magic box (Coq_abstract_declarator'nt, ((NT
         Coq_pointer'nt) :: [])) (fun pt -> fst pt JUSTBASE)
     | Prod'AND_expression'1 ->
       Obj.magic box (AND_expression'nt, ((NT
         Coq_equality_expression'nt) :: ((T AND't) :: ((NT
         AND_expression'nt) :: [])))) (fun expr2 _ expr1 -> ((BINARY (BAND,
         (fst expr1), (fst expr2))), (snd expr1)))
     | Prod'AND_expression'0 ->
       Obj.magic box (AND_expression'nt, ((NT
         Coq_equality_expression'nt) :: [])) (fun expr -> expr))

  (** val prod_lhs : production -> nonterminal **)

  let prod_lhs p =
    fst (projT1 (prod_contents p))

  (** val prod_rhs_rev : production -> symbol list **)

  let prod_rhs_rev p =
    snd (projT1 (prod_contents p))

  (** val prod_action : production -> symbol_semantic_type arrows_right **)

  let prod_action p =
    projT2 (prod_contents p)

  type parse_tree =
  | Terminal_pt of token
  | Non_terminal_pt of production * token list * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of symbol list * token list * parse_tree_list * symbol
     * token list * parse_tree

  (** val parse_tree_rect :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rect f f0 _ _ = function
  | Terminal_pt x -> f x
  | Non_terminal_pt (x, x0, x1) -> f0 x x0 x1

  (** val parse_tree_rec :
      (token -> 'a1) -> (production -> token list -> parse_tree_list -> 'a1)
      -> symbol -> token list -> parse_tree -> 'a1 **)

  let parse_tree_rec f f0 _ _ = function
  | Terminal_pt x -> f x
  | Non_terminal_pt (x, x0, x1) -> f0 x x0 x1

  (** val parse_tree_list_rect :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rect f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rect f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val parse_tree_list_rec :
      'a1 -> (symbol list -> token list -> parse_tree_list -> 'a1 -> symbol
      -> token list -> parse_tree -> 'a1) -> symbol list -> token list ->
      parse_tree_list -> 'a1 **)

  let rec parse_tree_list_rec f f0 _ _ = function
  | Nil_ptl -> f
  | Cons_ptl (head_symbolsq, wordq, p0, head_symbolt, wordt, p1) ->
    f0 head_symbolsq wordq p0
      (parse_tree_list_rec f f0 head_symbolsq wordq p0) head_symbolt wordt p1

  (** val pt_sem :
      symbol -> token list -> parse_tree -> symbol_semantic_type **)

  let rec pt_sem _ _ = function
  | Terminal_pt tok -> token_sem tok
  | Non_terminal_pt (prod, word0, ptl) ->
    Obj.magic ptl_sem (prod_rhs_rev prod) word0 ptl (prod_action prod)

  (** val ptl_sem :
      symbol list -> token list -> parse_tree_list -> 'a1 arrows_right -> 'a1 **)

  and ptl_sem _ _ tree0 act =
    match tree0 with
    | Nil_ptl -> Obj.magic act
    | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
      ptl_sem head_symbolsq wordq q
        (Obj.magic act (pt_sem head_symbolt wordt t0))

  (** val pt_size : symbol -> token list -> parse_tree -> nat **)

  let rec pt_size _ _ = function
  | Terminal_pt _ -> S O
  | Non_terminal_pt (prod, word0, l) ->
    S (ptl_size (prod_rhs_rev prod) word0 l)

  (** val ptl_size : symbol list -> token list -> parse_tree_list -> nat **)

  and ptl_size _ _ = function
  | Nil_ptl -> O
  | Cons_ptl (head_symbolsq, wordq, q, head_symbolt, wordt, t0) ->
    add (pt_size head_symbolt wordt t0) (ptl_size head_symbolsq wordq q)
 end
module Coq__2 = Gram

module Aut =
 struct
  module Gram = Gram

  module GramDefs = Gram

  (** val nullable_nterm : Coq__2.nonterminal -> bool **)

  let nullable_nterm = function
  | Coq__2.Coq_asm_arguments'nt -> true
  | Coq__2.Coq_asm_attributes'nt -> true
  | Coq__2.Coq_asm_op_name'nt -> true
  | Coq__2.Coq_asm_operands'nt -> true
  | Coq__2.Coq_attribute_specifier_list'nt -> true
  | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> true
  | Coq__2.Coq_gcc_attribute'nt -> true
  | Coq__2.Coq_gcc_attribute_list'nt -> true
  | Coq__2.Coq_struct_declaration_list'nt -> true
  | _ -> false

  (** val first_nterm : Coq__2.nonterminal -> Coq__2.terminal list **)

  let first_nterm = function
  | Coq__2.Coq_abstract_declarator'nt ->
    Coq__2.STAR't :: (Coq__2.LPAREN't :: (Coq__2.LBRACK't :: []))
  | Coq__2.Coq_asm_arguments'nt -> Coq__2.COLON't :: []
  | Coq__2.Coq_asm_attributes'nt ->
    Coq__2.VOLATILE't :: (Coq__2.CONST't :: [])
  | Coq__2.Coq_asm_flags'nt -> Coq__2.STRING_LITERAL't :: []
  | Coq__2.Coq_asm_op_name'nt -> Coq__2.LBRACK't :: []
  | Coq__2.Coq_asm_operand'nt ->
    Coq__2.STRING_LITERAL't :: (Coq__2.LBRACK't :: [])
  | Coq__2.Coq_asm_operands'nt ->
    Coq__2.STRING_LITERAL't :: (Coq__2.LBRACK't :: [])
  | Coq__2.Coq_asm_operands_ne'nt ->
    Coq__2.STRING_LITERAL't :: (Coq__2.LBRACK't :: [])
  | Coq__2.Coq_asm_statement'nt -> Coq__2.ASM't :: []
  | Coq__2.Coq_assignment_operator'nt ->
    Coq__2.XOR_ASSIGN't :: (Coq__2.SUB_ASSIGN't :: (Coq__2.RIGHT_ASSIGN't :: (Coq__2.OR_ASSIGN't :: (Coq__2.MUL_ASSIGN't :: (Coq__2.MOD_ASSIGN't :: (Coq__2.LEFT_ASSIGN't :: (Coq__2.EQ't :: (Coq__2.DIV_ASSIGN't :: (Coq__2.AND_ASSIGN't :: (Coq__2.ADD_ASSIGN't :: []))))))))))
  | Coq__2.Coq_attribute_specifier'nt ->
    Coq__2.PACKED't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))
  | Coq__2.Coq_attribute_specifier_list'nt ->
    Coq__2.PACKED't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))
  | Coq__2.Coq_block_item'nt ->
    Coq__2.WHILE't :: (Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.VAR_NAME't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.TILDE't :: (Coq__2.SWITCH't :: (Coq__2.STRUCT't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STATIC't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.SEMICOLON't :: (Coq__2.RETURN't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PRAGMA't :: (Coq__2.PLUS't :: (Coq__2.PACKED't :: (Coq__2.OTHER_NAME't :: (Coq__2.NORETURN't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LONG't :: (Coq__2.LBRACE't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.INC't :: (Coq__2.IF_'t :: (Coq__2.GOTO't :: (Coq__2.FOR't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.DO't :: (Coq__2.DEFAULT't :: (Coq__2.DEC't :: (Coq__2.CONTINUE't :: (Coq__2.CONSTANT't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.CASE't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BREAK't :: (Coq__2.BANG't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ASM't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | Coq__2.Coq_block_item_list'nt ->
    Coq__2.WHILE't :: (Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.VAR_NAME't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.TILDE't :: (Coq__2.SWITCH't :: (Coq__2.STRUCT't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STATIC't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.SEMICOLON't :: (Coq__2.RETURN't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PRAGMA't :: (Coq__2.PLUS't :: (Coq__2.PACKED't :: (Coq__2.OTHER_NAME't :: (Coq__2.NORETURN't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LONG't :: (Coq__2.LBRACE't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.INC't :: (Coq__2.IF_'t :: (Coq__2.GOTO't :: (Coq__2.FOR't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.DO't :: (Coq__2.DEFAULT't :: (Coq__2.DEC't :: (Coq__2.CONTINUE't :: (Coq__2.CONSTANT't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.CASE't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BREAK't :: (Coq__2.BANG't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ASM't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | Coq__2.Coq_c_initializer'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.PLUS't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LBRACE't :: (Coq__2.INC't :: (Coq__2.DEC't :: (Coq__2.CONSTANT't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BANG't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: []))))))))))))))))
  | Coq__2.Coq_compound_statement'nt -> Coq__2.LBRACE't :: []
  | Coq__2.Coq_declaration'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_declaration_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_declaration_specifiers'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_declaration_specifiers_typespec_opt'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_declarator'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: []))
  | Coq__2.Coq_declarator_noattrend'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: []))
  | Coq__2.Coq_designation'nt -> Coq__2.LBRACK't :: (Coq__2.DOT't :: [])
  | Coq__2.Coq_designator'nt -> Coq__2.LBRACK't :: (Coq__2.DOT't :: [])
  | Coq__2.Coq_designator_list'nt -> Coq__2.LBRACK't :: (Coq__2.DOT't :: [])
  | Coq__2.Coq_direct_abstract_declarator'nt ->
    Coq__2.LPAREN't :: (Coq__2.LBRACK't :: [])
  | Coq__2.Coq_direct_declarator'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.LPAREN't :: [])
  | Coq__2.Coq_enum_specifier'nt -> Coq__2.ENUM't :: []
  | Coq__2.Coq_enumeration_constant'nt -> Coq__2.VAR_NAME't :: []
  | Coq__2.Coq_enumerator'nt -> Coq__2.VAR_NAME't :: []
  | Coq__2.Coq_enumerator_list'nt -> Coq__2.VAR_NAME't :: []
  | Coq__2.Coq_expression_statement'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.SEMICOLON't :: (Coq__2.PLUS't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.INC't :: (Coq__2.DEC't :: (Coq__2.CONSTANT't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BANG't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: []))))))))))))))))
  | Coq__2.Coq_external_declaration'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PRAGMA't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))))))))))
  | Coq__2.Coq_function_definition'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_function_specifier'nt ->
    Coq__2.NORETURN't :: (Coq__2.INLINE't :: [])
  | Coq__2.Coq_gcc_attribute'nt ->
    Coq__2.PACKED't :: (Coq__2.OTHER_NAME't :: (Coq__2.CONST't :: []))
  | Coq__2.Coq_gcc_attribute_list'nt ->
    Coq__2.PACKED't :: (Coq__2.OTHER_NAME't :: (Coq__2.CONST't :: (Coq__2.COMMA't :: [])))
  | Coq__2.Coq_gcc_attribute_word'nt ->
    Coq__2.PACKED't :: (Coq__2.OTHER_NAME't :: (Coq__2.CONST't :: []))
  | Coq__2.Coq_identifier_list'nt -> Coq__2.VAR_NAME't :: []
  | Coq__2.Coq_init_declarator'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: []))
  | Coq__2.Coq_init_declarator_list'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: []))
  | Coq__2.Coq_initializer_list'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.PLUS't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LBRACK't :: (Coq__2.LBRACE't :: (Coq__2.INC't :: (Coq__2.DOT't :: (Coq__2.DEC't :: (Coq__2.CONSTANT't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BANG't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: []))))))))))))))))))
  | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
    Coq__2.WHILE't :: (Coq__2.FOR't :: (Coq__2.DO't :: []))
  | Coq__2.Coq_iteration_statement_statement_safe_'nt ->
    Coq__2.WHILE't :: (Coq__2.FOR't :: (Coq__2.DO't :: []))
  | Coq__2.Coq_jump_statement'nt ->
    Coq__2.RETURN't :: (Coq__2.GOTO't :: (Coq__2.CONTINUE't :: (Coq__2.BREAK't :: [])))
  | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
    Coq__2.OTHER_NAME't :: (Coq__2.DEFAULT't :: (Coq__2.CASE't :: []))
  | Coq__2.Coq_labeled_statement_statement_safe_'nt ->
    Coq__2.OTHER_NAME't :: (Coq__2.DEFAULT't :: (Coq__2.CASE't :: []))
  | Coq__2.Coq_parameter_declaration'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_parameter_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_parameter_type_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))
  | Coq__2.Coq_pointer'nt -> Coq__2.STAR't :: []
  | Coq__2.Coq_postfix_expression'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STRING_LITERAL't :: (Coq__2.LPAREN't :: (Coq__2.CONSTANT't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: [])))))
  | Coq__2.Coq_primary_expression'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STRING_LITERAL't :: (Coq__2.LPAREN't :: (Coq__2.CONSTANT't :: [])))
  | Coq__2.Coq_selection_statement_dangerous'nt ->
    Coq__2.SWITCH't :: (Coq__2.IF_'t :: [])
  | Coq__2.Coq_selection_statement_safe'nt ->
    Coq__2.SWITCH't :: (Coq__2.IF_'t :: [])
  | Coq__2.Coq_specifier_qualifier_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.STRUCT't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.FLOAT't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))
  | Coq__2.Coq_statement_dangerous'nt ->
    Coq__2.WHILE't :: (Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.SWITCH't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.SEMICOLON't :: (Coq__2.RETURN't :: (Coq__2.PLUS't :: (Coq__2.OTHER_NAME't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LBRACE't :: (Coq__2.INC't :: (Coq__2.IF_'t :: (Coq__2.GOTO't :: (Coq__2.FOR't :: (Coq__2.DO't :: (Coq__2.DEFAULT't :: (Coq__2.DEC't :: (Coq__2.CONTINUE't :: (Coq__2.CONSTANT't :: (Coq__2.CASE't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BREAK't :: (Coq__2.BANG't :: (Coq__2.ASM't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: []))))))))))))))))))))))))))))))
  | Coq__2.Coq_statement_safe'nt ->
    Coq__2.WHILE't :: (Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.SWITCH't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.SEMICOLON't :: (Coq__2.RETURN't :: (Coq__2.PLUS't :: (Coq__2.OTHER_NAME't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.LBRACE't :: (Coq__2.INC't :: (Coq__2.IF_'t :: (Coq__2.GOTO't :: (Coq__2.FOR't :: (Coq__2.DO't :: (Coq__2.DEFAULT't :: (Coq__2.DEC't :: (Coq__2.CONTINUE't :: (Coq__2.CONSTANT't :: (Coq__2.CASE't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BREAK't :: (Coq__2.BANG't :: (Coq__2.ASM't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: []))))))))))))))))))))))))))))))
  | Coq__2.Coq_storage_class_specifier'nt ->
    Coq__2.TYPEDEF't :: (Coq__2.STATIC't :: (Coq__2.REGISTER't :: (Coq__2.EXTERN't :: (Coq__2.AUTO't :: []))))
  | Coq__2.Coq_struct_declaration'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.STRUCT't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.FLOAT't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))
  | Coq__2.Coq_struct_declaration_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.STRUCT't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.FLOAT't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))
  | Coq__2.Coq_struct_declarator'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: (Coq__2.COLON't :: [])))
  | Coq__2.Coq_struct_declarator_list'nt ->
    Coq__2.VAR_NAME't :: (Coq__2.STAR't :: (Coq__2.LPAREN't :: (Coq__2.COLON't :: [])))
  | Coq__2.Coq_struct_or_union'nt -> Coq__2.UNION't :: (Coq__2.STRUCT't :: [])
  | Coq__2.Coq_struct_or_union_specifier'nt ->
    Coq__2.UNION't :: (Coq__2.STRUCT't :: [])
  | Coq__2.Coq_translation_unit'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.SEMICOLON't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PRAGMA't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: []))))))))))))))))))))))))))))
  | Coq__2.Coq_translation_unit_file'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.TYPEDEF't :: (Coq__2.STRUCT't :: (Coq__2.STATIC't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.SEMICOLON't :: (Coq__2.RESTRICT't :: (Coq__2.REGISTER't :: (Coq__2.PRAGMA't :: (Coq__2.PACKED't :: (Coq__2.NORETURN't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.INLINE't :: (Coq__2.FLOAT't :: (Coq__2.EXTERN't :: (Coq__2.EOF't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.AUTO't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))))))))))))
  | Coq__2.Coq_type_name'nt ->
    Coq__2.VOLATILE't :: (Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.STRUCT't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.FLOAT't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CONST't :: (Coq__2.CHAR't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))))))))))))))))
  | Coq__2.Coq_type_qualifier'nt ->
    Coq__2.VOLATILE't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.CONST't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))
  | Coq__2.Coq_type_qualifier_list'nt ->
    Coq__2.VOLATILE't :: (Coq__2.RESTRICT't :: (Coq__2.PACKED't :: (Coq__2.CONST't :: (Coq__2.ATTRIBUTE't :: (Coq__2.ALIGNAS't :: [])))))
  | Coq__2.Coq_type_qualifier_noattr'nt ->
    Coq__2.VOLATILE't :: (Coq__2.RESTRICT't :: (Coq__2.CONST't :: []))
  | Coq__2.Coq_type_specifier'nt ->
    Coq__2.VOID't :: (Coq__2.UNSIGNED't :: (Coq__2.UNION't :: (Coq__2.UNDERSCORE_BOOL't :: (Coq__2.TYPEDEF_NAME't :: (Coq__2.STRUCT't :: (Coq__2.SIGNED't :: (Coq__2.SHORT't :: (Coq__2.LONG't :: (Coq__2.INT't :: (Coq__2.FLOAT't :: (Coq__2.ENUM't :: (Coq__2.DOUBLE't :: (Coq__2.CHAR't :: [])))))))))))))
  | Coq__2.Coq_unary_operator'nt ->
    Coq__2.TILDE't :: (Coq__2.STAR't :: (Coq__2.PLUS't :: (Coq__2.MINUS't :: (Coq__2.BANG't :: (Coq__2.AND't :: [])))))
  | _ ->
    Coq__2.VAR_NAME't :: (Coq__2.TILDE't :: (Coq__2.STRING_LITERAL't :: (Coq__2.STAR't :: (Coq__2.SIZEOF't :: (Coq__2.PLUS't :: (Coq__2.MINUS't :: (Coq__2.LPAREN't :: (Coq__2.INC't :: (Coq__2.DEC't :: (Coq__2.CONSTANT't :: (Coq__2.BUILTIN_VA_ARG't :: (Coq__2.BUILTIN_OFFSETOF't :: (Coq__2.BANG't :: (Coq__2.AND't :: (Coq__2.ALIGNOF't :: [])))))))))))))))

  type noninitstate' =
  | Nis'612
  | Nis'611
  | Nis'610
  | Nis'609
  | Nis'608
  | Nis'607
  | Nis'606
  | Nis'605
  | Nis'604
  | Nis'603
  | Nis'602
  | Nis'601
  | Nis'600
  | Nis'599
  | Nis'598
  | Nis'597
  | Nis'596
  | Nis'595
  | Nis'594
  | Nis'593
  | Nis'592
  | Nis'591
  | Nis'590
  | Nis'589
  | Nis'588
  | Nis'587
  | Nis'586
  | Nis'585
  | Nis'584
  | Nis'583
  | Nis'582
  | Nis'581
  | Nis'580
  | Nis'579
  | Nis'578
  | Nis'577
  | Nis'576
  | Nis'575
  | Nis'574
  | Nis'573
  | Nis'572
  | Nis'571
  | Nis'570
  | Nis'569
  | Nis'568
  | Nis'567
  | Nis'566
  | Nis'565
  | Nis'564
  | Nis'563
  | Nis'562
  | Nis'561
  | Nis'560
  | Nis'559
  | Nis'558
  | Nis'557
  | Nis'556
  | Nis'555
  | Nis'554
  | Nis'553
  | Nis'552
  | Nis'551
  | Nis'550
  | Nis'549
  | Nis'548
  | Nis'547
  | Nis'546
  | Nis'545
  | Nis'544
  | Nis'543
  | Nis'542
  | Nis'541
  | Nis'540
  | Nis'539
  | Nis'538
  | Nis'537
  | Nis'536
  | Nis'535
  | Nis'534
  | Nis'533
  | Nis'532
  | Nis'531
  | Nis'530
  | Nis'529
  | Nis'528
  | Nis'527
  | Nis'526
  | Nis'525
  | Nis'524
  | Nis'523
  | Nis'522
  | Nis'521
  | Nis'520
  | Nis'519
  | Nis'518
  | Nis'517
  | Nis'516
  | Nis'515
  | Nis'514
  | Nis'513
  | Nis'512
  | Nis'511
  | Nis'510
  | Nis'509
  | Nis'508
  | Nis'507
  | Nis'506
  | Nis'505
  | Nis'504
  | Nis'503
  | Nis'502
  | Nis'501
  | Nis'500
  | Nis'499
  | Nis'498
  | Nis'497
  | Nis'496
  | Nis'495
  | Nis'494
  | Nis'493
  | Nis'492
  | Nis'491
  | Nis'490
  | Nis'489
  | Nis'488
  | Nis'487
  | Nis'486
  | Nis'485
  | Nis'484
  | Nis'483
  | Nis'482
  | Nis'481
  | Nis'480
  | Nis'479
  | Nis'478
  | Nis'477
  | Nis'476
  | Nis'475
  | Nis'474
  | Nis'473
  | Nis'472
  | Nis'471
  | Nis'470
  | Nis'469
  | Nis'468
  | Nis'467
  | Nis'466
  | Nis'465
  | Nis'464
  | Nis'463
  | Nis'462
  | Nis'461
  | Nis'460
  | Nis'459
  | Nis'458
  | Nis'457
  | Nis'456
  | Nis'455
  | Nis'454
  | Nis'453
  | Nis'452
  | Nis'451
  | Nis'450
  | Nis'449
  | Nis'448
  | Nis'447
  | Nis'446
  | Nis'445
  | Nis'444
  | Nis'443
  | Nis'442
  | Nis'441
  | Nis'440
  | Nis'439
  | Nis'438
  | Nis'437
  | Nis'436
  | Nis'435
  | Nis'434
  | Nis'433
  | Nis'432
  | Nis'431
  | Nis'430
  | Nis'429
  | Nis'428
  | Nis'427
  | Nis'426
  | Nis'425
  | Nis'424
  | Nis'423
  | Nis'422
  | Nis'421
  | Nis'420
  | Nis'419
  | Nis'418
  | Nis'417
  | Nis'416
  | Nis'415
  | Nis'414
  | Nis'413
  | Nis'412
  | Nis'411
  | Nis'410
  | Nis'409
  | Nis'408
  | Nis'407
  | Nis'406
  | Nis'405
  | Nis'404
  | Nis'403
  | Nis'402
  | Nis'401
  | Nis'400
  | Nis'399
  | Nis'398
  | Nis'397
  | Nis'396
  | Nis'395
  | Nis'394
  | Nis'393
  | Nis'392
  | Nis'391
  | Nis'390
  | Nis'389
  | Nis'388
  | Nis'387
  | Nis'386
  | Nis'385
  | Nis'384
  | Nis'383
  | Nis'382
  | Nis'381
  | Nis'380
  | Nis'379
  | Nis'378
  | Nis'377
  | Nis'376
  | Nis'375
  | Nis'374
  | Nis'373
  | Nis'372
  | Nis'371
  | Nis'370
  | Nis'369
  | Nis'368
  | Nis'367
  | Nis'366
  | Nis'365
  | Nis'364
  | Nis'363
  | Nis'362
  | Nis'361
  | Nis'360
  | Nis'359
  | Nis'357
  | Nis'356
  | Nis'355
  | Nis'354
  | Nis'353
  | Nis'352
  | Nis'351
  | Nis'350
  | Nis'349
  | Nis'348
  | Nis'347
  | Nis'346
  | Nis'345
  | Nis'344
  | Nis'343
  | Nis'342
  | Nis'341
  | Nis'340
  | Nis'339
  | Nis'338
  | Nis'337
  | Nis'336
  | Nis'335
  | Nis'334
  | Nis'333
  | Nis'332
  | Nis'331
  | Nis'330
  | Nis'329
  | Nis'328
  | Nis'327
  | Nis'326
  | Nis'325
  | Nis'324
  | Nis'323
  | Nis'322
  | Nis'321
  | Nis'320
  | Nis'319
  | Nis'318
  | Nis'317
  | Nis'316
  | Nis'315
  | Nis'314
  | Nis'313
  | Nis'312
  | Nis'311
  | Nis'310
  | Nis'309
  | Nis'308
  | Nis'307
  | Nis'306
  | Nis'305
  | Nis'304
  | Nis'303
  | Nis'302
  | Nis'301
  | Nis'300
  | Nis'299
  | Nis'298
  | Nis'297
  | Nis'296
  | Nis'295
  | Nis'294
  | Nis'293
  | Nis'292
  | Nis'291
  | Nis'290
  | Nis'289
  | Nis'288
  | Nis'287
  | Nis'286
  | Nis'285
  | Nis'284
  | Nis'283
  | Nis'282
  | Nis'281
  | Nis'280
  | Nis'279
  | Nis'278
  | Nis'277
  | Nis'276
  | Nis'275
  | Nis'274
  | Nis'273
  | Nis'272
  | Nis'271
  | Nis'270
  | Nis'269
  | Nis'268
  | Nis'267
  | Nis'266
  | Nis'265
  | Nis'264
  | Nis'263
  | Nis'262
  | Nis'261
  | Nis'260
  | Nis'259
  | Nis'258
  | Nis'257
  | Nis'256
  | Nis'255
  | Nis'254
  | Nis'253
  | Nis'252
  | Nis'251
  | Nis'250
  | Nis'249
  | Nis'248
  | Nis'247
  | Nis'246
  | Nis'245
  | Nis'244
  | Nis'243
  | Nis'242
  | Nis'241
  | Nis'240
  | Nis'239
  | Nis'238
  | Nis'237
  | Nis'236
  | Nis'235
  | Nis'234
  | Nis'233
  | Nis'232
  | Nis'231
  | Nis'230
  | Nis'229
  | Nis'228
  | Nis'227
  | Nis'226
  | Nis'225
  | Nis'224
  | Nis'223
  | Nis'222
  | Nis'221
  | Nis'220
  | Nis'219
  | Nis'218
  | Nis'217
  | Nis'216
  | Nis'215
  | Nis'214
  | Nis'213
  | Nis'212
  | Nis'211
  | Nis'210
  | Nis'209
  | Nis'208
  | Nis'207
  | Nis'206
  | Nis'205
  | Nis'204
  | Nis'203
  | Nis'202
  | Nis'201
  | Nis'200
  | Nis'199
  | Nis'198
  | Nis'197
  | Nis'196
  | Nis'195
  | Nis'194
  | Nis'193
  | Nis'192
  | Nis'191
  | Nis'190
  | Nis'189
  | Nis'188
  | Nis'187
  | Nis'186
  | Nis'185
  | Nis'184
  | Nis'183
  | Nis'182
  | Nis'181
  | Nis'180
  | Nis'179
  | Nis'178
  | Nis'177
  | Nis'176
  | Nis'175
  | Nis'174
  | Nis'173
  | Nis'172
  | Nis'171
  | Nis'170
  | Nis'169
  | Nis'168
  | Nis'167
  | Nis'166
  | Nis'165
  | Nis'164
  | Nis'163
  | Nis'162
  | Nis'161
  | Nis'160
  | Nis'159
  | Nis'158
  | Nis'157
  | Nis'156
  | Nis'155
  | Nis'154
  | Nis'153
  | Nis'152
  | Nis'151
  | Nis'150
  | Nis'149
  | Nis'148
  | Nis'147
  | Nis'146
  | Nis'145
  | Nis'144
  | Nis'143
  | Nis'142
  | Nis'141
  | Nis'140
  | Nis'139
  | Nis'138
  | Nis'137
  | Nis'136
  | Nis'135
  | Nis'134
  | Nis'133
  | Nis'132
  | Nis'131
  | Nis'130
  | Nis'129
  | Nis'128
  | Nis'127
  | Nis'126
  | Nis'125
  | Nis'124
  | Nis'123
  | Nis'122
  | Nis'121
  | Nis'120
  | Nis'119
  | Nis'118
  | Nis'117
  | Nis'116
  | Nis'115
  | Nis'114
  | Nis'113
  | Nis'112
  | Nis'111
  | Nis'110
  | Nis'109
  | Nis'108
  | Nis'107
  | Nis'106
  | Nis'105
  | Nis'104
  | Nis'103
  | Nis'102
  | Nis'101
  | Nis'100
  | Nis'99
  | Nis'98
  | Nis'97
  | Nis'96
  | Nis'95
  | Nis'94
  | Nis'93
  | Nis'92
  | Nis'91
  | Nis'90
  | Nis'89
  | Nis'88
  | Nis'87
  | Nis'86
  | Nis'85
  | Nis'84
  | Nis'83
  | Nis'82
  | Nis'81
  | Nis'80
  | Nis'79
  | Nis'78
  | Nis'77
  | Nis'76
  | Nis'75
  | Nis'74
  | Nis'73
  | Nis'72
  | Nis'71
  | Nis'70
  | Nis'69
  | Nis'68
  | Nis'67
  | Nis'66
  | Nis'65
  | Nis'64
  | Nis'63
  | Nis'62
  | Nis'61
  | Nis'60
  | Nis'59
  | Nis'58
  | Nis'57
  | Nis'56
  | Nis'55
  | Nis'54
  | Nis'53
  | Nis'52
  | Nis'51
  | Nis'50
  | Nis'49
  | Nis'48
  | Nis'47
  | Nis'46
  | Nis'45
  | Nis'44
  | Nis'43
  | Nis'42
  | Nis'41
  | Nis'40
  | Nis'39
  | Nis'38
  | Nis'37
  | Nis'36
  | Nis'35
  | Nis'34
  | Nis'33
  | Nis'32
  | Nis'31
  | Nis'30
  | Nis'29
  | Nis'28
  | Nis'27
  | Nis'26
  | Nis'25
  | Nis'24
  | Nis'23
  | Nis'22
  | Nis'21
  | Nis'20
  | Nis'19
  | Nis'18
  | Nis'17
  | Nis'16
  | Nis'15
  | Nis'14
  | Nis'13
  | Nis'12
  | Nis'11
  | Nis'10
  | Nis'9
  | Nis'8
  | Nis'7
  | Nis'6
  | Nis'5
  | Nis'4
  | Nis'3
  | Nis'2
  | Nis'1

  type noninitstate = noninitstate'

  (** val noninitstateNum : noninitstate coq_Numbered **)

  let noninitstateNum =
    { inj = (fun x ->
      match x with
      | Nis'612 -> Coq_xH
      | Nis'611 -> Coq_xO Coq_xH
      | Nis'610 -> Coq_xI Coq_xH
      | Nis'609 -> Coq_xO (Coq_xO Coq_xH)
      | Nis'608 -> Coq_xI (Coq_xO Coq_xH)
      | Nis'607 -> Coq_xO (Coq_xI Coq_xH)
      | Nis'606 -> Coq_xI (Coq_xI Coq_xH)
      | Nis'605 -> Coq_xO (Coq_xO (Coq_xO Coq_xH))
      | Nis'604 -> Coq_xI (Coq_xO (Coq_xO Coq_xH))
      | Nis'603 -> Coq_xO (Coq_xI (Coq_xO Coq_xH))
      | Nis'602 -> Coq_xI (Coq_xI (Coq_xO Coq_xH))
      | Nis'601 -> Coq_xO (Coq_xO (Coq_xI Coq_xH))
      | Nis'600 -> Coq_xI (Coq_xO (Coq_xI Coq_xH))
      | Nis'599 -> Coq_xO (Coq_xI (Coq_xI Coq_xH))
      | Nis'598 -> Coq_xI (Coq_xI (Coq_xI Coq_xH))
      | Nis'597 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Nis'596 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Nis'595 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Nis'594 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Nis'593 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Nis'592 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Nis'591 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Nis'590 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Nis'589 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Nis'588 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Nis'587 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Nis'586 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Nis'585 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Nis'584 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Nis'583 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Nis'582 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Nis'581 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis'580 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis'579 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis'578 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis'577 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis'576 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis'575 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis'574 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis'573 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis'572 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis'571 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis'570 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis'569 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis'568 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis'567 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis'566 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis'565 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis'564 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis'563 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis'562 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis'561 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis'560 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis'559 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis'558 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis'557 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis'556 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis'555 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis'554 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis'553 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis'552 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis'551 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis'550 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis'549 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'548 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'547 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'546 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'545 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'544 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'543 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'542 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'541 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'540 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'539 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'538 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'537 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'536 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'535 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'534 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis'533 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'532 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'531 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'530 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'529 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'528 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'527 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'526 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'525 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'524 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'523 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'522 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'521 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'520 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'519 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'518 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis'517 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'516 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'515 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'514 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'513 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'512 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'511 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'510 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'509 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'508 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'507 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'506 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'505 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'504 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'503 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'502 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis'501 -> Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'500 -> Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'499 -> Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'498 -> Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'497 -> Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'496 -> Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'495 -> Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'494 -> Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'493 -> Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'492 -> Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'491 -> Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'490 -> Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'489 -> Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'488 -> Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'487 -> Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'486 -> Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis'485 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'484 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'483 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'482 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'481 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'480 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'479 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'478 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'477 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'476 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'475 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'474 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'473 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'472 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'471 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'470 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'469 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'468 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'467 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'466 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'465 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'464 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'463 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'462 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'461 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'460 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'459 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'458 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'457 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'456 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'455 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'454 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis'453 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'452 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'451 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'450 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'449 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'448 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'447 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'446 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'445 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'444 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'443 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'442 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'441 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'440 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'439 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'438 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'437 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'436 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'435 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'434 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'433 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'432 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'431 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'430 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'429 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'428 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'427 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'426 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'425 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'424 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'423 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'422 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis'421 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'420 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'419 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'418 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'417 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'416 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'415 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'414 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'413 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'412 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'411 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'410 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'409 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'408 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'407 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'406 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'405 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'404 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'403 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'402 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'401 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'400 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'399 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'398 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'397 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'396 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'395 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'394 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'393 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'392 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'391 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'390 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis'389 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'388 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'387 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'386 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'385 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'384 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'383 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'382 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'381 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'380 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'379 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'378 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'377 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'376 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'375 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'374 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'373 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'372 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'371 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'370 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'369 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'368 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'367 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'366 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'365 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'364 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'363 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'362 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'361 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'360 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'359 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'357 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis'356 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'355 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'354 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'353 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'352 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'351 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'350 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'349 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'348 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'347 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'346 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'345 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'344 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'343 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'342 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'341 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'340 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'339 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'338 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'337 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'336 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'335 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'334 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'333 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'332 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'331 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'330 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'329 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'328 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'327 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'326 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'325 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'324 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'323 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'322 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'321 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'320 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'319 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'318 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'317 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'316 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'315 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'314 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'313 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'312 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'311 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'310 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'309 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'308 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'307 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'306 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'305 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'304 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'303 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'302 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'301 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'300 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'299 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'298 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'297 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'296 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'295 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'294 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'293 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis'292 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'291 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'290 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'289 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'288 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'287 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'286 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'285 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'284 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'283 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'282 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'281 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'280 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'279 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'278 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'277 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'276 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'275 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'274 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'273 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'272 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'271 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'270 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'269 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'268 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'267 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'266 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'265 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'264 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'263 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'262 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'261 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'260 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'259 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'258 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'257 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'256 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'255 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'254 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'253 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'252 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'251 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'250 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'249 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'248 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'247 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'246 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'245 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'244 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'243 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'242 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'241 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'240 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'239 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'238 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'237 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'236 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'235 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'234 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'233 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'232 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'231 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'230 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'229 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis'228 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'227 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'226 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'225 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'224 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'223 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'222 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'221 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'220 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'219 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'218 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'217 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'216 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'215 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'214 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'213 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'212 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'211 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'210 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'209 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'208 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'207 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'206 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'205 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'204 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'203 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'202 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'201 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'200 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'199 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'198 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'197 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'196 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'195 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'194 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'193 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'192 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'191 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'190 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'189 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'188 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'187 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'186 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'185 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'184 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'183 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'182 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'181 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'180 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'179 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'178 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'177 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'176 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'175 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'174 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'173 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'172 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'171 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'170 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'169 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'168 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'167 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'166 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'165 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis'164 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'163 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'162 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'161 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'160 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'159 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'158 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'157 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'156 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'155 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'154 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'153 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'152 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'151 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'150 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'149 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'148 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'147 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'146 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'145 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'144 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'143 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'142 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'141 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'140 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'139 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'138 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'137 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'136 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'135 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'134 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'133 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'132 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'131 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'130 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'129 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'128 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'127 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'126 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'125 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'124 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'123 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'122 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'121 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'120 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'119 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'118 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'117 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'116 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'115 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'114 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'113 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'112 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'111 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'110 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'109 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'108 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'107 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'106 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'105 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'104 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'103 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'102 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'101 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis'100 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'99 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'98 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'97 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'96 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'95 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'94 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'93 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'92 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'91 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'90 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'89 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'88 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'87 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'86 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'85 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'84 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'83 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'82 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'81 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'80 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'79 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'78 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'77 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'76 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'75 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'74 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'73 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'72 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'71 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'70 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'69 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'68 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'67 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'66 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'65 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'64 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'63 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'62 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'61 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'60 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'59 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'58 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'57 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'56 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'55 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'54 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'53 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'52 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'51 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'50 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'49 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'48 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'47 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'46 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'45 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'44 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'43 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'42 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'41 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'40 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'39 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'38 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'37 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'36 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'35 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'34 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'33 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'32 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'31 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'30 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'29 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'28 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'27 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'26 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'25 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'24 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'23 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'22 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'21 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'20 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'19 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'18 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'17 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'16 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'15 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'14 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'13 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'12 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'11 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'10 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'9 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'8 ->
        Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'7 ->
        Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'6 ->
        Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'5 ->
        Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'4 ->
        Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'3 ->
        Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'2 ->
        Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))
      | Nis'1 ->
        Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          (Coq_xO Coq_xH))))))))); surj = (fun n ->
      match n with
      | Coq_xI p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'101
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'229
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'357)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'165
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'37
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'293)
                           | Coq_xH -> Nis'422)
                        | Coq_xH -> Nis'486)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'133
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'5
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'261)
                           | Coq_xH -> Nis'390)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'197
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'69
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'325)
                           | Coq_xH -> Nis'454)
                        | Coq_xH -> Nis'518)
                     | Coq_xH -> Nis'550)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'117
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'245
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'374)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'181
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'53
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'309)
                           | Coq_xH -> Nis'438)
                        | Coq_xH -> Nis'502)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'149
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'21
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'277)
                           | Coq_xH -> Nis'406)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'213
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'85
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'341)
                           | Coq_xH -> Nis'470)
                        | Coq_xH -> Nis'534)
                     | Coq_xH -> Nis'566)
                  | Coq_xH -> Nis'582)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'109
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'237
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'366)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'173
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'45
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'301)
                           | Coq_xH -> Nis'430)
                        | Coq_xH -> Nis'494)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'141
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'13
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'269)
                           | Coq_xH -> Nis'398)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'205
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'77
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'333)
                           | Coq_xH -> Nis'462)
                        | Coq_xH -> Nis'526)
                     | Coq_xH -> Nis'558)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'125
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'253
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'382)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'189
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'61
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'317)
                           | Coq_xH -> Nis'446)
                        | Coq_xH -> Nis'510)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'157
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'29
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'285)
                           | Coq_xH -> Nis'414)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'221
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'93
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'349)
                           | Coq_xH -> Nis'478)
                        | Coq_xH -> Nis'542)
                     | Coq_xH -> Nis'574)
                  | Coq_xH -> Nis'590)
               | Coq_xH -> Nis'598)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'105
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'233
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'362)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'169
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'41
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'297)
                           | Coq_xH -> Nis'426)
                        | Coq_xH -> Nis'490)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'137
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'9
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'265)
                           | Coq_xH -> Nis'394)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'201
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'73
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'329)
                           | Coq_xH -> Nis'458)
                        | Coq_xH -> Nis'522)
                     | Coq_xH -> Nis'554)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'121
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'249
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'378)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'185
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'57
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'313)
                           | Coq_xH -> Nis'442)
                        | Coq_xH -> Nis'506)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'153
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'25
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'281)
                           | Coq_xH -> Nis'410)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'217
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'89
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'345)
                           | Coq_xH -> Nis'474)
                        | Coq_xH -> Nis'538)
                     | Coq_xH -> Nis'570)
                  | Coq_xH -> Nis'586)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'113
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'241
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'370)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'177
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'49
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'305)
                           | Coq_xH -> Nis'434)
                        | Coq_xH -> Nis'498)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'145
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'17
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'273)
                           | Coq_xH -> Nis'402)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'209
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'81
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'337)
                           | Coq_xH -> Nis'466)
                        | Coq_xH -> Nis'530)
                     | Coq_xH -> Nis'562)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'129
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'1
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'257)
                           | Coq_xH -> Nis'386)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'193
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'65
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'321)
                           | Coq_xH -> Nis'450)
                        | Coq_xH -> Nis'514)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'161
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'33
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'289)
                           | Coq_xH -> Nis'418)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'225
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'97
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'353)
                           | Coq_xH -> Nis'482)
                        | Coq_xH -> Nis'546)
                     | Coq_xH -> Nis'578)
                  | Coq_xH -> Nis'594)
               | Coq_xH -> Nis'602)
            | Coq_xH -> Nis'606)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'103
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'231
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'360)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'167
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'39
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'295)
                           | Coq_xH -> Nis'424)
                        | Coq_xH -> Nis'488)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'135
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'7
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'263)
                           | Coq_xH -> Nis'392)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'199
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'71
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'327)
                           | Coq_xH -> Nis'456)
                        | Coq_xH -> Nis'520)
                     | Coq_xH -> Nis'552)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'119
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'247
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'376)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'183
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'55
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'311)
                           | Coq_xH -> Nis'440)
                        | Coq_xH -> Nis'504)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'151
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'23
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'279)
                           | Coq_xH -> Nis'408)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'215
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'87
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'343)
                           | Coq_xH -> Nis'472)
                        | Coq_xH -> Nis'536)
                     | Coq_xH -> Nis'568)
                  | Coq_xH -> Nis'584)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'111
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'239
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'368)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'175
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'47
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'303)
                           | Coq_xH -> Nis'432)
                        | Coq_xH -> Nis'496)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'143
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'15
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'271)
                           | Coq_xH -> Nis'400)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'207
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'79
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'335)
                           | Coq_xH -> Nis'464)
                        | Coq_xH -> Nis'528)
                     | Coq_xH -> Nis'560)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'127
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'255
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'384)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'191
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'63
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'319)
                           | Coq_xH -> Nis'448)
                        | Coq_xH -> Nis'512)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'159
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'31
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'287)
                           | Coq_xH -> Nis'416)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'223
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'95
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'351)
                           | Coq_xH -> Nis'480)
                        | Coq_xH -> Nis'544)
                     | Coq_xH -> Nis'576)
                  | Coq_xH -> Nis'592)
               | Coq_xH -> Nis'600)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'107
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'235
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'364)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'171
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'43
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'299)
                           | Coq_xH -> Nis'428)
                        | Coq_xH -> Nis'492)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'139
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'11
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'267)
                           | Coq_xH -> Nis'396)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'203
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'75
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'331)
                           | Coq_xH -> Nis'460)
                        | Coq_xH -> Nis'524)
                     | Coq_xH -> Nis'556)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'123
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'251
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'380)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'187
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'59
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'315)
                           | Coq_xH -> Nis'444)
                        | Coq_xH -> Nis'508)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'155
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'27
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'283)
                           | Coq_xH -> Nis'412)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'219
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'91
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'347)
                           | Coq_xH -> Nis'476)
                        | Coq_xH -> Nis'540)
                     | Coq_xH -> Nis'572)
                  | Coq_xH -> Nis'588)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'115
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'243
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'372)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'179
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'51
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'307)
                           | Coq_xH -> Nis'436)
                        | Coq_xH -> Nis'500)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'147
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'19
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'275)
                           | Coq_xH -> Nis'404)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'211
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'83
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'339)
                           | Coq_xH -> Nis'468)
                        | Coq_xH -> Nis'532)
                     | Coq_xH -> Nis'564)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'131
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'3
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'259)
                           | Coq_xH -> Nis'388)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'195
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'67
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'323)
                           | Coq_xH -> Nis'452)
                        | Coq_xH -> Nis'516)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'163
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'35
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'291)
                           | Coq_xH -> Nis'420)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'227
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'99
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'355)
                           | Coq_xH -> Nis'484)
                        | Coq_xH -> Nis'548)
                     | Coq_xH -> Nis'580)
                  | Coq_xH -> Nis'596)
               | Coq_xH -> Nis'604)
            | Coq_xH -> Nis'608)
         | Coq_xH -> Nis'610)
      | Coq_xO p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'102
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'230
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'359)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'166
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'38
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'294)
                           | Coq_xH -> Nis'423)
                        | Coq_xH -> Nis'487)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'134
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'6
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'262)
                           | Coq_xH -> Nis'391)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'198
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'70
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'326)
                           | Coq_xH -> Nis'455)
                        | Coq_xH -> Nis'519)
                     | Coq_xH -> Nis'551)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'118
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'246
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'375)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'182
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'54
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'310)
                           | Coq_xH -> Nis'439)
                        | Coq_xH -> Nis'503)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'150
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'22
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'278)
                           | Coq_xH -> Nis'407)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'214
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'86
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'342)
                           | Coq_xH -> Nis'471)
                        | Coq_xH -> Nis'535)
                     | Coq_xH -> Nis'567)
                  | Coq_xH -> Nis'583)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'110
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'238
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'367)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'174
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'46
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'302)
                           | Coq_xH -> Nis'431)
                        | Coq_xH -> Nis'495)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'142
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'14
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'270)
                           | Coq_xH -> Nis'399)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'206
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'78
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'334)
                           | Coq_xH -> Nis'463)
                        | Coq_xH -> Nis'527)
                     | Coq_xH -> Nis'559)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'126
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'254
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'383)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'190
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'62
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'318)
                           | Coq_xH -> Nis'447)
                        | Coq_xH -> Nis'511)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'158
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'30
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'286)
                           | Coq_xH -> Nis'415)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'222
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'94
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'350)
                           | Coq_xH -> Nis'479)
                        | Coq_xH -> Nis'543)
                     | Coq_xH -> Nis'575)
                  | Coq_xH -> Nis'591)
               | Coq_xH -> Nis'599)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'106
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'234
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'363)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'170
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'42
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'298)
                           | Coq_xH -> Nis'427)
                        | Coq_xH -> Nis'491)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'138
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'10
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'266)
                           | Coq_xH -> Nis'395)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'202
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'74
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'330)
                           | Coq_xH -> Nis'459)
                        | Coq_xH -> Nis'523)
                     | Coq_xH -> Nis'555)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'122
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'250
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'379)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'186
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'58
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'314)
                           | Coq_xH -> Nis'443)
                        | Coq_xH -> Nis'507)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'154
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'26
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'282)
                           | Coq_xH -> Nis'411)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'218
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'90
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'346)
                           | Coq_xH -> Nis'475)
                        | Coq_xH -> Nis'539)
                     | Coq_xH -> Nis'571)
                  | Coq_xH -> Nis'587)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'114
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'242
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'371)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'178
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'50
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'306)
                           | Coq_xH -> Nis'435)
                        | Coq_xH -> Nis'499)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'146
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'18
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'274)
                           | Coq_xH -> Nis'403)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'210
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'82
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'338)
                           | Coq_xH -> Nis'467)
                        | Coq_xH -> Nis'531)
                     | Coq_xH -> Nis'563)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'130
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'2
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'258)
                           | Coq_xH -> Nis'387)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'194
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'66
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'322)
                           | Coq_xH -> Nis'451)
                        | Coq_xH -> Nis'515)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'162
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'34
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'290)
                           | Coq_xH -> Nis'419)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'226
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'98
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'354)
                           | Coq_xH -> Nis'483)
                        | Coq_xH -> Nis'547)
                     | Coq_xH -> Nis'579)
                  | Coq_xH -> Nis'595)
               | Coq_xH -> Nis'603)
            | Coq_xH -> Nis'607)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'104
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'232
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'361)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'168
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'40
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'296)
                           | Coq_xH -> Nis'425)
                        | Coq_xH -> Nis'489)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'136
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'8
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'264)
                           | Coq_xH -> Nis'393)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'200
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'72
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'328)
                           | Coq_xH -> Nis'457)
                        | Coq_xH -> Nis'521)
                     | Coq_xH -> Nis'553)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'120
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'248
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'377)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'184
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'56
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'312)
                           | Coq_xH -> Nis'441)
                        | Coq_xH -> Nis'505)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'152
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'24
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'280)
                           | Coq_xH -> Nis'409)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'216
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'88
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'344)
                           | Coq_xH -> Nis'473)
                        | Coq_xH -> Nis'537)
                     | Coq_xH -> Nis'569)
                  | Coq_xH -> Nis'585)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'112
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'240
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'369)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'176
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'48
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'304)
                           | Coq_xH -> Nis'433)
                        | Coq_xH -> Nis'497)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'144
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'16
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'272)
                           | Coq_xH -> Nis'401)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'208
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'80
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'336)
                           | Coq_xH -> Nis'465)
                        | Coq_xH -> Nis'529)
                     | Coq_xH -> Nis'561)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'128
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'256
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'385)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'192
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'64
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'320)
                           | Coq_xH -> Nis'449)
                        | Coq_xH -> Nis'513)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'160
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'32
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'288)
                           | Coq_xH -> Nis'417)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'224
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'96
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'352)
                           | Coq_xH -> Nis'481)
                        | Coq_xH -> Nis'545)
                     | Coq_xH -> Nis'577)
                  | Coq_xH -> Nis'593)
               | Coq_xH -> Nis'601)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'108
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'236
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'365)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'172
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'44
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'300)
                           | Coq_xH -> Nis'429)
                        | Coq_xH -> Nis'493)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'140
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'12
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'268)
                           | Coq_xH -> Nis'397)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'204
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'76
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'332)
                           | Coq_xH -> Nis'461)
                        | Coq_xH -> Nis'525)
                     | Coq_xH -> Nis'557)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'124
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'252
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'381)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'188
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'60
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'316)
                           | Coq_xH -> Nis'445)
                        | Coq_xH -> Nis'509)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'156
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'28
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'284)
                           | Coq_xH -> Nis'413)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'220
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'92
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'348)
                           | Coq_xH -> Nis'477)
                        | Coq_xH -> Nis'541)
                     | Coq_xH -> Nis'573)
                  | Coq_xH -> Nis'589)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'116
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'244
                              | _ -> Nis'612)
                           | Coq_xH -> Nis'373)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'180
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'52
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'308)
                           | Coq_xH -> Nis'437)
                        | Coq_xH -> Nis'501)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'148
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'20
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'276)
                           | Coq_xH -> Nis'405)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'212
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'84
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'340)
                           | Coq_xH -> Nis'469)
                        | Coq_xH -> Nis'533)
                     | Coq_xH -> Nis'565)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'132
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'4
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'260)
                           | Coq_xH -> Nis'389)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'196
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'68
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'324)
                           | Coq_xH -> Nis'453)
                        | Coq_xH -> Nis'517)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'164
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'36
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'292)
                           | Coq_xH -> Nis'421)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Nis'228
                              | _ -> Nis'612)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI _ -> Nis'612
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis'100
                                 | _ -> Nis'612)
                              | Coq_xH -> Nis'356)
                           | Coq_xH -> Nis'485)
                        | Coq_xH -> Nis'549)
                     | Coq_xH -> Nis'581)
                  | Coq_xH -> Nis'597)
               | Coq_xH -> Nis'605)
            | Coq_xH -> Nis'609)
         | Coq_xH -> Nis'611)
      | Coq_xH -> Nis'612); inj_bound = (Coq_xI (Coq_xI (Coq_xO (Coq_xO
      (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))))) }

  (** val coq_NonInitStateAlph : noninitstate coq_Alphabet **)

  let coq_NonInitStateAlph =
    coq_NumberedAlphabet noninitstateNum

  (** val last_symb_of_non_init_state : noninitstate -> Coq__2.symbol **)

  let last_symb_of_non_init_state = function
  | Nis'612 -> Coq__2.NT Coq__2.Coq_external_declaration'nt
  | Nis'611 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'610 -> Coq__2.NT Coq__2.Coq_compound_statement'nt
  | Nis'609 -> Coq__2.NT Coq__2.Coq_declarator'nt
  | Nis'608 -> Coq__2.NT Coq__2.Coq_attribute_specifier'nt
  | Nis'607 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'606 -> Coq__2.NT Coq__2.Coq_compound_statement'nt
  | Nis'605 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'604 -> Coq__2.NT Coq__2.Coq_block_item'nt
  | Nis'603 -> Coq__2.NT Coq__2.Coq_block_item'nt
  | Nis'602 -> Coq__2.T Coq__2.RBRACE't
  | Nis'601 -> Coq__2.NT Coq__2.Coq_block_item_list'nt
  | Nis'600 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'599 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'598 -> Coq__2.T Coq__2.PRAGMA't
  | Nis'597 -> Coq__2.T Coq__2.RBRACE't
  | Nis'596 -> Coq__2.T Coq__2.ELSE't
  | Nis'595 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'594 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'593 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'592 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'591 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'590 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'589 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'588 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'587 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'586 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'585 -> Coq__2.T Coq__2.ELSE't
  | Nis'584 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'583 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'581 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'580 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'578 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'577 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'576 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'574 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'573 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'571 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'570 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'569 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'567 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'566 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'564 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'563 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'562 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'560 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'559 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'557 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'556 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'555 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'554 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'552 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'551 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'549 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'548 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'547 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'545 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'544 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'543 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'542 -> Coq__2.NT Coq__2.Coq_asm_statement'nt
  | Nis'541 -> Coq__2.NT Coq__2.Coq_compound_statement'nt
  | Nis'540 -> Coq__2.NT Coq__2.Coq_expression_statement'nt
  | Nis'539 -> Coq__2.NT Coq__2.Coq_iteration_statement_statement_safe_'nt
  | Nis'538 -> Coq__2.NT Coq__2.Coq_jump_statement'nt
  | Nis'537 -> Coq__2.NT Coq__2.Coq_labeled_statement_statement_safe_'nt
  | Nis'536 -> Coq__2.NT Coq__2.Coq_selection_statement_safe'nt
  | Nis'535 -> Coq__2.NT Coq__2.Coq_statement_safe'nt
  | Nis'534 -> Coq__2.T Coq__2.COLON't
  | Nis'533 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'532 -> Coq__2.T Coq__2.CASE't
  | Nis'531 -> Coq__2.T Coq__2.COLON't
  | Nis'530 -> Coq__2.T Coq__2.DEFAULT't
  | Nis'529 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'527 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'526 -> Coq__2.T Coq__2.LPAREN't
  | Nis'525 -> Coq__2.T Coq__2.WHILE't
  | Nis'524 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'523 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'521 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'520 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'518 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'517 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'516 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'514 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'513 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'511 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'510 -> Coq__2.NT Coq__2.Coq_declaration'nt
  | Nis'509 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'507 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'506 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'504 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'503 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'502 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'500 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'499 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'497 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'496 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'495 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'494 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'492 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'491 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'489 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'488 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'487 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'485 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'484 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'483 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'481 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'480 -> Coq__2.T Coq__2.LPAREN't
  | Nis'479 -> Coq__2.T Coq__2.WHILE't
  | Nis'478 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'477 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'476 -> Coq__2.NT Coq__2.Coq_asm_statement'nt
  | Nis'475 -> Coq__2.NT Coq__2.Coq_compound_statement'nt
  | Nis'474 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'473 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'472 -> Coq__2.NT Coq__2.Coq_expression_statement'nt
  | Nis'471 ->
    Coq__2.NT Coq__2.Coq_iteration_statement_statement_dangerous_'nt
  | Nis'470 -> Coq__2.NT Coq__2.Coq_jump_statement'nt
  | Nis'469 -> Coq__2.NT Coq__2.Coq_labeled_statement_statement_dangerous_'nt
  | Nis'468 -> Coq__2.NT Coq__2.Coq_selection_statement_dangerous'nt
  | Nis'467 -> Coq__2.NT Coq__2.Coq_statement_dangerous'nt
  | Nis'466 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'464 -> Coq__2.NT Coq__2.Coq_asm_arguments'nt
  | Nis'463 -> Coq__2.NT Coq__2.Coq_asm_operand'nt
  | Nis'462 -> Coq__2.NT Coq__2.Coq_asm_flags'nt
  | Nis'461 -> Coq__2.NT Coq__2.Coq_asm_flags'nt
  | Nis'460 -> Coq__2.T Coq__2.COMMA't
  | Nis'459 -> Coq__2.T Coq__2.STRING_LITERAL't
  | Nis'458 -> Coq__2.T Coq__2.COLON't
  | Nis'457 -> Coq__2.NT Coq__2.Coq_asm_operands'nt
  | Nis'456 -> Coq__2.T Coq__2.COLON't
  | Nis'455 -> Coq__2.NT Coq__2.Coq_asm_operands'nt
  | Nis'453 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'452 -> Coq__2.T Coq__2.LPAREN't
  | Nis'451 -> Coq__2.T Coq__2.STRING_LITERAL't
  | Nis'450 -> Coq__2.NT Coq__2.Coq_asm_op_name'nt
  | Nis'449 -> Coq__2.NT Coq__2.Coq_asm_operand'nt
  | Nis'448 -> Coq__2.T Coq__2.COMMA't
  | Nis'447 -> Coq__2.NT Coq__2.Coq_asm_operands_ne'nt
  | Nis'446 -> Coq__2.T Coq__2.RBRACK't
  | Nis'445 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'444 -> Coq__2.T Coq__2.LBRACK't
  | Nis'443 -> Coq__2.T Coq__2.COLON't
  | Nis'442 -> Coq__2.T Coq__2.STRING_LITERAL't
  | Nis'441 -> Coq__2.T Coq__2.LPAREN't
  | Nis'440 -> Coq__2.NT Coq__2.Coq_asm_attributes'nt
  | Nis'439 -> Coq__2.NT Coq__2.Coq_asm_attributes'nt
  | Nis'438 -> Coq__2.NT Coq__2.Coq_asm_attributes'nt
  | Nis'437 -> Coq__2.T Coq__2.CONST't
  | Nis'436 -> Coq__2.T Coq__2.VOLATILE't
  | Nis'435 -> Coq__2.T Coq__2.ASM't
  | Nis'434 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'433 -> Coq__2.T Coq__2.BREAK't
  | Nis'432 -> Coq__2.T Coq__2.COLON't
  | Nis'431 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'430 -> Coq__2.T Coq__2.CASE't
  | Nis'429 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'428 -> Coq__2.T Coq__2.CONTINUE't
  | Nis'427 -> Coq__2.T Coq__2.COLON't
  | Nis'426 -> Coq__2.T Coq__2.DEFAULT't
  | Nis'425 -> Coq__2.T Coq__2.DO't
  | Nis'423 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'422 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'421 -> Coq__2.T Coq__2.LPAREN't
  | Nis'420 -> Coq__2.T Coq__2.FOR't
  | Nis'419 -> Coq__2.T Coq__2.DO't
  | Nis'417 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'416 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'415 -> Coq__2.T Coq__2.LPAREN't
  | Nis'414 -> Coq__2.T Coq__2.FOR't
  | Nis'413 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'412 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'411 -> Coq__2.T Coq__2.GOTO't
  | Nis'409 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'408 -> Coq__2.T Coq__2.LPAREN't
  | Nis'407 -> Coq__2.T Coq__2.IF_'t
  | Nis'406 -> Coq__2.T Coq__2.COLON't
  | Nis'405 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'403 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'402 -> Coq__2.T Coq__2.LPAREN't
  | Nis'401 -> Coq__2.T Coq__2.SWITCH't
  | Nis'399 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'398 -> Coq__2.T Coq__2.LPAREN't
  | Nis'397 -> Coq__2.T Coq__2.WHILE't
  | Nis'395 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'394 -> Coq__2.T Coq__2.LPAREN't
  | Nis'393 -> Coq__2.T Coq__2.IF_'t
  | Nis'392 -> Coq__2.T Coq__2.COLON't
  | Nis'391 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'390 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'389 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'388 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'387 -> Coq__2.T Coq__2.RETURN't
  | Nis'386 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'384 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'383 -> Coq__2.T Coq__2.LPAREN't
  | Nis'382 -> Coq__2.T Coq__2.SWITCH't
  | Nis'380 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'379 -> Coq__2.T Coq__2.LPAREN't
  | Nis'378 -> Coq__2.T Coq__2.WHILE't
  | Nis'377 -> Coq__2.T Coq__2.LBRACE't
  | Nis'376 -> Coq__2.NT Coq__2.Coq_declaration_list'nt
  | Nis'375 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'374 -> Coq__2.NT Coq__2.Coq_declarator_noattrend'nt
  | Nis'373 -> Coq__2.NT Coq__2.Coq_init_declarator'nt
  | Nis'372 -> Coq__2.NT Coq__2.Coq_c_initializer'nt
  | Nis'371 -> Coq__2.T Coq__2.EQ't
  | Nis'370 -> Coq__2.NT Coq__2.Coq_declarator'nt
  | Nis'369 -> Coq__2.NT Coq__2.Coq_init_declarator'nt
  | Nis'368 -> Coq__2.T Coq__2.COMMA't
  | Nis'367 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'366 -> Coq__2.NT Coq__2.Coq_init_declarator_list'nt
  | Nis'365 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'364 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'363 -> Coq__2.NT Coq__2.Coq_external_declaration'nt
  | Nis'362 -> Coq__2.NT Coq__2.Coq_function_definition'nt
  | Nis'361 -> Coq__2.T Coq__2.EOF't
  | Nis'360 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'359 -> Coq__2.NT Coq__2.Coq_translation_unit'nt
  | Nis'357 -> Coq__2.T Coq__2.EOF't
  | Nis'355 -> Coq__2.NT Coq__2.Coq_argument_expression_list'nt
  | Nis'354 -> Coq__2.NT Coq__2.Coq_unary_expression'nt
  | Nis'352 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'351 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'349 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'348 -> Coq__2.NT Coq__2.Coq_unary_expression'nt
  | Nis'346 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'345 -> Coq__2.T Coq__2.RBRACE't
  | Nis'344 -> Coq__2.T Coq__2.COMMA't
  | Nis'343 -> Coq__2.T Coq__2.RBRACE't
  | Nis'342 -> Coq__2.NT Coq__2.Coq_initializer_list'nt
  | Nis'341 -> Coq__2.NT Coq__2.Coq_c_initializer'nt
  | Nis'340 -> Coq__2.NT Coq__2.Coq_c_initializer'nt
  | Nis'339 -> Coq__2.NT Coq__2.Coq_designation'nt
  | Nis'338 -> Coq__2.NT Coq__2.Coq_c_initializer'nt
  | Nis'337 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'336 -> Coq__2.NT Coq__2.Coq_c_initializer'nt
  | Nis'335 -> Coq__2.NT Coq__2.Coq_designation'nt
  | Nis'334 -> Coq__2.T Coq__2.EQ't
  | Nis'333 -> Coq__2.NT Coq__2.Coq_designator_list'nt
  | Nis'332 -> Coq__2.T Coq__2.RBRACE't
  | Nis'331 -> Coq__2.T Coq__2.COMMA't
  | Nis'330 -> Coq__2.T Coq__2.RBRACE't
  | Nis'329 -> Coq__2.NT Coq__2.Coq_initializer_list'nt
  | Nis'328 -> Coq__2.T Coq__2.LBRACE't
  | Nis'327 -> Coq__2.T Coq__2.LBRACE't
  | Nis'325 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'324 -> Coq__2.T Coq__2.RBRACE't
  | Nis'323 -> Coq__2.T Coq__2.COMMA't
  | Nis'322 -> Coq__2.T Coq__2.RBRACE't
  | Nis'321 -> Coq__2.NT Coq__2.Coq_enumerator_list'nt
  | Nis'320 -> Coq__2.T Coq__2.LBRACE't
  | Nis'319 -> Coq__2.NT Coq__2.Coq_enumerator'nt
  | Nis'318 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'317 -> Coq__2.T Coq__2.EQ't
  | Nis'316 -> Coq__2.NT Coq__2.Coq_enumeration_constant'nt
  | Nis'315 -> Coq__2.NT Coq__2.Coq_enumerator'nt
  | Nis'314 -> Coq__2.T Coq__2.RBRACE't
  | Nis'313 -> Coq__2.T Coq__2.COMMA't
  | Nis'312 -> Coq__2.T Coq__2.RBRACE't
  | Nis'311 -> Coq__2.NT Coq__2.Coq_enumerator_list'nt
  | Nis'310 -> Coq__2.T Coq__2.VAR_NAME't
  | Nis'309 -> Coq__2.T Coq__2.LBRACE't
  | Nis'308 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'307 -> Coq__2.NT Coq__2.Coq_attribute_specifier_list'nt
  | Nis'306 -> Coq__2.NT Coq__2.Coq_gcc_attribute'nt
  | Nis'305 -> Coq__2.NT Coq__2.Coq_gcc_attribute'nt
  | Nis'304 -> Coq__2.T Coq__2.COMMA't
  | Nis'301 -> Coq__2.NT Coq__2.Coq_gcc_attribute_list'nt
  | Nis'299 -> Coq__2.NT Coq__2.Coq_argument_expression_list'nt
  | Nis'298 -> Coq__2.NT Coq__2.Coq_unary_expression'nt
  | Nis'296 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'295 -> Coq__2.T Coq__2.COMMA't
  | Nis'294 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'293 -> Coq__2.NT Coq__2.Coq_designator'nt
  | Nis'292 -> Coq__2.NT Coq__2.Coq_designator'nt
  | Nis'290 -> Coq__2.NT Coq__2.Coq_designator_list'nt
  | Nis'289 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'288 -> Coq__2.T Coq__2.DOT't
  | Nis'287 -> Coq__2.T Coq__2.RBRACK't
  | Nis'286 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'285 -> Coq__2.T Coq__2.LBRACK't
  | Nis'283 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'282 -> Coq__2.T Coq__2.COMMA't
  | Nis'281 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'279 -> Coq__2.NT Coq__2.Coq_argument_expression_list'nt
  | Nis'277 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'276 -> Coq__2.NT Coq__2.Coq_abstract_declarator'nt
  | Nis'275 -> Coq__2.NT Coq__2.Coq_pointer'nt
  | Nis'274 -> Coq__2.T Coq__2.LPAREN't
  | Nis'273 -> Coq__2.NT Coq__2.Coq_specifier_qualifier_list'nt
  | Nis'271 -> Coq__2.NT Coq__2.Coq_type_name'nt
  | Nis'270 -> Coq__2.NT Coq__2.Coq_specifier_qualifier_list'nt
  | Nis'269 -> Coq__2.NT Coq__2.Coq_specifier_qualifier_list'nt
  | Nis'268 -> Coq__2.T Coq__2.RBRACE't
  | Nis'267 -> Coq__2.NT Coq__2.Coq_struct_declaration_list'nt
  | Nis'266 -> Coq__2.T Coq__2.LBRACE't
  | Nis'265 -> Coq__2.NT Coq__2.Coq_struct_declarator'nt
  | Nis'264 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'263 -> Coq__2.T Coq__2.COLON't
  | Nis'262 -> Coq__2.NT Coq__2.Coq_declarator'nt
  | Nis'261 -> Coq__2.NT Coq__2.Coq_struct_declarator'nt
  | Nis'260 -> Coq__2.T Coq__2.COMMA't
  | Nis'259 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'258 -> Coq__2.NT Coq__2.Coq_struct_declarator_list'nt
  | Nis'257 -> Coq__2.NT Coq__2.Coq_conditional_expression'nt
  | Nis'256 -> Coq__2.NT Coq__2.Coq_constant_expression'nt
  | Nis'255 -> Coq__2.T Coq__2.COLON't
  | Nis'254 -> Coq__2.T Coq__2.VAR_NAME't
  | Nis'253 -> Coq__2.T Coq__2.COMMA't
  | Nis'251 -> Coq__2.NT Coq__2.Coq_identifier_list'nt
  | Nis'250 -> Coq__2.NT Coq__2.Coq_abstract_declarator'nt
  | Nis'249 -> Coq__2.NT Coq__2.Coq_declarator'nt
  | Nis'247 -> Coq__2.NT Coq__2.Coq_abstract_declarator'nt
  | Nis'245 -> Coq__2.NT Coq__2.Coq_declarator'nt
  | Nis'244 -> Coq__2.NT Coq__2.Coq_attribute_specifier_list'nt
  | Nis'243 -> Coq__2.NT Coq__2.Coq_attribute_specifier'nt
  | Nis'242 -> Coq__2.NT Coq__2.Coq_attribute_specifier_list'nt
  | Nis'241 -> Coq__2.NT Coq__2.Coq_declarator_noattrend'nt
  | Nis'240 -> Coq__2.NT Coq__2.Coq_direct_abstract_declarator'nt
  | Nis'239 -> Coq__2.T Coq__2.RBRACK't
  | Nis'238 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'237 -> Coq__2.T Coq__2.RBRACK't
  | Nis'236 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'235 -> Coq__2.T Coq__2.RBRACK't
  | Nis'234 -> Coq__2.NT Coq__2.Coq_type_qualifier_list'nt
  | Nis'233 -> Coq__2.T Coq__2.RBRACK't
  | Nis'232 -> Coq__2.T Coq__2.LBRACK't
  | Nis'231 -> Coq__2.NT Coq__2.Coq_direct_declarator'nt
  | Nis'229 -> Coq__2.NT Coq__2.Coq_parameter_type_list'nt
  | Nis'228 -> Coq__2.T Coq__2.RBRACK't
  | Nis'227 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'226 -> Coq__2.T Coq__2.RBRACK't
  | Nis'225 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'224 -> Coq__2.T Coq__2.RBRACK't
  | Nis'223 -> Coq__2.NT Coq__2.Coq_type_qualifier_list'nt
  | Nis'222 -> Coq__2.T Coq__2.RBRACK't
  | Nis'221 -> Coq__2.T Coq__2.LBRACK't
  | Nis'220 -> Coq__2.NT Coq__2.Coq_parameter_declaration'nt
  | Nis'218 -> Coq__2.NT Coq__2.Coq_parameter_type_list'nt
  | Nis'216 -> Coq__2.T Coq__2.LPAREN't
  | Nis'215 -> Coq__2.NT Coq__2.Coq_direct_abstract_declarator'nt
  | Nis'214 -> Coq__2.NT Coq__2.Coq_pointer'nt
  | Nis'213 -> Coq__2.T Coq__2.RBRACK't
  | Nis'212 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'211 -> Coq__2.T Coq__2.RBRACK't
  | Nis'210 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'209 -> Coq__2.T Coq__2.RBRACK't
  | Nis'208 -> Coq__2.NT Coq__2.Coq_type_qualifier_list'nt
  | Nis'207 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'206 -> Coq__2.T Coq__2.DEC't
  | Nis'205 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'204 -> Coq__2.T Coq__2.DOT't
  | Nis'203 -> Coq__2.T Coq__2.INC't
  | Nis'202 -> Coq__2.T Coq__2.RBRACK't
  | Nis'201 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'200 -> Coq__2.T Coq__2.LBRACK't
  | Nis'199 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'198 -> Coq__2.T Coq__2.COMMA't
  | Nis'196 -> Coq__2.NT Coq__2.Coq_argument_expression_list'nt
  | Nis'195 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'194 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'193 -> Coq__2.NT Coq__2.Coq_logical_AND_expression'nt
  | Nis'192 -> Coq__2.T Coq__2.BARBAR't
  | Nis'191 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'190 -> Coq__2.NT Coq__2.Coq_conditional_expression'nt
  | Nis'189 -> Coq__2.T Coq__2.COLON't
  | Nis'188 -> Coq__2.NT Coq__2.Coq_assignment_expression'nt
  | Nis'187 -> Coq__2.NT Coq__2.Coq_conditional_expression'nt
  | Nis'186 -> Coq__2.T Coq__2.COMMA't
  | Nis'185 -> Coq__2.NT Coq__2.Coq_expression'nt
  | Nis'184 -> Coq__2.NT Coq__2.Coq_inclusive_OR_expression'nt
  | Nis'183 -> Coq__2.NT Coq__2.Coq_exclusive_OR_expression'nt
  | Nis'182 -> Coq__2.NT Coq__2.AND_expression'nt
  | Nis'181 -> Coq__2.NT Coq__2.Coq_equality_expression'nt
  | Nis'180 -> Coq__2.T Coq__2.AND't
  | Nis'179 -> Coq__2.NT Coq__2.AND_expression'nt
  | Nis'178 -> Coq__2.NT Coq__2.Coq_relational_expression'nt
  | Nis'177 -> Coq__2.T Coq__2.EQEQ't
  | Nis'176 -> Coq__2.NT Coq__2.Coq_relational_expression'nt
  | Nis'175 -> Coq__2.T Coq__2.NEQ't
  | Nis'174 -> Coq__2.NT Coq__2.Coq_equality_expression'nt
  | Nis'173 -> Coq__2.T Coq__2.HAT't
  | Nis'172 -> Coq__2.NT Coq__2.Coq_exclusive_OR_expression'nt
  | Nis'171 -> Coq__2.T Coq__2.BAR't
  | Nis'170 -> Coq__2.NT Coq__2.Coq_inclusive_OR_expression'nt
  | Nis'169 -> Coq__2.T Coq__2.ANDAND't
  | Nis'168 -> Coq__2.NT Coq__2.Coq_logical_AND_expression'nt
  | Nis'167 -> Coq__2.T Coq__2.QUESTION't
  | Nis'166 -> Coq__2.NT Coq__2.Coq_logical_OR_expression'nt
  | Nis'165 -> Coq__2.NT Coq__2.Coq_shift_expression'nt
  | Nis'164 -> Coq__2.T Coq__2.GEQ't
  | Nis'163 -> Coq__2.NT Coq__2.Coq_shift_expression'nt
  | Nis'162 -> Coq__2.T Coq__2.GT't
  | Nis'161 -> Coq__2.NT Coq__2.Coq_shift_expression'nt
  | Nis'160 -> Coq__2.T Coq__2.LEQ't
  | Nis'159 -> Coq__2.NT Coq__2.Coq_additive_expression'nt
  | Nis'158 -> Coq__2.NT Coq__2.Coq_shift_expression'nt
  | Nis'157 -> Coq__2.T Coq__2.LT't
  | Nis'156 -> Coq__2.NT Coq__2.Coq_relational_expression'nt
  | Nis'155 -> Coq__2.NT Coq__2.Coq_additive_expression'nt
  | Nis'154 -> Coq__2.T Coq__2.LEFT't
  | Nis'153 -> Coq__2.NT Coq__2.Coq_multiplicative_expression'nt
  | Nis'152 -> Coq__2.T Coq__2.MINUS't
  | Nis'151 -> Coq__2.NT Coq__2.Coq_multiplicative_expression'nt
  | Nis'150 -> Coq__2.T Coq__2.PLUS't
  | Nis'149 -> Coq__2.NT Coq__2.Coq_additive_expression'nt
  | Nis'148 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'147 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'146 -> Coq__2.T Coq__2.PERCENT't
  | Nis'145 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'144 -> Coq__2.T Coq__2.SLASH't
  | Nis'143 -> Coq__2.NT Coq__2.Coq_cast_expression'nt
  | Nis'142 -> Coq__2.T Coq__2.STAR't
  | Nis'141 -> Coq__2.NT Coq__2.Coq_multiplicative_expression'nt
  | Nis'140 -> Coq__2.T Coq__2.RIGHT't
  | Nis'139 -> Coq__2.NT Coq__2.Coq_shift_expression'nt
  | Nis'138 -> Coq__2.NT Coq__2.Coq_assignment_operator'nt
  | Nis'137 -> Coq__2.T Coq__2.ADD_ASSIGN't
  | Nis'136 -> Coq__2.T Coq__2.AND_ASSIGN't
  | Nis'135 -> Coq__2.T Coq__2.DIV_ASSIGN't
  | Nis'134 -> Coq__2.T Coq__2.EQ't
  | Nis'133 -> Coq__2.T Coq__2.LEFT_ASSIGN't
  | Nis'132 -> Coq__2.T Coq__2.MOD_ASSIGN't
  | Nis'131 -> Coq__2.T Coq__2.MUL_ASSIGN't
  | Nis'130 -> Coq__2.T Coq__2.OR_ASSIGN't
  | Nis'129 -> Coq__2.T Coq__2.RIGHT_ASSIGN't
  | Nis'128 -> Coq__2.T Coq__2.SUB_ASSIGN't
  | Nis'127 -> Coq__2.T Coq__2.XOR_ASSIGN't
  | Nis'126 -> Coq__2.NT Coq__2.Coq_unary_expression'nt
  | Nis'124 -> Coq__2.T Coq__2.LPAREN't
  | Nis'123 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'122 -> Coq__2.T Coq__2.PTR't
  | Nis'121 -> Coq__2.NT Coq__2.Coq_postfix_expression'nt
  | Nis'120 -> Coq__2.NT Coq__2.Coq_primary_expression'nt
  | Nis'119 -> Coq__2.NT Coq__2.Coq_unary_expression'nt
  | Nis'118 -> Coq__2.NT Coq__2.Coq_unary_operator'nt
  | Nis'117 -> Coq__2.T Coq__2.RBRACK't
  | Nis'116 -> Coq__2.T Coq__2.LBRACK't
  | Nis'114 -> Coq__2.T Coq__2.LPAREN't
  | Nis'113 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'112 -> Coq__2.NT Coq__2.Coq_parameter_declaration'nt
  | Nis'111 -> Coq__2.T Coq__2.ELLIPSIS't
  | Nis'110 -> Coq__2.T Coq__2.COMMA't
  | Nis'109 -> Coq__2.NT Coq__2.Coq_parameter_list'nt
  | Nis'107 -> Coq__2.NT Coq__2.Coq_parameter_type_list'nt
  | Nis'106 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'105 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'104 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'103 -> Coq__2.NT Coq__2.Coq_attribute_specifier'nt
  | Nis'102 -> Coq__2.NT Coq__2.Coq_declaration_specifiers'nt
  | Nis'101 -> Coq__2.NT Coq__2.Coq_function_specifier'nt
  | Nis'100 -> Coq__2.NT Coq__2.Coq_storage_class_specifier'nt
  | Nis'99 -> Coq__2.NT Coq__2.Coq_type_qualifier_noattr'nt
  | Nis'98 -> Coq__2.NT Coq__2.Coq_declaration_specifiers_typespec_opt'nt
  | Nis'97 -> Coq__2.NT Coq__2.Coq_declaration_specifiers_typespec_opt'nt
  | Nis'96 -> Coq__2.NT Coq__2.Coq_declaration_specifiers_typespec_opt'nt
  | Nis'95 -> Coq__2.NT Coq__2.Coq_declaration_specifiers_typespec_opt'nt
  | Nis'94 -> Coq__2.NT Coq__2.Coq_declaration_specifiers_typespec_opt'nt
  | Nis'93 -> Coq__2.NT Coq__2.Coq_enum_specifier'nt
  | Nis'92 -> Coq__2.NT Coq__2.Coq_function_specifier'nt
  | Nis'91 -> Coq__2.NT Coq__2.Coq_storage_class_specifier'nt
  | Nis'90 -> Coq__2.NT Coq__2.Coq_type_qualifier'nt
  | Nis'89 -> Coq__2.NT Coq__2.Coq_type_specifier'nt
  | Nis'88 -> Coq__2.NT Coq__2.Coq_type_specifier'nt
  | Nis'87 -> Coq__2.T Coq__2.AUTO't
  | Nis'86 -> Coq__2.T Coq__2.EXTERN't
  | Nis'85 -> Coq__2.T Coq__2.INLINE't
  | Nis'84 -> Coq__2.T Coq__2.NORETURN't
  | Nis'82 -> Coq__2.T Coq__2.VAR_NAME't
  | Nis'81 -> Coq__2.T Coq__2.LPAREN't
  | Nis'80 -> Coq__2.NT Coq__2.Coq_direct_declarator'nt
  | Nis'79 -> Coq__2.NT Coq__2.Coq_pointer'nt
  | Nis'78 -> Coq__2.T Coq__2.LPAREN't
  | Nis'77 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'76 -> Coq__2.NT Coq__2.Coq_pointer'nt
  | Nis'75 -> Coq__2.NT Coq__2.Coq_type_qualifier'nt
  | Nis'74 -> Coq__2.NT Coq__2.Coq_attribute_specifier'nt
  | Nis'73 -> Coq__2.NT Coq__2.Coq_pointer'nt
  | Nis'72 -> Coq__2.NT Coq__2.Coq_type_qualifier'nt
  | Nis'71 -> Coq__2.NT Coq__2.Coq_type_qualifier_list'nt
  | Nis'70 -> Coq__2.T Coq__2.STAR't
  | Nis'69 -> Coq__2.T Coq__2.VAR_NAME't
  | Nis'68 -> Coq__2.NT Coq__2.Coq_specifier_qualifier_list'nt
  | Nis'67 -> Coq__2.NT Coq__2.Coq_struct_declaration'nt
  | Nis'66 -> Coq__2.T Coq__2.RBRACE't
  | Nis'65 -> Coq__2.NT Coq__2.Coq_struct_declaration_list'nt
  | Nis'64 -> Coq__2.T Coq__2.LBRACE't
  | Nis'63 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'62 -> Coq__2.NT Coq__2.Coq_attribute_specifier_list'nt
  | Nis'61 -> Coq__2.NT Coq__2.Coq_struct_or_union'nt
  | Nis'60 -> Coq__2.NT Coq__2.Coq_struct_or_union_specifier'nt
  | Nis'59 -> Coq__2.NT Coq__2.Coq_type_qualifier'nt
  | Nis'58 -> Coq__2.NT Coq__2.Coq_type_qualifier_noattr'nt
  | Nis'57 -> Coq__2.NT Coq__2.Coq_type_specifier'nt
  | Nis'56 -> Coq__2.T Coq__2.LPAREN't
  | Nis'55 -> Coq__2.T Coq__2.ALIGNOF't
  | Nis'54 -> Coq__2.T Coq__2.AND't
  | Nis'53 -> Coq__2.T Coq__2.BANG't
  | Nis'52 -> Coq__2.T Coq__2.LPAREN't
  | Nis'51 -> Coq__2.T Coq__2.ALIGNAS't
  | Nis'50 -> Coq__2.T Coq__2.CHAR't
  | Nis'49 -> Coq__2.T Coq__2.CONST't
  | Nis'48 -> Coq__2.T Coq__2.DOUBLE't
  | Nis'47 -> Coq__2.T Coq__2.LPAREN't
  | Nis'46 -> Coq__2.T Coq__2.BUILTIN_OFFSETOF't
  | Nis'45 -> Coq__2.T Coq__2.LPAREN't
  | Nis'44 -> Coq__2.T Coq__2.BUILTIN_VA_ARG't
  | Nis'43 -> Coq__2.T Coq__2.CONSTANT't
  | Nis'42 -> Coq__2.T Coq__2.DEC't
  | Nis'40 -> Coq__2.T Coq__2.LPAREN't
  | Nis'39 -> Coq__2.NT Coq__2.Coq_gcc_attribute_word'nt
  | Nis'38 -> Coq__2.T Coq__2.CONST't
  | Nis'37 -> Coq__2.T Coq__2.OTHER_NAME't
  | Nis'36 -> Coq__2.T Coq__2.PACKED't
  | Nis'35 -> Coq__2.T Coq__2.LPAREN't
  | Nis'34 -> Coq__2.T Coq__2.LPAREN't
  | Nis'33 -> Coq__2.T Coq__2.ATTRIBUTE't
  | Nis'32 -> Coq__2.T Coq__2.ENUM't
  | Nis'31 -> Coq__2.T Coq__2.FLOAT't
  | Nis'30 -> Coq__2.T Coq__2.LPAREN't
  | Nis'29 -> Coq__2.T Coq__2.INC't
  | Nis'28 -> Coq__2.T Coq__2.INT't
  | Nis'27 -> Coq__2.T Coq__2.LONG't
  | Nis'26 -> Coq__2.T Coq__2.LPAREN't
  | Nis'25 -> Coq__2.T Coq__2.LPAREN't
  | Nis'24 -> Coq__2.T Coq__2.MINUS't
  | Nis'23 -> Coq__2.T Coq__2.PLUS't
  | Nis'22 -> Coq__2.T Coq__2.SIZEOF't
  | Nis'21 -> Coq__2.T Coq__2.STAR't
  | Nis'20 -> Coq__2.T Coq__2.STRING_LITERAL't
  | Nis'19 -> Coq__2.T Coq__2.TILDE't
  | Nis'18 -> Coq__2.T Coq__2.VAR_NAME't
  | Nis'17 -> Coq__2.T Coq__2.LPAREN't
  | Nis'16 -> Coq__2.T Coq__2.PACKED't
  | Nis'15 -> Coq__2.T Coq__2.PRAGMA't
  | Nis'14 -> Coq__2.T Coq__2.REGISTER't
  | Nis'13 -> Coq__2.T Coq__2.RESTRICT't
  | Nis'12 -> Coq__2.T Coq__2.SEMICOLON't
  | Nis'11 -> Coq__2.T Coq__2.SHORT't
  | Nis'10 -> Coq__2.T Coq__2.SIGNED't
  | Nis'9 -> Coq__2.T Coq__2.STATIC't
  | Nis'8 -> Coq__2.T Coq__2.STRUCT't
  | Nis'7 -> Coq__2.T Coq__2.TYPEDEF't
  | Nis'6 -> Coq__2.T Coq__2.TYPEDEF_NAME't
  | Nis'5 -> Coq__2.T Coq__2.UNDERSCORE_BOOL't
  | Nis'4 -> Coq__2.T Coq__2.UNION't
  | Nis'3 -> Coq__2.T Coq__2.UNSIGNED't
  | Nis'2 -> Coq__2.T Coq__2.VOID't
  | Nis'1 -> Coq__2.T Coq__2.VOLATILE't
  | _ -> Coq__2.T Coq__2.RPAREN't

  type initstate' =
  | Init'0

  type initstate = initstate'

  (** val initstateNum : initstate coq_Numbered **)

  let initstateNum =
    { inj = (fun _ -> Coq_xH); surj = (fun _ -> Init'0); inj_bound = Coq_xH }

  (** val coq_InitStateAlph : initstate coq_Alphabet **)

  let coq_InitStateAlph =
    coq_NumberedAlphabet initstateNum

  type state =
  | Init of initstate
  | Ninit of noninitstate

  (** val state_rect :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rect f f0 = function
  | Init x -> f x
  | Ninit x -> f0 x

  (** val state_rec :
      (initstate -> 'a1) -> (noninitstate -> 'a1) -> state -> 'a1 **)

  let state_rec f f0 = function
  | Init x -> f x
  | Ninit x -> f0 x

  (** val coq_StateAlph : state coq_Alphabet **)

  let coq_StateAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | Init x0 ->
        (match y with
         | Init y0 -> compare coq_InitStateAlph.coq_AlphabetComparable x0 y0
         | Ninit _ -> Lt)
      | Ninit x0 ->
        (match y with
         | Init _ -> Gt
         | Ninit y0 ->
           compare coq_NonInitStateAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app
        (map (fun x -> Init x)
          (all_list coq_InitStateAlph.coq_AlphabetFinite))
        (map (fun x -> Ninit x)
          (all_list coq_NonInitStateAlph.coq_AlphabetFinite))) }

  type lookahead_action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act

  (** val lookahead_action_rect :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rect _ f f0 f1 = function
  | Shift_act x -> f x __
  | Reduce_act x -> f0 x
  | Fail_act -> f1

  (** val lookahead_action_rec :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> lookahead_action -> 'a1 **)

  let lookahead_action_rec _ f f0 f1 = function
  | Shift_act x -> f x __
  | Reduce_act x -> f0 x
  | Fail_act -> f1

  type action =
  | Default_reduce_act of Gram.production
  | Lookahead_act of (Gram.terminal -> lookahead_action)

  (** val action_rect :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rect f f0 = function
  | Default_reduce_act x -> f x
  | Lookahead_act x -> f0 x

  (** val action_rec :
      (Gram.production -> 'a1) -> ((Gram.terminal -> lookahead_action) ->
      'a1) -> action -> 'a1 **)

  let action_rec f f0 = function
  | Default_reduce_act x -> f x
  | Lookahead_act x -> f0 x

  type item = { prod_item : Gram.production; dot_pos_item : nat;
                lookaheads_item : Gram.terminal list }

  (** val prod_item : item -> Gram.production **)

  let prod_item i =
    i.prod_item

  (** val dot_pos_item : item -> nat **)

  let dot_pos_item i =
    i.dot_pos_item

  (** val lookaheads_item : item -> Gram.terminal list **)

  let lookaheads_item i =
    i.lookaheads_item

  (** val start_nt : initstate -> Coq__2.nonterminal **)

  let start_nt _ =
    Coq__2.Coq_translation_unit_file'nt

  (** val action_table : state -> action **)

  let action_table = function
  | Init _ ->
    Lookahead_act (fun terminal0 ->
      match terminal0 with
      | Coq__2.ALIGNAS't -> Shift_act Nis'51
      | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
      | Coq__2.AUTO't -> Shift_act Nis'87
      | Coq__2.CHAR't -> Shift_act Nis'50
      | Coq__2.CONST't -> Shift_act Nis'49
      | Coq__2.DOUBLE't -> Shift_act Nis'48
      | Coq__2.ENUM't -> Shift_act Nis'32
      | Coq__2.EOF't -> Shift_act Nis'357
      | Coq__2.EXTERN't -> Shift_act Nis'86
      | Coq__2.FLOAT't -> Shift_act Nis'31
      | Coq__2.INLINE't -> Shift_act Nis'85
      | Coq__2.INT't -> Shift_act Nis'28
      | Coq__2.LONG't -> Shift_act Nis'27
      | Coq__2.NORETURN't -> Shift_act Nis'84
      | Coq__2.PACKED't -> Shift_act Nis'16
      | Coq__2.PRAGMA't -> Shift_act Nis'15
      | Coq__2.REGISTER't -> Shift_act Nis'14
      | Coq__2.RESTRICT't -> Shift_act Nis'13
      | Coq__2.SEMICOLON't -> Shift_act Nis'12
      | Coq__2.SHORT't -> Shift_act Nis'11
      | Coq__2.SIGNED't -> Shift_act Nis'10
      | Coq__2.STATIC't -> Shift_act Nis'9
      | Coq__2.STRUCT't -> Shift_act Nis'8
      | Coq__2.TYPEDEF't -> Shift_act Nis'7
      | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
      | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
      | Coq__2.UNION't -> Shift_act Nis'4
      | Coq__2.UNSIGNED't -> Shift_act Nis'3
      | Coq__2.VOID't -> Shift_act Nis'2
      | Coq__2.VOLATILE't -> Shift_act Nis'1
      | _ -> Fail_act)
  | Ninit n ->
    (match n with
     | Nis'612 -> Default_reduce_act Coq__2.Prod'translation_unit'0
     | Nis'611 -> Default_reduce_act Coq__2.Prod'external_declaration'1
     | Nis'610 -> Default_reduce_act Coq__2.Prod'function_definition'1
     | Nis'609 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'init_declarator'0
         | Coq__2.EQ't -> Shift_act Nis'371
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'init_declarator'0
         | _ -> Fail_act)
     | Nis'608 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACE't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'607 -> Default_reduce_act Coq__2.Prod'declaration_list'0
     | Nis'606 -> Default_reduce_act Coq__2.Prod'function_definition'0
     | Nis'605 -> Default_reduce_act Coq__2.Prod'declaration_list'1
     | Nis'604 -> Default_reduce_act Coq__2.Prod'block_item_list'0
     | Nis'603 -> Default_reduce_act Coq__2.Prod'block_item_list'1
     | Nis'602 -> Default_reduce_act Coq__2.Prod'compound_statement'0
     | Nis'601 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.PRAGMA't -> Shift_act Nis'598
         | Coq__2.RBRACE't -> Shift_act Nis'602
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'600 -> Default_reduce_act Coq__2.Prod'block_item'0
     | Nis'599 -> Default_reduce_act Coq__2.Prod'block_item'1
     | Nis'598 -> Default_reduce_act Coq__2.Prod'block_item'2
     | Nis'597 -> Default_reduce_act Coq__2.Prod'compound_statement'1
     | Nis'596 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'595 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ELSE't -> Shift_act Nis'596
         | _ -> Fail_act)
     | Nis'594 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'0
     | Nis'593 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'0
     | Nis'592 ->
       Default_reduce_act Coq__2.Prod'selection_statement_dangerous'2
     | Nis'591 -> Default_reduce_act Coq__2.Prod'selection_statement_safe'1
     | Nis'590 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_dangerous_'0
     | Nis'589 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_safe_'0
     | Nis'588 ->
       Default_reduce_act Coq__2.Prod'selection_statement_dangerous'0
     | Nis'587 ->
       Default_reduce_act Coq__2.Prod'selection_statement_dangerous'1
     | Nis'586 -> Default_reduce_act Coq__2.Prod'selection_statement_safe'0
     | Nis'585 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'584 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ELSE't -> Shift_act Nis'585
         | _ -> Fail_act)
     | Nis'583 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'3
     | Nis'582 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'581 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'582
         | _ -> Fail_act)
     | Nis'580 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'9
     | Nis'579 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'578 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'579
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'577 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'578
         | _ -> Fail_act)
     | Nis'576 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'6
     | Nis'575 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'574 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'575
         | _ -> Fail_act)
     | Nis'573 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'12
     | Nis'572 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'571 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'572
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'570 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'571
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'569 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'2
     | Nis'568 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'567 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'568
         | _ -> Fail_act)
     | Nis'566 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'8
     | Nis'565 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'564 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'565
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'563 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'564
         | _ -> Fail_act)
     | Nis'562 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'5
     | Nis'561 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'560 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'561
         | _ -> Fail_act)
     | Nis'559 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'11
     | Nis'558 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'557 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'558
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'556 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'557
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'555 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'556
         | _ -> Fail_act)
     | Nis'554 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'4
     | Nis'553 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'552 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'553
         | _ -> Fail_act)
     | Nis'551 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'10
     | Nis'550 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'549 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'550
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'548 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'549
         | _ -> Fail_act)
     | Nis'547 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'7
     | Nis'546 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'545 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'546
         | _ -> Fail_act)
     | Nis'544 ->
       Default_reduce_act Coq__2.Prod'iteration_statement_statement_safe_'13
     | Nis'543 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_safe_'2
     | Nis'542 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Fail_act
         | Coq__2.ANDAND't -> Fail_act
         | Coq__2.AND_ASSIGN't -> Fail_act
         | Coq__2.BAR't -> Fail_act
         | Coq__2.BARBAR't -> Fail_act
         | Coq__2.COLON't -> Fail_act
         | Coq__2.COMMA't -> Fail_act
         | Coq__2.DIV_ASSIGN't -> Fail_act
         | Coq__2.DOT't -> Fail_act
         | Coq__2.ELLIPSIS't -> Fail_act
         | Coq__2.ELSE't -> Reduce_act Coq__2.Prod'statement_safe'6
         | Coq__2.EOF't -> Fail_act
         | Coq__2.EQ't -> Fail_act
         | Coq__2.EQEQ't -> Fail_act
         | Coq__2.GEQ't -> Fail_act
         | Coq__2.GT't -> Fail_act
         | Coq__2.HAT't -> Fail_act
         | Coq__2.LBRACK't -> Fail_act
         | Coq__2.LEFT't -> Fail_act
         | Coq__2.LEFT_ASSIGN't -> Fail_act
         | Coq__2.LEQ't -> Fail_act
         | Coq__2.LT't -> Fail_act
         | Coq__2.MOD_ASSIGN't -> Fail_act
         | Coq__2.MUL_ASSIGN't -> Fail_act
         | Coq__2.NEQ't -> Fail_act
         | Coq__2.OR_ASSIGN't -> Fail_act
         | Coq__2.PERCENT't -> Fail_act
         | Coq__2.PTR't -> Fail_act
         | Coq__2.QUESTION't -> Fail_act
         | Coq__2.RBRACK't -> Fail_act
         | Coq__2.RIGHT't -> Fail_act
         | Coq__2.RIGHT_ASSIGN't -> Fail_act
         | Coq__2.RPAREN't -> Fail_act
         | Coq__2.SLASH't -> Fail_act
         | Coq__2.SUB_ASSIGN't -> Fail_act
         | Coq__2.XOR_ASSIGN't -> Fail_act
         | _ -> Reduce_act Coq__2.Prod'statement_dangerous'6)
     | Nis'541 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Fail_act
         | Coq__2.ANDAND't -> Fail_act
         | Coq__2.AND_ASSIGN't -> Fail_act
         | Coq__2.BAR't -> Fail_act
         | Coq__2.BARBAR't -> Fail_act
         | Coq__2.COLON't -> Fail_act
         | Coq__2.COMMA't -> Fail_act
         | Coq__2.DIV_ASSIGN't -> Fail_act
         | Coq__2.DOT't -> Fail_act
         | Coq__2.ELLIPSIS't -> Fail_act
         | Coq__2.ELSE't -> Reduce_act Coq__2.Prod'statement_safe'1
         | Coq__2.EOF't -> Fail_act
         | Coq__2.EQ't -> Fail_act
         | Coq__2.EQEQ't -> Fail_act
         | Coq__2.GEQ't -> Fail_act
         | Coq__2.GT't -> Fail_act
         | Coq__2.HAT't -> Fail_act
         | Coq__2.LBRACK't -> Fail_act
         | Coq__2.LEFT't -> Fail_act
         | Coq__2.LEFT_ASSIGN't -> Fail_act
         | Coq__2.LEQ't -> Fail_act
         | Coq__2.LT't -> Fail_act
         | Coq__2.MOD_ASSIGN't -> Fail_act
         | Coq__2.MUL_ASSIGN't -> Fail_act
         | Coq__2.NEQ't -> Fail_act
         | Coq__2.OR_ASSIGN't -> Fail_act
         | Coq__2.PERCENT't -> Fail_act
         | Coq__2.PTR't -> Fail_act
         | Coq__2.QUESTION't -> Fail_act
         | Coq__2.RBRACK't -> Fail_act
         | Coq__2.RIGHT't -> Fail_act
         | Coq__2.RIGHT_ASSIGN't -> Fail_act
         | Coq__2.RPAREN't -> Fail_act
         | Coq__2.SLASH't -> Fail_act
         | Coq__2.SUB_ASSIGN't -> Fail_act
         | Coq__2.XOR_ASSIGN't -> Fail_act
         | _ -> Reduce_act Coq__2.Prod'statement_dangerous'1)
     | Nis'540 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Fail_act
         | Coq__2.ANDAND't -> Fail_act
         | Coq__2.AND_ASSIGN't -> Fail_act
         | Coq__2.BAR't -> Fail_act
         | Coq__2.BARBAR't -> Fail_act
         | Coq__2.COLON't -> Fail_act
         | Coq__2.COMMA't -> Fail_act
         | Coq__2.DIV_ASSIGN't -> Fail_act
         | Coq__2.DOT't -> Fail_act
         | Coq__2.ELLIPSIS't -> Fail_act
         | Coq__2.ELSE't -> Reduce_act Coq__2.Prod'statement_safe'2
         | Coq__2.EOF't -> Fail_act
         | Coq__2.EQ't -> Fail_act
         | Coq__2.EQEQ't -> Fail_act
         | Coq__2.GEQ't -> Fail_act
         | Coq__2.GT't -> Fail_act
         | Coq__2.HAT't -> Fail_act
         | Coq__2.LBRACK't -> Fail_act
         | Coq__2.LEFT't -> Fail_act
         | Coq__2.LEFT_ASSIGN't -> Fail_act
         | Coq__2.LEQ't -> Fail_act
         | Coq__2.LT't -> Fail_act
         | Coq__2.MOD_ASSIGN't -> Fail_act
         | Coq__2.MUL_ASSIGN't -> Fail_act
         | Coq__2.NEQ't -> Fail_act
         | Coq__2.OR_ASSIGN't -> Fail_act
         | Coq__2.PERCENT't -> Fail_act
         | Coq__2.PTR't -> Fail_act
         | Coq__2.QUESTION't -> Fail_act
         | Coq__2.RBRACK't -> Fail_act
         | Coq__2.RIGHT't -> Fail_act
         | Coq__2.RIGHT_ASSIGN't -> Fail_act
         | Coq__2.RPAREN't -> Fail_act
         | Coq__2.SLASH't -> Fail_act
         | Coq__2.SUB_ASSIGN't -> Fail_act
         | Coq__2.XOR_ASSIGN't -> Fail_act
         | _ -> Reduce_act Coq__2.Prod'statement_dangerous'2)
     | Nis'539 -> Default_reduce_act Coq__2.Prod'statement_safe'4
     | Nis'538 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Fail_act
         | Coq__2.ANDAND't -> Fail_act
         | Coq__2.AND_ASSIGN't -> Fail_act
         | Coq__2.BAR't -> Fail_act
         | Coq__2.BARBAR't -> Fail_act
         | Coq__2.COLON't -> Fail_act
         | Coq__2.COMMA't -> Fail_act
         | Coq__2.DIV_ASSIGN't -> Fail_act
         | Coq__2.DOT't -> Fail_act
         | Coq__2.ELLIPSIS't -> Fail_act
         | Coq__2.ELSE't -> Reduce_act Coq__2.Prod'statement_safe'5
         | Coq__2.EOF't -> Fail_act
         | Coq__2.EQ't -> Fail_act
         | Coq__2.EQEQ't -> Fail_act
         | Coq__2.GEQ't -> Fail_act
         | Coq__2.GT't -> Fail_act
         | Coq__2.HAT't -> Fail_act
         | Coq__2.LBRACK't -> Fail_act
         | Coq__2.LEFT't -> Fail_act
         | Coq__2.LEFT_ASSIGN't -> Fail_act
         | Coq__2.LEQ't -> Fail_act
         | Coq__2.LT't -> Fail_act
         | Coq__2.MOD_ASSIGN't -> Fail_act
         | Coq__2.MUL_ASSIGN't -> Fail_act
         | Coq__2.NEQ't -> Fail_act
         | Coq__2.OR_ASSIGN't -> Fail_act
         | Coq__2.PERCENT't -> Fail_act
         | Coq__2.PTR't -> Fail_act
         | Coq__2.QUESTION't -> Fail_act
         | Coq__2.RBRACK't -> Fail_act
         | Coq__2.RIGHT't -> Fail_act
         | Coq__2.RIGHT_ASSIGN't -> Fail_act
         | Coq__2.RPAREN't -> Fail_act
         | Coq__2.SLASH't -> Fail_act
         | Coq__2.SUB_ASSIGN't -> Fail_act
         | Coq__2.XOR_ASSIGN't -> Fail_act
         | _ -> Reduce_act Coq__2.Prod'statement_dangerous'5)
     | Nis'537 -> Default_reduce_act Coq__2.Prod'statement_safe'0
     | Nis'536 -> Default_reduce_act Coq__2.Prod'statement_safe'3
     | Nis'535 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_safe_'1
     | Nis'534 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'533 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'534
         | _ -> Fail_act)
     | Nis'531 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'530 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'531
         | _ -> Fail_act)
     | Nis'529 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Fail_act
         | Coq__2.ANDAND't -> Fail_act
         | Coq__2.AND_ASSIGN't -> Fail_act
         | Coq__2.BAR't -> Fail_act
         | Coq__2.BARBAR't -> Fail_act
         | Coq__2.COLON't -> Fail_act
         | Coq__2.COMMA't -> Fail_act
         | Coq__2.DIV_ASSIGN't -> Fail_act
         | Coq__2.DOT't -> Fail_act
         | Coq__2.ELLIPSIS't -> Fail_act
         | Coq__2.ELSE't ->
           Reduce_act Coq__2.Prod'iteration_statement_statement_safe_'1
         | Coq__2.EOF't -> Fail_act
         | Coq__2.EQ't -> Fail_act
         | Coq__2.EQEQ't -> Fail_act
         | Coq__2.GEQ't -> Fail_act
         | Coq__2.GT't -> Fail_act
         | Coq__2.HAT't -> Fail_act
         | Coq__2.LBRACK't -> Fail_act
         | Coq__2.LEFT't -> Fail_act
         | Coq__2.LEFT_ASSIGN't -> Fail_act
         | Coq__2.LEQ't -> Fail_act
         | Coq__2.LT't -> Fail_act
         | Coq__2.MOD_ASSIGN't -> Fail_act
         | Coq__2.MUL_ASSIGN't -> Fail_act
         | Coq__2.NEQ't -> Fail_act
         | Coq__2.OR_ASSIGN't -> Fail_act
         | Coq__2.PERCENT't -> Fail_act
         | Coq__2.PTR't -> Fail_act
         | Coq__2.QUESTION't -> Fail_act
         | Coq__2.RBRACK't -> Fail_act
         | Coq__2.RIGHT't -> Fail_act
         | Coq__2.RIGHT_ASSIGN't -> Fail_act
         | Coq__2.RPAREN't -> Fail_act
         | Coq__2.SLASH't -> Fail_act
         | Coq__2.SUB_ASSIGN't -> Fail_act
         | Coq__2.XOR_ASSIGN't -> Fail_act
         | _ ->
           Reduce_act Coq__2.Prod'iteration_statement_statement_dangerous_'1)
     | Nis'528 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'529
         | _ -> Fail_act)
     | Nis'527 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'528
         | _ -> Fail_act)
     | Nis'525 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'526
         | _ -> Fail_act)
     | Nis'524 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.WHILE't -> Shift_act Nis'525
         | _ -> Fail_act)
     | Nis'523 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'3
     | Nis'522 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'521 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'522
         | _ -> Fail_act)
     | Nis'520 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'9
     | Nis'519 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'518 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'519
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'517 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'518
         | _ -> Fail_act)
     | Nis'516 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'6
     | Nis'515 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'514 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'515
         | _ -> Fail_act)
     | Nis'513 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'12
     | Nis'512 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'511 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'512
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'510 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'511
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'509 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'2
     | Nis'508 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'507 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'508
         | _ -> Fail_act)
     | Nis'506 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'8
     | Nis'505 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'504 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'505
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'503 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'504
         | _ -> Fail_act)
     | Nis'502 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'5
     | Nis'501 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'500 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'501
         | _ -> Fail_act)
     | Nis'499 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'11
     | Nis'498 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'497 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'498
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'496 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'497
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'495 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'496
         | _ -> Fail_act)
     | Nis'494 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'4
     | Nis'493 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'492 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'493
         | _ -> Fail_act)
     | Nis'491 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'10
     | Nis'490 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'489 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'490
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'488 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'489
         | _ -> Fail_act)
     | Nis'487 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'7
     | Nis'486 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'485 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'486
         | _ -> Fail_act)
     | Nis'484 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'13
     | Nis'483 ->
       Default_reduce_act
         Coq__2.Prod'iteration_statement_statement_dangerous_'1
     | Nis'482 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'483
         | _ -> Fail_act)
     | Nis'481 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'482
         | _ -> Fail_act)
     | Nis'479 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'480
         | _ -> Fail_act)
     | Nis'478 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.WHILE't -> Shift_act Nis'479
         | _ -> Fail_act)
     | Nis'477 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_dangerous_'2
     | Nis'476 -> Default_reduce_act Coq__2.Prod'statement_dangerous'6
     | Nis'475 -> Default_reduce_act Coq__2.Prod'statement_dangerous'1
     | Nis'474 -> Default_reduce_act Coq__2.Prod'expression_statement'0
     | Nis'473 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'474
         | _ -> Fail_act)
     | Nis'472 -> Default_reduce_act Coq__2.Prod'statement_dangerous'2
     | Nis'471 -> Default_reduce_act Coq__2.Prod'statement_dangerous'4
     | Nis'470 -> Default_reduce_act Coq__2.Prod'statement_dangerous'5
     | Nis'469 -> Default_reduce_act Coq__2.Prod'statement_dangerous'0
     | Nis'468 -> Default_reduce_act Coq__2.Prod'statement_dangerous'3
     | Nis'467 ->
       Default_reduce_act Coq__2.Prod'labeled_statement_statement_dangerous_'1
     | Nis'466 -> Default_reduce_act Coq__2.Prod'asm_statement'0
     | Nis'465 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'466
         | _ -> Fail_act)
     | Nis'464 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'465
         | _ -> Fail_act)
     | Nis'463 -> Default_reduce_act Coq__2.Prod'asm_operands_ne'1
     | Nis'462 -> Default_reduce_act Coq__2.Prod'asm_arguments'3
     | Nis'461 -> Default_reduce_act Coq__2.Prod'asm_flags'1
     | Nis'460 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'459
         | _ -> Fail_act)
     | Nis'459 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'460
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_flags'0
         | _ -> Fail_act)
     | Nis'458 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'459
         | _ -> Fail_act)
     | Nis'457 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'458
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_arguments'2
         | _ -> Fail_act)
     | Nis'456 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'asm_operands'0
         | Coq__2.LBRACK't -> Shift_act Nis'444
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_operands'0
         | Coq__2.STRING_LITERAL't -> Reduce_act Coq__2.Prod'asm_op_name'0
         | _ -> Fail_act)
     | Nis'455 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'456
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_arguments'1
         | _ -> Fail_act)
     | Nis'454 -> Default_reduce_act Coq__2.Prod'asm_operand'0
     | Nis'453 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'454
         | _ -> Fail_act)
     | Nis'451 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'452
         | _ -> Fail_act)
     | Nis'450 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'451
         | _ -> Fail_act)
     | Nis'449 -> Default_reduce_act Coq__2.Prod'asm_operands_ne'0
     | Nis'448 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LBRACK't -> Shift_act Nis'444
         | Coq__2.STRING_LITERAL't -> Reduce_act Coq__2.Prod'asm_op_name'0
         | _ -> Fail_act)
     | Nis'447 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'asm_operands'1
         | Coq__2.COMMA't -> Shift_act Nis'448
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_operands'1
         | _ -> Fail_act)
     | Nis'446 -> Default_reduce_act Coq__2.Prod'asm_op_name'1
     | Nis'445 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'446
         | _ -> Fail_act)
     | Nis'444 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'445
         | _ -> Fail_act)
     | Nis'443 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'asm_operands'0
         | Coq__2.LBRACK't -> Shift_act Nis'444
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_operands'0
         | Coq__2.STRING_LITERAL't -> Reduce_act Coq__2.Prod'asm_op_name'0
         | _ -> Fail_act)
     | Nis'442 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'443
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'asm_arguments'0
         | _ -> Fail_act)
     | Nis'441 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'442
         | _ -> Fail_act)
     | Nis'440 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'441
         | _ -> Fail_act)
     | Nis'439 -> Default_reduce_act Coq__2.Prod'asm_attributes'2
     | Nis'438 -> Default_reduce_act Coq__2.Prod'asm_attributes'1
     | Nis'437 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.CONST't -> Shift_act Nis'437
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'asm_attributes'0
         | Coq__2.VOLATILE't -> Shift_act Nis'436
         | _ -> Fail_act)
     | Nis'436 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.CONST't -> Shift_act Nis'437
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'asm_attributes'0
         | Coq__2.VOLATILE't -> Shift_act Nis'436
         | _ -> Fail_act)
     | Nis'435 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.CONST't -> Shift_act Nis'437
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'asm_attributes'0
         | Coq__2.VOLATILE't -> Shift_act Nis'436
         | _ -> Fail_act)
     | Nis'434 -> Default_reduce_act Coq__2.Prod'jump_statement'2
     | Nis'433 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'434
         | _ -> Fail_act)
     | Nis'432 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'431 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'432
         | _ -> Fail_act)
     | Nis'429 -> Default_reduce_act Coq__2.Prod'jump_statement'1
     | Nis'428 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'429
         | _ -> Fail_act)
     | Nis'427 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'426 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'427
         | _ -> Fail_act)
     | Nis'425 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'424 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'423 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'424
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'422 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'423
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'421 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SEMICOLON't -> Shift_act Nis'422
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'420 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'421
         | _ -> Fail_act)
     | Nis'419 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'418 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'417 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'418
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'416 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'417
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'415 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SEMICOLON't -> Shift_act Nis'416
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'414 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'415
         | _ -> Fail_act)
     | Nis'413 -> Default_reduce_act Coq__2.Prod'jump_statement'0
     | Nis'412 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.SEMICOLON't -> Shift_act Nis'413
         | _ -> Fail_act)
     | Nis'411 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'412
         | _ -> Fail_act)
     | Nis'410 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'409 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'410
         | _ -> Fail_act)
     | Nis'407 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'408
         | _ -> Fail_act)
     | Nis'406 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'405 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'406
         | _ -> Fail_act)
     | Nis'404 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'403 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'404
         | _ -> Fail_act)
     | Nis'401 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'402
         | _ -> Fail_act)
     | Nis'400 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'399 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'400
         | _ -> Fail_act)
     | Nis'397 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'398
         | _ -> Fail_act)
     | Nis'396 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'532
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'530
         | Coq__2.DO't -> Shift_act Nis'419
         | Coq__2.FOR't -> Shift_act Nis'414
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'407
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'405
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'401
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'397
         | _ -> Fail_act)
     | Nis'395 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'396
         | _ -> Fail_act)
     | Nis'393 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'394
         | _ -> Fail_act)
     | Nis'392 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'391 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'392
         | _ -> Fail_act)
     | Nis'390 -> Default_reduce_act Coq__2.Prod'jump_statement'3
     | Nis'389 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.SEMICOLON't -> Shift_act Nis'390
         | _ -> Fail_act)
     | Nis'388 -> Default_reduce_act Coq__2.Prod'jump_statement'4
     | Nis'387 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SEMICOLON't -> Shift_act Nis'388
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'386 -> Default_reduce_act Coq__2.Prod'expression_statement'1
     | Nis'385 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'384 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'385
         | _ -> Fail_act)
     | Nis'382 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'383
         | _ -> Fail_act)
     | Nis'381 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'380 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'381
         | _ -> Fail_act)
     | Nis'378 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'379
         | _ -> Fail_act)
     | Nis'377 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ASM't -> Shift_act Nis'435
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BREAK't -> Shift_act Nis'433
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CASE't -> Shift_act Nis'430
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.CONTINUE't -> Shift_act Nis'428
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DEFAULT't -> Shift_act Nis'426
         | Coq__2.DO't -> Shift_act Nis'425
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.FOR't -> Shift_act Nis'420
         | Coq__2.GOTO't -> Shift_act Nis'411
         | Coq__2.IF_'t -> Shift_act Nis'393
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.OTHER_NAME't -> Shift_act Nis'391
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.PRAGMA't -> Shift_act Nis'598
         | Coq__2.RBRACE't -> Shift_act Nis'597
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RETURN't -> Shift_act Nis'387
         | Coq__2.SEMICOLON't -> Shift_act Nis'386
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.SWITCH't -> Shift_act Nis'382
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | Coq__2.WHILE't -> Shift_act Nis'378
         | _ -> Fail_act)
     | Nis'376 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACE't -> Shift_act Nis'377
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'375 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.SEMICOLON't -> Shift_act Nis'365
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'374 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACE't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'373 -> Default_reduce_act Coq__2.Prod'init_declarator_list'0
     | Nis'372 -> Default_reduce_act Coq__2.Prod'init_declarator'1
     | Nis'371 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'370 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'init_declarator'0
         | Coq__2.EQ't -> Shift_act Nis'371
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'init_declarator'0
         | _ -> Fail_act)
     | Nis'369 -> Default_reduce_act Coq__2.Prod'init_declarator_list'1
     | Nis'368 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'367 -> Default_reduce_act Coq__2.Prod'declaration'0
     | Nis'366 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'368
         | Coq__2.SEMICOLON't -> Shift_act Nis'367
         | _ -> Fail_act)
     | Nis'365 -> Default_reduce_act Coq__2.Prod'declaration'1
     | Nis'364 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.SEMICOLON't -> Shift_act Nis'365
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'363 -> Default_reduce_act Coq__2.Prod'translation_unit'1
     | Nis'362 -> Default_reduce_act Coq__2.Prod'external_declaration'0
     | Nis'361 -> Default_reduce_act Coq__2.Prod'translation_unit_file'0
     | Nis'360 -> Default_reduce_act Coq__2.Prod'translation_unit'2
     | Nis'359 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EOF't -> Shift_act Nis'361
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PRAGMA't -> Shift_act Nis'15
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SEMICOLON't -> Shift_act Nis'360
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'357 -> Default_reduce_act Coq__2.Prod'translation_unit_file'1
     | Nis'356 -> Default_reduce_act Coq__2.Prod'attribute_specifier'1
     | Nis'355 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'198
         | Coq__2.RPAREN't -> Shift_act Nis'356
         | _ -> Fail_act)
     | Nis'354 -> Default_reduce_act Coq__2.Prod'unary_expression'4
     | Nis'353 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.AND_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.DIV_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.LBRACE't -> Shift_act Nis'327
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.LEFT_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.MOD_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.MUL_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.OR_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.PERCENT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.RIGHT_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.SLASH't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.SUB_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | Coq__2.XOR_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'5
         | _ -> Fail_act)
     | Nis'352 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'353
         | _ -> Fail_act)
     | Nis'351 -> Default_reduce_act Coq__2.Prod'cast_expression'1
     | Nis'350 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'327
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'349 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'350
         | _ -> Fail_act)
     | Nis'348 -> Default_reduce_act Coq__2.Prod'unary_expression'1
     | Nis'347 -> Default_reduce_act Coq__2.Prod'primary_expression'3
     | Nis'346 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RPAREN't -> Shift_act Nis'347
         | _ -> Fail_act)
     | Nis'345 -> Default_reduce_act Coq__2.Prod'postfix_expression'10
     | Nis'344 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACE't -> Shift_act Nis'345
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'343 -> Default_reduce_act Coq__2.Prod'postfix_expression'9
     | Nis'342 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'344
         | Coq__2.RBRACE't -> Shift_act Nis'343
         | _ -> Fail_act)
     | Nis'341 -> Default_reduce_act Coq__2.Prod'initializer_list'1
     | Nis'340 -> Default_reduce_act Coq__2.Prod'initializer_list'0
     | Nis'339 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'338 -> Default_reduce_act Coq__2.Prod'initializer_list'3
     | Nis'337 -> Default_reduce_act Coq__2.Prod'c_initializer'0
     | Nis'336 -> Default_reduce_act Coq__2.Prod'initializer_list'2
     | Nis'335 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'334 -> Default_reduce_act Coq__2.Prod'designation'0
     | Nis'333 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.EQ't -> Shift_act Nis'334
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | _ -> Fail_act)
     | Nis'332 -> Default_reduce_act Coq__2.Prod'c_initializer'2
     | Nis'331 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACE't -> Shift_act Nis'332
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'330 -> Default_reduce_act Coq__2.Prod'c_initializer'1
     | Nis'329 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'331
         | Coq__2.RBRACE't -> Shift_act Nis'330
         | _ -> Fail_act)
     | Nis'328 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'327 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LBRACE't -> Shift_act Nis'328
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'326 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LBRACE't -> Shift_act Nis'327
         | _ -> Fail_act)
     | Nis'325 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'326
         | _ -> Fail_act)
     | Nis'324 -> Default_reduce_act Coq__2.Prod'enum_specifier'3
     | Nis'323 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACE't -> Shift_act Nis'324
         | Coq__2.VAR_NAME't -> Shift_act Nis'310
         | _ -> Fail_act)
     | Nis'322 -> Default_reduce_act Coq__2.Prod'enum_specifier'1
     | Nis'321 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'323
         | Coq__2.RBRACE't -> Shift_act Nis'322
         | _ -> Fail_act)
     | Nis'320 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR_NAME't -> Shift_act Nis'310
         | _ -> Fail_act)
     | Nis'319 -> Default_reduce_act Coq__2.Prod'enumerator_list'0
     | Nis'318 -> Default_reduce_act Coq__2.Prod'enumerator'1
     | Nis'316 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'enumerator'0
         | Coq__2.EQ't -> Shift_act Nis'317
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'enumerator'0
         | _ -> Fail_act)
     | Nis'315 -> Default_reduce_act Coq__2.Prod'enumerator_list'1
     | Nis'314 -> Default_reduce_act Coq__2.Prod'enum_specifier'2
     | Nis'313 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACE't -> Shift_act Nis'314
         | Coq__2.VAR_NAME't -> Shift_act Nis'310
         | _ -> Fail_act)
     | Nis'312 -> Default_reduce_act Coq__2.Prod'enum_specifier'0
     | Nis'311 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'313
         | Coq__2.RBRACE't -> Shift_act Nis'312
         | _ -> Fail_act)
     | Nis'310 -> Default_reduce_act Coq__2.Prod'enumeration_constant'0
     | Nis'309 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR_NAME't -> Shift_act Nis'310
         | _ -> Fail_act)
     | Nis'308 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.ATTRIBUTE't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.AUTO't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.CHAR't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.CONST't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.DOUBLE't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.ENUM't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.EXTERN't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.FLOAT't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.INLINE't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.INT't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.LBRACE't -> Shift_act Nis'309
         | Coq__2.LBRACK't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.LONG't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.NORETURN't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.PACKED't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.REGISTER't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.RESTRICT't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.SHORT't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.SIGNED't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.STATIC't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.STRUCT't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.TYPEDEF't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.TYPEDEF_NAME't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.UNDERSCORE_BOOL't ->
           Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.UNION't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.UNSIGNED't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.VAR_NAME't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.VOID't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | Coq__2.VOLATILE't -> Reduce_act Coq__2.Prod'enum_specifier'4
         | _ -> Fail_act)
     | Nis'307 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LBRACE't -> Shift_act Nis'320
         | Coq__2.OTHER_NAME't -> Shift_act Nis'308
         | _ -> Fail_act)
     | Nis'306 -> Default_reduce_act Coq__2.Prod'gcc_attribute_list'0
     | Nis'305 -> Default_reduce_act Coq__2.Prod'gcc_attribute_list'1
     | Nis'304 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'gcc_attribute'0
         | Coq__2.CONST't -> Shift_act Nis'38
         | Coq__2.OTHER_NAME't -> Shift_act Nis'37
         | Coq__2.PACKED't -> Shift_act Nis'36
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'gcc_attribute'0
         | _ -> Fail_act)
     | Nis'303 -> Default_reduce_act Coq__2.Prod'attribute_specifier'0
     | Nis'302 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'303
         | _ -> Fail_act)
     | Nis'301 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'304
         | Coq__2.RPAREN't -> Shift_act Nis'302
         | _ -> Fail_act)
     | Nis'300 -> Default_reduce_act Coq__2.Prod'gcc_attribute'3
     | Nis'299 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'198
         | Coq__2.RPAREN't -> Shift_act Nis'300
         | _ -> Fail_act)
     | Nis'298 -> Default_reduce_act Coq__2.Prod'unary_expression'2
     | Nis'297 -> Default_reduce_act Coq__2.Prod'postfix_expression'4
     | Nis'296 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'297
         | _ -> Fail_act)
     | Nis'295 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'294 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'295
         | _ -> Fail_act)
     | Nis'293 -> Default_reduce_act Coq__2.Prod'designator_list'0
     | Nis'292 -> Default_reduce_act Coq__2.Prod'designator_list'1
     | Nis'291 -> Default_reduce_act Coq__2.Prod'postfix_expression'11
     | Nis'290 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.RPAREN't -> Shift_act Nis'291
         | _ -> Fail_act)
     | Nis'289 -> Default_reduce_act Coq__2.Prod'designator'1
     | Nis'288 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'289
         | _ -> Fail_act)
     | Nis'287 -> Default_reduce_act Coq__2.Prod'designator'0
     | Nis'286 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'287
         | _ -> Fail_act)
     | Nis'284 -> Default_reduce_act Coq__2.Prod'postfix_expression'12
     | Nis'283 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.DOT't -> Shift_act Nis'288
         | Coq__2.LBRACK't -> Shift_act Nis'285
         | Coq__2.RPAREN't -> Shift_act Nis'284
         | _ -> Fail_act)
     | Nis'282 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'283
         | _ -> Fail_act)
     | Nis'281 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'282
         | _ -> Fail_act)
     | Nis'280 -> Default_reduce_act Coq__2.Prod'attribute_specifier'2
     | Nis'279 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'198
         | Coq__2.RPAREN't -> Shift_act Nis'280
         | _ -> Fail_act)
     | Nis'278 -> Default_reduce_act Coq__2.Prod'attribute_specifier'3
     | Nis'277 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'278
         | _ -> Fail_act)
     | Nis'276 -> Default_reduce_act Coq__2.Prod'type_name'1
     | Nis'275 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'abstract_declarator'0
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LPAREN't -> Shift_act Nis'274
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'abstract_declarator'0
         | _ -> Fail_act)
     | Nis'274 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'274
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Shift_act Nis'115
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'273 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'type_name'0
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LPAREN't -> Shift_act Nis'274
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'type_name'0
         | Coq__2.STAR't -> Shift_act Nis'70
         | _ -> Fail_act)
     | Nis'272 -> Default_reduce_act Coq__2.Prod'unary_expression'6
     | Nis'271 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'272
         | _ -> Fail_act)
     | Nis'270 -> Default_reduce_act Coq__2.Prod'specifier_qualifier_list'0
     | Nis'269 -> Default_reduce_act Coq__2.Prod'specifier_qualifier_list'2
     | Nis'268 -> Default_reduce_act Coq__2.Prod'struct_or_union_specifier'1
     | Nis'267 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RBRACE't -> Shift_act Nis'268
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'266 -> Default_reduce_act Coq__2.Prod'struct_declaration_list'0
     | Nis'265 -> Default_reduce_act Coq__2.Prod'struct_declarator_list'0
     | Nis'264 -> Default_reduce_act Coq__2.Prod'struct_declarator'1
     | Nis'262 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'263
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'struct_declarator'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'struct_declarator'0
         | _ -> Fail_act)
     | Nis'261 -> Default_reduce_act Coq__2.Prod'struct_declarator_list'1
     | Nis'260 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'255
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'259 -> Default_reduce_act Coq__2.Prod'struct_declaration'0
     | Nis'258 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'260
         | Coq__2.SEMICOLON't -> Shift_act Nis'259
         | _ -> Fail_act)
     | Nis'257 -> Default_reduce_act Coq__2.Prod'constant_expression'0
     | Nis'256 -> Default_reduce_act Coq__2.Prod'struct_declarator'2
     | Nis'254 -> Default_reduce_act Coq__2.Prod'identifier_list'1
     | Nis'253 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.VAR_NAME't -> Shift_act Nis'254
         | _ -> Fail_act)
     | Nis'252 -> Default_reduce_act Coq__2.Prod'direct_declarator'8
     | Nis'251 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'253
         | Coq__2.RPAREN't -> Shift_act Nis'252
         | _ -> Fail_act)
     | Nis'250 -> Default_reduce_act Coq__2.Prod'parameter_declaration'1
     | Nis'249 -> Default_reduce_act Coq__2.Prod'parameter_declaration'0
     | Nis'248 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'0
     | Nis'247 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'248
         | _ -> Fail_act)
     | Nis'246 -> Default_reduce_act Coq__2.Prod'direct_declarator'1
     | Nis'245 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'246
         | _ -> Fail_act)
     | Nis'244 -> Default_reduce_act Coq__2.Prod'attribute_specifier_list'1
     | Nis'243 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.COLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.LBRACE't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.OTHER_NAME't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | _ -> Fail_act)
     | Nis'242 -> Default_reduce_act Coq__2.Prod'declarator'0
     | Nis'241 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.COLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | _ -> Fail_act)
     | Nis'240 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'abstract_declarator'2
         | Coq__2.LBRACK't -> Shift_act Nis'221
         | Coq__2.LPAREN't -> Shift_act Nis'216
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'abstract_declarator'2
         | _ -> Fail_act)
     | Nis'239 -> Default_reduce_act Coq__2.Prod'direct_declarator'3
     | Nis'238 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'239
         | _ -> Fail_act)
     | Nis'237 -> Default_reduce_act Coq__2.Prod'direct_declarator'2
     | Nis'236 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'237
         | _ -> Fail_act)
     | Nis'235 -> Default_reduce_act Coq__2.Prod'direct_declarator'4
     | Nis'234 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'235
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'233 -> Default_reduce_act Coq__2.Prod'direct_declarator'5
     | Nis'232 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'233
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'231 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.ATTRIBUTE't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.AUTO't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.CHAR't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.CONST't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.DOUBLE't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.ENUM't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.EXTERN't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.FLOAT't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.INLINE't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.INT't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.LBRACE't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.LBRACK't -> Shift_act Nis'232
         | Coq__2.LONG't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.LPAREN't -> Shift_act Nis'81
         | Coq__2.NORETURN't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.PACKED't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.REGISTER't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.RESTRICT't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.SHORT't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.SIGNED't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.STATIC't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.STRUCT't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.TYPEDEF't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.TYPEDEF_NAME't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.UNDERSCORE_BOOL't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.UNION't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.UNSIGNED't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.VOID't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | Coq__2.VOLATILE't -> Reduce_act Coq__2.Prod'declarator_noattrend'0
         | _ -> Fail_act)
     | Nis'230 ->
       Default_reduce_act Coq__2.Prod'direct_abstract_declarator'10
     | Nis'229 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'230
         | _ -> Fail_act)
     | Nis'228 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'3
     | Nis'227 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'228
         | _ -> Fail_act)
     | Nis'226 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'1
     | Nis'225 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'226
         | _ -> Fail_act)
     | Nis'224 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'5
     | Nis'223 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'224
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'222 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'7
     | Nis'221 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'222
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'220 -> Default_reduce_act Coq__2.Prod'parameter_list'0
     | Nis'219 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'9
     | Nis'218 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'219
         | _ -> Fail_act)
     | Nis'217 ->
       Default_reduce_act Coq__2.Prod'direct_abstract_declarator'11
     | Nis'216 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Shift_act Nis'217
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'215 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'abstract_declarator'1
         | Coq__2.LBRACK't -> Shift_act Nis'221
         | Coq__2.LPAREN't -> Shift_act Nis'216
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'abstract_declarator'1
         | _ -> Fail_act)
     | Nis'214 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'abstract_declarator'0
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LPAREN't -> Shift_act Nis'114
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'abstract_declarator'0
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'213 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'4
     | Nis'212 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'213
         | _ -> Fail_act)
     | Nis'211 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'2
     | Nis'210 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RBRACK't -> Shift_act Nis'211
         | _ -> Fail_act)
     | Nis'209 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'6
     | Nis'208 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'209
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'207 -> Default_reduce_act Coq__2.Prod'unary_expression'3
     | Nis'206 -> Default_reduce_act Coq__2.Prod'postfix_expression'8
     | Nis'205 -> Default_reduce_act Coq__2.Prod'postfix_expression'5
     | Nis'204 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'205
         | _ -> Fail_act)
     | Nis'203 -> Default_reduce_act Coq__2.Prod'postfix_expression'7
     | Nis'202 -> Default_reduce_act Coq__2.Prod'postfix_expression'1
     | Nis'201 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'186
         | Coq__2.RBRACK't -> Shift_act Nis'202
         | _ -> Fail_act)
     | Nis'199 -> Default_reduce_act Coq__2.Prod'argument_expression_list'1
     | Nis'197 -> Default_reduce_act Coq__2.Prod'postfix_expression'2
     | Nis'196 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'198
         | Coq__2.RPAREN't -> Shift_act Nis'197
         | _ -> Fail_act)
     | Nis'195 -> Default_reduce_act Coq__2.Prod'argument_expression_list'0
     | Nis'194 -> Default_reduce_act Coq__2.Prod'assignment_expression'1
     | Nis'193 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't -> Shift_act Nis'169
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'logical_OR_expression'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'logical_OR_expression'1
         | _ -> Fail_act)
     | Nis'191 -> Default_reduce_act Coq__2.Prod'expression'0
     | Nis'190 -> Default_reduce_act Coq__2.Prod'conditional_expression'1
     | Nis'188 -> Default_reduce_act Coq__2.Prod'expression'1
     | Nis'187 -> Default_reduce_act Coq__2.Prod'assignment_expression'0
     | Nis'185 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'189
         | Coq__2.COMMA't -> Shift_act Nis'186
         | _ -> Fail_act)
     | Nis'184 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.BAR't -> Shift_act Nis'171
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'logical_AND_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'logical_AND_expression'0
         | _ -> Fail_act)
     | Nis'183 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.BARBAR't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.HAT't -> Shift_act Nis'173
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.RBRACE't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.RBRACK't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'0
         | _ -> Fail_act)
     | Nis'182 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Shift_act Nis'180
         | Coq__2.ANDAND't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.BARBAR't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.RBRACE't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.RBRACK't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'0
         | _ -> Fail_act)
     | Nis'181 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.EQEQ't -> Shift_act Nis'177
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.NEQ't -> Shift_act Nis'175
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'AND_expression'1
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'AND_expression'1
         | _ -> Fail_act)
     | Nis'179 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Shift_act Nis'180
         | Coq__2.ANDAND't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.BARBAR't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.RBRACE't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.RBRACK't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'exclusive_OR_expression'1
         | _ -> Fail_act)
     | Nis'178 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.GEQ't -> Shift_act Nis'164
         | Coq__2.GT't -> Shift_act Nis'162
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.LEQ't -> Shift_act Nis'160
         | Coq__2.LT't -> Shift_act Nis'157
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'equality_expression'1
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'equality_expression'1
         | _ -> Fail_act)
     | Nis'176 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.GEQ't -> Shift_act Nis'164
         | Coq__2.GT't -> Shift_act Nis'162
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.LEQ't -> Shift_act Nis'160
         | Coq__2.LT't -> Shift_act Nis'157
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'equality_expression'2
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'equality_expression'2
         | _ -> Fail_act)
     | Nis'174 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.EQEQ't -> Shift_act Nis'177
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.NEQ't -> Shift_act Nis'175
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'AND_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'AND_expression'0
         | _ -> Fail_act)
     | Nis'172 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.BARBAR't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.HAT't -> Shift_act Nis'173
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.RBRACE't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.RBRACK't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'inclusive_OR_expression'1
         | _ -> Fail_act)
     | Nis'170 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.BAR't -> Shift_act Nis'171
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'logical_AND_expression'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'logical_AND_expression'1
         | _ -> Fail_act)
     | Nis'168 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ANDAND't -> Shift_act Nis'169
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'logical_OR_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'logical_OR_expression'0
         | _ -> Fail_act)
     | Nis'166 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.BARBAR't -> Shift_act Nis'192
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'conditional_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'conditional_expression'0
         | Coq__2.QUESTION't -> Shift_act Nis'167
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'conditional_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'conditional_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'conditional_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'conditional_expression'0
         | _ -> Fail_act)
     | Nis'165 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.LEFT't -> Shift_act Nis'154
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.RIGHT't -> Shift_act Nis'140
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'relational_expression'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'relational_expression'4
         | _ -> Fail_act)
     | Nis'163 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.LEFT't -> Shift_act Nis'154
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.RIGHT't -> Shift_act Nis'140
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'relational_expression'2
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'relational_expression'2
         | _ -> Fail_act)
     | Nis'161 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.LEFT't -> Shift_act Nis'154
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.RIGHT't -> Shift_act Nis'140
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'relational_expression'3
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'relational_expression'3
         | _ -> Fail_act)
     | Nis'159 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.MINUS't -> Shift_act Nis'152
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.PLUS't -> Shift_act Nis'150
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'shift_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'shift_expression'0
         | _ -> Fail_act)
     | Nis'158 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.LEFT't -> Shift_act Nis'154
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.RIGHT't -> Shift_act Nis'140
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'relational_expression'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'relational_expression'1
         | _ -> Fail_act)
     | Nis'156 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.GEQ't -> Shift_act Nis'164
         | Coq__2.GT't -> Shift_act Nis'162
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.LEQ't -> Shift_act Nis'160
         | Coq__2.LT't -> Shift_act Nis'157
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'equality_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'equality_expression'0
         | _ -> Fail_act)
     | Nis'155 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.MINUS't -> Shift_act Nis'152
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.PLUS't -> Shift_act Nis'150
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'shift_expression'1
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'shift_expression'1
         | _ -> Fail_act)
     | Nis'153 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.PERCENT't -> Shift_act Nis'146
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'additive_expression'2
         | Coq__2.SLASH't -> Shift_act Nis'144
         | Coq__2.STAR't -> Shift_act Nis'142
         | _ -> Fail_act)
     | Nis'151 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.PERCENT't -> Shift_act Nis'146
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'additive_expression'1
         | Coq__2.SLASH't -> Shift_act Nis'144
         | Coq__2.STAR't -> Shift_act Nis'142
         | _ -> Fail_act)
     | Nis'149 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.MINUS't -> Shift_act Nis'152
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.PLUS't -> Shift_act Nis'150
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'shift_expression'2
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'shift_expression'2
         | _ -> Fail_act)
     | Nis'148 -> Default_reduce_act Coq__2.Prod'multiplicative_expression'0
     | Nis'147 -> Default_reduce_act Coq__2.Prod'multiplicative_expression'3
     | Nis'145 -> Default_reduce_act Coq__2.Prod'multiplicative_expression'2
     | Nis'143 -> Default_reduce_act Coq__2.Prod'multiplicative_expression'1
     | Nis'141 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.PERCENT't -> Shift_act Nis'146
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'additive_expression'0
         | Coq__2.SLASH't -> Shift_act Nis'144
         | Coq__2.STAR't -> Shift_act Nis'142
         | _ -> Fail_act)
     | Nis'139 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.LEFT't -> Shift_act Nis'154
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.QUESTION't ->
           Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.RIGHT't -> Shift_act Nis'140
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'relational_expression'0
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'relational_expression'0
         | _ -> Fail_act)
     | Nis'137 -> Default_reduce_act Coq__2.Prod'assignment_operator'4
     | Nis'136 -> Default_reduce_act Coq__2.Prod'assignment_operator'10
     | Nis'135 -> Default_reduce_act Coq__2.Prod'assignment_operator'2
     | Nis'134 -> Default_reduce_act Coq__2.Prod'assignment_operator'0
     | Nis'133 -> Default_reduce_act Coq__2.Prod'assignment_operator'6
     | Nis'132 -> Default_reduce_act Coq__2.Prod'assignment_operator'3
     | Nis'131 -> Default_reduce_act Coq__2.Prod'assignment_operator'1
     | Nis'130 -> Default_reduce_act Coq__2.Prod'assignment_operator'9
     | Nis'129 -> Default_reduce_act Coq__2.Prod'assignment_operator'7
     | Nis'128 -> Default_reduce_act Coq__2.Prod'assignment_operator'5
     | Nis'127 -> Default_reduce_act Coq__2.Prod'assignment_operator'8
     | Nis'126 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Shift_act Nis'137
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.AND_ASSIGN't -> Shift_act Nis'136
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.DIV_ASSIGN't -> Shift_act Nis'135
         | Coq__2.EQ't -> Shift_act Nis'134
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.LEFT_ASSIGN't -> Shift_act Nis'133
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.MOD_ASSIGN't -> Shift_act Nis'132
         | Coq__2.MUL_ASSIGN't -> Shift_act Nis'131
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.OR_ASSIGN't -> Shift_act Nis'130
         | Coq__2.PERCENT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.RIGHT_ASSIGN't -> Shift_act Nis'129
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.SLASH't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'cast_expression'0
         | Coq__2.SUB_ASSIGN't -> Shift_act Nis'128
         | Coq__2.XOR_ASSIGN't -> Shift_act Nis'127
         | _ -> Fail_act)
     | Nis'125 -> Default_reduce_act Coq__2.Prod'postfix_expression'3
     | Nis'124 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'125
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'123 -> Default_reduce_act Coq__2.Prod'postfix_expression'6
     | Nis'122 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.OTHER_NAME't -> Shift_act Nis'123
         | _ -> Fail_act)
     | Nis'121 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ADD_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.AND't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.ANDAND't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.AND_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.BAR't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.BARBAR't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.DEC't -> Shift_act Nis'206
         | Coq__2.DIV_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.DOT't -> Shift_act Nis'204
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.EQEQ't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.GEQ't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.GT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.HAT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.INC't -> Shift_act Nis'203
         | Coq__2.LBRACK't -> Shift_act Nis'200
         | Coq__2.LEFT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.LEFT_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.LEQ't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.LPAREN't -> Shift_act Nis'124
         | Coq__2.LT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.MINUS't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.MOD_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.MUL_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.NEQ't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.OR_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.PERCENT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.PLUS't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.PTR't -> Shift_act Nis'122
         | Coq__2.QUESTION't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.RBRACE't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.RBRACK't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.RIGHT't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.RIGHT_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.SEMICOLON't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.SLASH't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.SUB_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | Coq__2.XOR_ASSIGN't -> Reduce_act Coq__2.Prod'unary_expression'0
         | _ -> Fail_act)
     | Nis'120 -> Default_reduce_act Coq__2.Prod'postfix_expression'0
     | Nis'119 -> Default_reduce_act Coq__2.Prod'cast_expression'0
     | Nis'117 -> Default_reduce_act Coq__2.Prod'direct_abstract_declarator'8
     | Nis'116 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RBRACK't -> Shift_act Nis'117
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'115 ->
       Default_reduce_act Coq__2.Prod'direct_abstract_declarator'12
     | Nis'114 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'114
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Shift_act Nis'115
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'113 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'parameter_declaration'2
         | Coq__2.LBRACK't -> Shift_act Nis'116
         | Coq__2.LPAREN't -> Shift_act Nis'114
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'parameter_declaration'2
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'112 -> Default_reduce_act Coq__2.Prod'parameter_list'1
     | Nis'111 -> Default_reduce_act Coq__2.Prod'parameter_type_list'1
     | Nis'110 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ELLIPSIS't -> Shift_act Nis'111
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'109 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Shift_act Nis'110
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'parameter_type_list'0
         | _ -> Fail_act)
     | Nis'108 -> Default_reduce_act Coq__2.Prod'direct_declarator'6
     | Nis'107 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.RPAREN't -> Shift_act Nis'108
         | _ -> Fail_act)
     | Nis'106 -> Default_reduce_act Coq__2.Prod'declaration_specifiers'2
     | Nis'105 -> Default_reduce_act Coq__2.Prod'declaration_specifiers'0
     | Nis'104 -> Default_reduce_act Coq__2.Prod'declaration_specifiers'3
     | Nis'103 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'102 -> Default_reduce_act Coq__2.Prod'declaration_specifiers'4
     | Nis'101 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'100 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'99 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'98 -> Default_reduce_act Coq__2.Prod'declaration_specifiers'1
     | Nis'97 ->
       Default_reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'1
     | Nis'96 ->
       Default_reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'2
     | Nis'95 ->
       Default_reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'0
     | Nis'94 ->
       Default_reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'3
     | Nis'93 -> Default_reduce_act Coq__2.Prod'type_specifier'11
     | Nis'92 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'91 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'90 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'89 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'88 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'declaration_specifiers_typespec_opt'4
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'87 -> Default_reduce_act Coq__2.Prod'storage_class_specifier'3
     | Nis'86 -> Default_reduce_act Coq__2.Prod'storage_class_specifier'1
     | Nis'85 -> Default_reduce_act Coq__2.Prod'function_specifier'0
     | Nis'84 -> Default_reduce_act Coq__2.Prod'function_specifier'1
     | Nis'83 -> Default_reduce_act Coq__2.Prod'direct_declarator'7
     | Nis'82 -> Default_reduce_act Coq__2.Prod'identifier_list'0
     | Nis'81 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.AUTO't -> Shift_act Nis'87
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.EXTERN't -> Shift_act Nis'86
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INLINE't -> Shift_act Nis'85
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.NORETURN't -> Shift_act Nis'84
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.REGISTER't -> Shift_act Nis'14
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Shift_act Nis'83
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STATIC't -> Shift_act Nis'9
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF't -> Shift_act Nis'7
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'82
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'80 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.ATTRIBUTE't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.AUTO't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.CHAR't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.COLON't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.CONST't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.DOUBLE't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.ENUM't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.EQ't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.EXTERN't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.FLOAT't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.INLINE't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.INT't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.LBRACE't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.LBRACK't -> Shift_act Nis'232
         | Coq__2.LONG't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.LPAREN't -> Shift_act Nis'81
         | Coq__2.NORETURN't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.PACKED't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.REGISTER't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.RESTRICT't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.SHORT't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.SIGNED't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.STATIC't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.STRUCT't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.TYPEDEF't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.TYPEDEF_NAME't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.UNDERSCORE_BOOL't ->
           Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.UNION't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.UNSIGNED't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.VOID't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | Coq__2.VOLATILE't -> Reduce_act Coq__2.Prod'declarator_noattrend'1
         | _ -> Fail_act)
     | Nis'79 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'78 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'77 -> Default_reduce_act Coq__2.Prod'struct_declaration'1
     | Nis'76 -> Default_reduce_act Coq__2.Prod'pointer'2
     | Nis'75 -> Default_reduce_act Coq__2.Prod'type_qualifier_list'0
     | Nis'74 -> Default_reduce_act Coq__2.Prod'type_qualifier'1
     | Nis'73 -> Default_reduce_act Coq__2.Prod'pointer'3
     | Nis'72 -> Default_reduce_act Coq__2.Prod'type_qualifier_list'1
     | Nis'71 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'pointer'1
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.LBRACK't -> Reduce_act Coq__2.Prod'pointer'1
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'pointer'1
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'pointer'1
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Reduce_act Coq__2.Prod'pointer'1
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'70 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'pointer'0
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.LBRACK't -> Reduce_act Coq__2.Prod'pointer'0
         | Coq__2.LPAREN't -> Reduce_act Coq__2.Prod'pointer'0
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'pointer'0
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Reduce_act Coq__2.Prod'pointer'0
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'69 -> Default_reduce_act Coq__2.Prod'direct_declarator'0
     | Nis'68 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COLON't -> Shift_act Nis'255
         | Coq__2.LPAREN't -> Shift_act Nis'78
         | Coq__2.SEMICOLON't -> Shift_act Nis'77
         | Coq__2.STAR't -> Shift_act Nis'70
         | Coq__2.VAR_NAME't -> Shift_act Nis'69
         | _ -> Fail_act)
     | Nis'67 -> Default_reduce_act Coq__2.Prod'struct_declaration_list'1
     | Nis'66 -> Default_reduce_act Coq__2.Prod'struct_or_union_specifier'0
     | Nis'65 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RBRACE't -> Shift_act Nis'66
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'64 -> Default_reduce_act Coq__2.Prod'struct_declaration_list'0
     | Nis'63 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.ATTRIBUTE't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.AUTO't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.CHAR't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.COLON't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.CONST't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.DOUBLE't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.ENUM't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.EXTERN't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.FLOAT't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.INLINE't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.INT't -> Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.LBRACE't -> Shift_act Nis'64
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.LONG't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.NORETURN't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.PACKED't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.REGISTER't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.RESTRICT't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.SHORT't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.SIGNED't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.STAR't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.STATIC't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.STRUCT't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.TYPEDEF't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.TYPEDEF_NAME't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.UNDERSCORE_BOOL't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.UNION't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.UNSIGNED't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.VOID't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | Coq__2.VOLATILE't ->
           Reduce_act Coq__2.Prod'struct_or_union_specifier'2
         | _ -> Fail_act)
     | Nis'62 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LBRACE't -> Shift_act Nis'266
         | Coq__2.OTHER_NAME't -> Shift_act Nis'63
         | _ -> Fail_act)
     | Nis'61 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.LBRACE't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.OTHER_NAME't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.PACKED't -> Shift_act Nis'16
         | _ -> Fail_act)
     | Nis'60 -> Default_reduce_act Coq__2.Prod'type_specifier'10
     | Nis'59 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COLON't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'58 -> Default_reduce_act Coq__2.Prod'type_qualifier'0
     | Nis'57 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.COLON't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.COMMA't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LBRACK't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.RPAREN't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.SEMICOLON't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STAR't -> Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't ->
           Reduce_act Coq__2.Prod'specifier_qualifier_list'1
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'56 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'55 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'56
         | _ -> Fail_act)
     | Nis'54 -> Default_reduce_act Coq__2.Prod'unary_operator'0
     | Nis'53 -> Default_reduce_act Coq__2.Prod'unary_operator'5
     | Nis'52 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'51 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'52
         | _ -> Fail_act)
     | Nis'50 -> Default_reduce_act Coq__2.Prod'type_specifier'1
     | Nis'49 -> Default_reduce_act Coq__2.Prod'type_qualifier_noattr'0
     | Nis'48 -> Default_reduce_act Coq__2.Prod'type_specifier'6
     | Nis'47 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'46 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'47
         | _ -> Fail_act)
     | Nis'44 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'45
         | _ -> Fail_act)
     | Nis'43 -> Default_reduce_act Coq__2.Prod'primary_expression'1
     | Nis'42 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'30
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'41 -> Default_reduce_act Coq__2.Prod'gcc_attribute'2
     | Nis'40 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RPAREN't -> Shift_act Nis'41
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'39 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'gcc_attribute'1
         | Coq__2.LPAREN't -> Shift_act Nis'40
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'gcc_attribute'1
         | _ -> Fail_act)
     | Nis'38 -> Default_reduce_act Coq__2.Prod'gcc_attribute_word'1
     | Nis'37 -> Default_reduce_act Coq__2.Prod'gcc_attribute_word'0
     | Nis'36 -> Default_reduce_act Coq__2.Prod'gcc_attribute_word'2
     | Nis'35 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.COMMA't -> Reduce_act Coq__2.Prod'gcc_attribute'0
         | Coq__2.CONST't -> Shift_act Nis'38
         | Coq__2.OTHER_NAME't -> Shift_act Nis'37
         | Coq__2.PACKED't -> Shift_act Nis'36
         | Coq__2.RPAREN't -> Reduce_act Coq__2.Prod'gcc_attribute'0
         | _ -> Fail_act)
     | Nis'34 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'35
         | _ -> Fail_act)
     | Nis'33 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'34
         | _ -> Fail_act)
     | Nis'32 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.LBRACE't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.OTHER_NAME't ->
           Reduce_act Coq__2.Prod'attribute_specifier_list'0
         | Coq__2.PACKED't -> Shift_act Nis'16
         | _ -> Fail_act)
     | Nis'31 -> Default_reduce_act Coq__2.Prod'type_specifier'5
     | Nis'30 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'29 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'30
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'28 -> Default_reduce_act Coq__2.Prod'type_specifier'3
     | Nis'27 -> Default_reduce_act Coq__2.Prod'type_specifier'4
     | Nis'26 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'25 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNAS't -> Shift_act Nis'51
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.ATTRIBUTE't -> Shift_act Nis'33
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CHAR't -> Shift_act Nis'50
         | Coq__2.CONST't -> Shift_act Nis'49
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.DOUBLE't -> Shift_act Nis'48
         | Coq__2.ENUM't -> Shift_act Nis'32
         | Coq__2.FLOAT't -> Shift_act Nis'31
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.INT't -> Shift_act Nis'28
         | Coq__2.LONG't -> Shift_act Nis'27
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PACKED't -> Shift_act Nis'16
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.RESTRICT't -> Shift_act Nis'13
         | Coq__2.SHORT't -> Shift_act Nis'11
         | Coq__2.SIGNED't -> Shift_act Nis'10
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.STRUCT't -> Shift_act Nis'8
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.TYPEDEF_NAME't -> Shift_act Nis'6
         | Coq__2.UNDERSCORE_BOOL't -> Shift_act Nis'5
         | Coq__2.UNION't -> Shift_act Nis'4
         | Coq__2.UNSIGNED't -> Shift_act Nis'3
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | Coq__2.VOID't -> Shift_act Nis'2
         | Coq__2.VOLATILE't -> Shift_act Nis'1
         | _ -> Fail_act)
     | Nis'24 -> Default_reduce_act Coq__2.Prod'unary_operator'3
     | Nis'23 -> Default_reduce_act Coq__2.Prod'unary_operator'2
     | Nis'22 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'25
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act)
     | Nis'21 -> Default_reduce_act Coq__2.Prod'unary_operator'1
     | Nis'20 -> Default_reduce_act Coq__2.Prod'primary_expression'2
     | Nis'19 -> Default_reduce_act Coq__2.Prod'unary_operator'4
     | Nis'18 -> Default_reduce_act Coq__2.Prod'primary_expression'0
     | Nis'16 ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.LPAREN't -> Shift_act Nis'17
         | _ -> Fail_act)
     | Nis'15 -> Default_reduce_act Coq__2.Prod'external_declaration'2
     | Nis'14 -> Default_reduce_act Coq__2.Prod'storage_class_specifier'4
     | Nis'13 -> Default_reduce_act Coq__2.Prod'type_qualifier_noattr'1
     | Nis'12 -> Default_reduce_act Coq__2.Prod'translation_unit'3
     | Nis'11 -> Default_reduce_act Coq__2.Prod'type_specifier'2
     | Nis'10 -> Default_reduce_act Coq__2.Prod'type_specifier'7
     | Nis'9 -> Default_reduce_act Coq__2.Prod'storage_class_specifier'2
     | Nis'8 -> Default_reduce_act Coq__2.Prod'struct_or_union'0
     | Nis'7 -> Default_reduce_act Coq__2.Prod'storage_class_specifier'0
     | Nis'6 -> Default_reduce_act Coq__2.Prod'type_specifier'12
     | Nis'5 -> Default_reduce_act Coq__2.Prod'type_specifier'9
     | Nis'4 -> Default_reduce_act Coq__2.Prod'struct_or_union'1
     | Nis'3 -> Default_reduce_act Coq__2.Prod'type_specifier'8
     | Nis'2 -> Default_reduce_act Coq__2.Prod'type_specifier'0
     | Nis'1 -> Default_reduce_act Coq__2.Prod'type_qualifier_noattr'2
     | _ ->
       Lookahead_act (fun terminal0 ->
         match terminal0 with
         | Coq__2.ALIGNOF't -> Shift_act Nis'55
         | Coq__2.AND't -> Shift_act Nis'54
         | Coq__2.BANG't -> Shift_act Nis'53
         | Coq__2.BUILTIN_OFFSETOF't -> Shift_act Nis'46
         | Coq__2.BUILTIN_VA_ARG't -> Shift_act Nis'44
         | Coq__2.CONSTANT't -> Shift_act Nis'43
         | Coq__2.DEC't -> Shift_act Nis'42
         | Coq__2.INC't -> Shift_act Nis'29
         | Coq__2.LPAREN't -> Shift_act Nis'26
         | Coq__2.MINUS't -> Shift_act Nis'24
         | Coq__2.PLUS't -> Shift_act Nis'23
         | Coq__2.SIZEOF't -> Shift_act Nis'22
         | Coq__2.STAR't -> Shift_act Nis'21
         | Coq__2.STRING_LITERAL't -> Shift_act Nis'20
         | Coq__2.TILDE't -> Shift_act Nis'19
         | Coq__2.VAR_NAME't -> Shift_act Nis'18
         | _ -> Fail_act))

  (** val goto_table : state -> Coq__2.nonterminal -> noninitstate option **)

  let goto_table state0 nt =
    match state0 with
    | Init _ ->
      (match nt with
       | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
       | Coq__2.Coq_declaration'nt -> Some Nis'611
       | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'364
       | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
       | Coq__2.Coq_external_declaration'nt -> Some Nis'612
       | Coq__2.Coq_function_definition'nt -> Some Nis'362
       | Coq__2.Coq_function_specifier'nt -> Some Nis'101
       | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
       | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
       | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
       | Coq__2.Coq_translation_unit'nt -> Some Nis'359
       | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
       | Coq__2.Coq_type_specifier'nt -> Some Nis'88
       | _ -> None)
    | Ninit n ->
      (match n with
       | Nis'609 ->
         (match nt with
          | Coq__2.Coq_compound_statement'nt -> Some Nis'610
          | _ -> None)
       | Nis'608 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'608
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'244
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'104
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'601 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_block_item'nt -> Some Nis'603
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_declaration'nt -> Some Nis'600
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'599
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'596 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'587
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'585 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'587
          | Coq__2.Coq_statement_safe'nt -> Some Nis'586
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'582 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'523
          | Coq__2.Coq_statement_safe'nt -> Some Nis'583
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'579 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'520
          | Coq__2.Coq_statement_safe'nt -> Some Nis'580
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'578 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'581
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'575 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'516
          | Coq__2.Coq_statement_safe'nt -> Some Nis'576
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'572 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'513
          | Coq__2.Coq_statement_safe'nt -> Some Nis'573
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'571 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'574
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'570 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'577
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'568 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'509
          | Coq__2.Coq_statement_safe'nt -> Some Nis'569
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'565 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'506
          | Coq__2.Coq_statement_safe'nt -> Some Nis'566
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'564 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'567
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'561 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'502
          | Coq__2.Coq_statement_safe'nt -> Some Nis'562
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'558 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'499
          | Coq__2.Coq_statement_safe'nt -> Some Nis'559
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'557 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'560
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'556 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'563
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'553 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'494
          | Coq__2.Coq_statement_safe'nt -> Some Nis'554
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'550 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'491
          | Coq__2.Coq_statement_safe'nt -> Some Nis'551
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'549 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'552
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'546 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'487
          | Coq__2.Coq_statement_safe'nt -> Some Nis'547
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'534 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'467
          | Coq__2.Coq_statement_safe'nt -> Some Nis'535
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'532 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'533
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'531 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'477
          | Coq__2.Coq_statement_safe'nt -> Some Nis'543
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'526 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'527
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'522 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'523
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'519 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'520
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'518 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'521
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'515 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'516
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'512 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'513
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'511 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'514
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'510 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'517
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'508 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'509
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'505 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'506
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'504 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'507
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'501 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'502
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'498 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'499
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'497 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'500
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'496 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'503
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'493 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'494
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'490 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'491
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'489 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'492
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'486 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'487
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'480 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'481
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'460 ->
         (match nt with
          | Coq__2.Coq_asm_flags'nt -> Some Nis'461
          | _ -> None)
       | Nis'458 ->
         (match nt with
          | Coq__2.Coq_asm_flags'nt -> Some Nis'462
          | _ -> None)
       | Nis'456 ->
         (match nt with
          | Coq__2.Coq_asm_op_name'nt -> Some Nis'450
          | Coq__2.Coq_asm_operand'nt -> Some Nis'463
          | Coq__2.Coq_asm_operands'nt -> Some Nis'457
          | Coq__2.Coq_asm_operands_ne'nt -> Some Nis'447
          | _ -> None)
       | Nis'452 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'453
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'448 ->
         (match nt with
          | Coq__2.Coq_asm_op_name'nt -> Some Nis'450
          | Coq__2.Coq_asm_operand'nt -> Some Nis'449
          | _ -> None)
       | Nis'443 ->
         (match nt with
          | Coq__2.Coq_asm_op_name'nt -> Some Nis'450
          | Coq__2.Coq_asm_operand'nt -> Some Nis'463
          | Coq__2.Coq_asm_operands'nt -> Some Nis'455
          | Coq__2.Coq_asm_operands_ne'nt -> Some Nis'447
          | _ -> None)
       | Nis'442 ->
         (match nt with
          | Coq__2.Coq_asm_arguments'nt -> Some Nis'464
          | _ -> None)
       | Nis'437 ->
         (match nt with
          | Coq__2.Coq_asm_attributes'nt -> Some Nis'438
          | _ -> None)
       | Nis'436 ->
         (match nt with
          | Coq__2.Coq_asm_attributes'nt -> Some Nis'439
          | _ -> None)
       | Nis'435 ->
         (match nt with
          | Coq__2.Coq_asm_attributes'nt -> Some Nis'440
          | _ -> None)
       | Nis'432 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'467
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'430 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'431
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'427 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'477
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'425 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'478
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'424 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'484
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'423 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'485
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'422 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'488
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'421 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_declaration'nt -> Some Nis'510
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'495
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'419 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'524
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'418 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'484
          | Coq__2.Coq_statement_safe'nt -> Some Nis'544
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'417 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'545
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'416 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'548
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'415 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_declaration'nt -> Some Nis'570
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'555
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'410 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'588
          | Coq__2.Coq_statement_safe'nt -> Some Nis'584
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'408 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'409
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'406 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'590
          | Coq__2.Coq_statement_safe'nt -> Some Nis'589
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'404 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'592
          | Coq__2.Coq_statement_safe'nt -> Some Nis'591
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'402 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'403
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'400 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'594
          | Coq__2.Coq_statement_safe'nt -> Some Nis'593
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'398 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'399
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'396 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'542
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'541
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'540
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_iteration_statement_statement_safe_'nt -> Some Nis'539
          | Coq__2.Coq_jump_statement'nt -> Some Nis'538
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_labeled_statement_statement_safe_'nt -> Some Nis'537
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_selection_statement_safe'nt -> Some Nis'536
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'588
          | Coq__2.Coq_statement_safe'nt -> Some Nis'595
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'394 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'395
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'392 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'590
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'387 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'389
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'385 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'592
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'383 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'384
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'381 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'594
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'379 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'380
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'377 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_asm_statement'nt -> Some Nis'476
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_block_item'nt -> Some Nis'604
          | Coq__2.Coq_block_item_list'nt -> Some Nis'601
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_compound_statement'nt -> Some Nis'475
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_declaration'nt -> Some Nis'600
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'473
          | Coq__2.Coq_expression_statement'nt -> Some Nis'472
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_iteration_statement_statement_dangerous_'nt ->
            Some Nis'471
          | Coq__2.Coq_jump_statement'nt -> Some Nis'470
          | Coq__2.Coq_labeled_statement_statement_dangerous_'nt ->
            Some Nis'469
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_selection_statement_dangerous'nt -> Some Nis'468
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_statement_dangerous'nt -> Some Nis'599
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'376 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_compound_statement'nt -> Some Nis'606
          | Coq__2.Coq_declaration'nt -> Some Nis'605
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'375 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'370
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_init_declarator'nt -> Some Nis'373
          | Coq__2.Coq_init_declarator_list'nt -> Some Nis'366
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | _ -> None)
       | Nis'374 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'608
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'242
          | Coq__2.Coq_declaration'nt -> Some Nis'607
          | Coq__2.Coq_declaration_list'nt -> Some Nis'376
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'375
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'371 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'372
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'368 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'370
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_init_declarator'nt -> Some Nis'369
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | _ -> None)
       | Nis'364 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'609
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'374
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_init_declarator'nt -> Some Nis'373
          | Coq__2.Coq_init_declarator_list'nt -> Some Nis'366
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | _ -> None)
       | Nis'359 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration'nt -> Some Nis'611
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'364
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_external_declaration'nt -> Some Nis'363
          | Coq__2.Coq_function_definition'nt -> Some Nis'362
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'350 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'351
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'344 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'338
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_designation'nt -> Some Nis'335
          | Coq__2.Coq_designator'nt -> Some Nis'293
          | Coq__2.Coq_designator_list'nt -> Some Nis'333
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'339 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'340
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'335 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'336
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'333 ->
         (match nt with
          | Coq__2.Coq_designator'nt -> Some Nis'292
          | _ -> None)
       | Nis'331 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'338
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_designation'nt -> Some Nis'335
          | Coq__2.Coq_designator'nt -> Some Nis'293
          | Coq__2.Coq_designator_list'nt -> Some Nis'333
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'328 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'341
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_designation'nt -> Some Nis'339
          | Coq__2.Coq_designator'nt -> Some Nis'293
          | Coq__2.Coq_designator_list'nt -> Some Nis'333
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_initializer_list'nt -> Some Nis'329
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'327 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'337
          | Coq__2.Coq_c_initializer'nt -> Some Nis'341
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_designation'nt -> Some Nis'339
          | Coq__2.Coq_designator'nt -> Some Nis'293
          | Coq__2.Coq_designator_list'nt -> Some Nis'333
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_initializer_list'nt -> Some Nis'342
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'323 ->
         (match nt with
          | Coq__2.Coq_enumeration_constant'nt -> Some Nis'316
          | Coq__2.Coq_enumerator'nt -> Some Nis'315
          | _ -> None)
       | Nis'320 ->
         (match nt with
          | Coq__2.Coq_enumeration_constant'nt -> Some Nis'316
          | Coq__2.Coq_enumerator'nt -> Some Nis'319
          | Coq__2.Coq_enumerator_list'nt -> Some Nis'321
          | _ -> None)
       | Nis'317 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'318
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'313 ->
         (match nt with
          | Coq__2.Coq_enumeration_constant'nt -> Some Nis'316
          | Coq__2.Coq_enumerator'nt -> Some Nis'315
          | _ -> None)
       | Nis'309 ->
         (match nt with
          | Coq__2.Coq_enumeration_constant'nt -> Some Nis'316
          | Coq__2.Coq_enumerator'nt -> Some Nis'319
          | Coq__2.Coq_enumerator_list'nt -> Some Nis'311
          | _ -> None)
       | Nis'304 ->
         (match nt with
          | Coq__2.Coq_gcc_attribute'nt -> Some Nis'305
          | Coq__2.Coq_gcc_attribute_word'nt -> Some Nis'39
          | _ -> None)
       | Nis'295 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'296
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'290 ->
         (match nt with
          | Coq__2.Coq_designator'nt -> Some Nis'292
          | _ -> None)
       | Nis'285 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'286
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'283 ->
         (match nt with
          | Coq__2.Coq_designator'nt -> Some Nis'293
          | Coq__2.Coq_designator_list'nt -> Some Nis'290
          | _ -> None)
       | Nis'275 ->
         (match nt with
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'215
          | _ -> None)
       | Nis'274 ->
         (match nt with
          | Coq__2.Coq_abstract_declarator'nt -> Some Nis'247
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'113
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'240
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_parameter_declaration'nt -> Some Nis'220
          | Coq__2.Coq_parameter_list'nt -> Some Nis'109
          | Coq__2.Coq_parameter_type_list'nt -> Some Nis'229
          | Coq__2.Coq_pointer'nt -> Some Nis'275
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'273 ->
         (match nt with
          | Coq__2.Coq_abstract_declarator'nt -> Some Nis'276
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'240
          | Coq__2.Coq_pointer'nt -> Some Nis'275
          | _ -> None)
       | Nis'267 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'68
          | Coq__2.Coq_struct_declaration'nt -> Some Nis'67
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'266 ->
         (match nt with
          | Coq__2.Coq_struct_declaration_list'nt -> Some Nis'267
          | _ -> None)
       | Nis'263 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'264
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'260 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'262
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | Coq__2.Coq_struct_declarator'nt -> Some Nis'261
          | _ -> None)
       | Nis'255 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'257
          | Coq__2.Coq_constant_expression'nt -> Some Nis'256
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'243 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'243
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'244
          | _ -> None)
       | Nis'241 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'243
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'242
          | _ -> None)
       | Nis'234 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'236
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'72
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'232 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'238
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'75
          | Coq__2.Coq_type_qualifier_list'nt -> Some Nis'234
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'223 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'225
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'72
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'221 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'227
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'75
          | Coq__2.Coq_type_qualifier_list'nt -> Some Nis'223
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'216 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'113
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_parameter_declaration'nt -> Some Nis'220
          | Coq__2.Coq_parameter_list'nt -> Some Nis'109
          | Coq__2.Coq_parameter_type_list'nt -> Some Nis'218
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'214 ->
         (match nt with
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'215
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'80
          | _ -> None)
       | Nis'208 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'210
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'72
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'200 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'201
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'198 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'199
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'192 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'193
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'189 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'190
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'186 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'188
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'180 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_equality_expression'nt -> Some Nis'181
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'177 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'178
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'175 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'176
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'173 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'179
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'171 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'172
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'169 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'170
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'167 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'185
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'164 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_shift_expression'nt -> Some Nis'165
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'162 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_shift_expression'nt -> Some Nis'163
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'160 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_shift_expression'nt -> Some Nis'161
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'157 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_shift_expression'nt -> Some Nis'158
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'154 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'155
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'152 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'153
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'150 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'151
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'146 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'147
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'144 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'145
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'142 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'143
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'140 ->
         (match nt with
          | Coq__2.Coq_additive_expression'nt -> Some Nis'149
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'138 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'194
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'126 ->
         (match nt with
          | Coq__2.Coq_assignment_operator'nt -> Some Nis'138
          | _ -> None)
       | Nis'124 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_argument_expression_list'nt -> Some Nis'196
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'195
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'118 ->
         (match nt with
          | Coq__2.Coq_cast_expression'nt -> Some Nis'207
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'119
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'116 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'212
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'75
          | Coq__2.Coq_type_qualifier_list'nt -> Some Nis'208
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'114 ->
         (match nt with
          | Coq__2.Coq_abstract_declarator'nt -> Some Nis'247
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'113
          | Coq__2.Coq_declarator'nt -> Some Nis'245
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'240
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_parameter_declaration'nt -> Some Nis'220
          | Coq__2.Coq_parameter_list'nt -> Some Nis'109
          | Coq__2.Coq_parameter_type_list'nt -> Some Nis'229
          | Coq__2.Coq_pointer'nt -> Some Nis'214
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'113 ->
         (match nt with
          | Coq__2.Coq_abstract_declarator'nt -> Some Nis'250
          | Coq__2.Coq_declarator'nt -> Some Nis'249
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_abstract_declarator'nt -> Some Nis'240
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_pointer'nt -> Some Nis'214
          | _ -> None)
       | Nis'110 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'113
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_parameter_declaration'nt -> Some Nis'112
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'103 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'104
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'101 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'102
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'100 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'105
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'99 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'106
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'92 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> Some Nis'94
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'92
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'91
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'90
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'89
          | _ -> None)
       | Nis'91 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> Some Nis'95
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'92
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'91
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'90
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'89
          | _ -> None)
       | Nis'90 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> Some Nis'96
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'92
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'91
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'90
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'89
          | _ -> None)
       | Nis'89 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> Some Nis'97
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'92
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'91
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'90
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'89
          | _ -> None)
       | Nis'88 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_declaration_specifiers_typespec_opt'nt -> Some Nis'98
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'92
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'91
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'90
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'89
          | _ -> None)
       | Nis'81 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'103
          | Coq__2.Coq_declaration_specifiers'nt -> Some Nis'113
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_function_specifier'nt -> Some Nis'101
          | Coq__2.Coq_identifier_list'nt -> Some Nis'251
          | Coq__2.Coq_parameter_declaration'nt -> Some Nis'220
          | Coq__2.Coq_parameter_list'nt -> Some Nis'109
          | Coq__2.Coq_parameter_type_list'nt -> Some Nis'107
          | Coq__2.Coq_storage_class_specifier'nt -> Some Nis'100
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'99
          | Coq__2.Coq_type_specifier'nt -> Some Nis'88
          | _ -> None)
       | Nis'79 ->
         (match nt with
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'80
          | _ -> None)
       | Nis'78 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'245
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | _ -> None)
       | Nis'71 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_pointer'nt -> Some Nis'73
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'72
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | _ -> None)
       | Nis'70 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_pointer'nt -> Some Nis'76
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'75
          | Coq__2.Coq_type_qualifier_list'nt -> Some Nis'71
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | _ -> None)
       | Nis'68 ->
         (match nt with
          | Coq__2.Coq_declarator'nt -> Some Nis'262
          | Coq__2.Coq_declarator_noattrend'nt -> Some Nis'241
          | Coq__2.Coq_direct_declarator'nt -> Some Nis'231
          | Coq__2.Coq_pointer'nt -> Some Nis'79
          | Coq__2.Coq_struct_declarator'nt -> Some Nis'265
          | Coq__2.Coq_struct_declarator_list'nt -> Some Nis'258
          | _ -> None)
       | Nis'65 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'68
          | Coq__2.Coq_struct_declaration'nt -> Some Nis'67
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'64 ->
         (match nt with
          | Coq__2.Coq_struct_declaration_list'nt -> Some Nis'65
          | _ -> None)
       | Nis'61 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'243
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'62
          | _ -> None)
       | Nis'59 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'269
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'57 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'270
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'56 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'271
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'52 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_argument_expression_list'nt -> Some Nis'279
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'195
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'277
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'47 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'281
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | _ -> None)
       | Nis'45 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'294
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'42 ->
         (match nt with
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'298
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'40 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_argument_expression_list'nt -> Some Nis'299
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'195
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'35 ->
         (match nt with
          | Coq__2.Coq_gcc_attribute'nt -> Some Nis'306
          | Coq__2.Coq_gcc_attribute_list'nt -> Some Nis'301
          | Coq__2.Coq_gcc_attribute_word'nt -> Some Nis'39
          | _ -> None)
       | Nis'32 ->
         (match nt with
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'243
          | Coq__2.Coq_attribute_specifier_list'nt -> Some Nis'307
          | _ -> None)
       | Nis'30 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'346
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'325
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'29 ->
         (match nt with
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'348
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'26 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'346
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'349
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'25 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'191
          | Coq__2.Coq_attribute_specifier'nt -> Some Nis'74
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_enum_specifier'nt -> Some Nis'93
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_expression'nt -> Some Nis'346
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_specifier_qualifier_list'nt -> Some Nis'273
          | Coq__2.Coq_struct_or_union'nt -> Some Nis'61
          | Coq__2.Coq_struct_or_union_specifier'nt -> Some Nis'60
          | Coq__2.Coq_type_name'nt -> Some Nis'352
          | Coq__2.Coq_type_qualifier'nt -> Some Nis'59
          | Coq__2.Coq_type_qualifier_noattr'nt -> Some Nis'58
          | Coq__2.Coq_type_specifier'nt -> Some Nis'57
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'22 ->
         (match nt with
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_unary_expression'nt -> Some Nis'354
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | Nis'17 ->
         (match nt with
          | Coq__2.AND_expression'nt -> Some Nis'182
          | Coq__2.Coq_additive_expression'nt -> Some Nis'159
          | Coq__2.Coq_argument_expression_list'nt -> Some Nis'355
          | Coq__2.Coq_assignment_expression'nt -> Some Nis'195
          | Coq__2.Coq_cast_expression'nt -> Some Nis'148
          | Coq__2.Coq_conditional_expression'nt -> Some Nis'187
          | Coq__2.Coq_equality_expression'nt -> Some Nis'174
          | Coq__2.Coq_exclusive_OR_expression'nt -> Some Nis'183
          | Coq__2.Coq_inclusive_OR_expression'nt -> Some Nis'184
          | Coq__2.Coq_logical_AND_expression'nt -> Some Nis'168
          | Coq__2.Coq_logical_OR_expression'nt -> Some Nis'166
          | Coq__2.Coq_multiplicative_expression'nt -> Some Nis'141
          | Coq__2.Coq_postfix_expression'nt -> Some Nis'121
          | Coq__2.Coq_primary_expression'nt -> Some Nis'120
          | Coq__2.Coq_relational_expression'nt -> Some Nis'156
          | Coq__2.Coq_shift_expression'nt -> Some Nis'139
          | Coq__2.Coq_unary_expression'nt -> Some Nis'126
          | Coq__2.Coq_unary_operator'nt -> Some Nis'118
          | _ -> None)
       | _ -> None)

  (** val past_symb_of_non_init_state : noninitstate -> Coq__2.symbol list **)

  let past_symb_of_non_init_state = fun _ -> assert false

  (** val past_state_of_non_init_state :
      noninitstate -> (state -> bool) list **)

  let past_state_of_non_init_state = fun _ -> assert false

  (** val items_of_state : state -> item list **)

  let items_of_state = fun _ -> assert false
 end

module MenhirLibParser = Make(Aut)

(** val translation_unit_file :
    nat -> MenhirLibParser.Inter.buffer -> definition list
    MenhirLibParser.Inter.parse_result **)

let translation_unit_file =
  Obj.magic MenhirLibParser.parse Aut.Init'0
