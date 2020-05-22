(** Pretty-printer for Csharpminor *)

open Format
open Camlcoq
open Csharpminor
open PrintAST
open AST

type associativity = LtoR | RtoL | NA

let precedence = function
  | Evar _ -> (16, NA)
  | Econst _ -> (16, NA)
  | Eunop _ -> (15, RtoL)
  | Eaddrof _ -> (15, RtoL)
  | Ebinop((Omul|Odiv|Odivu|Omod|Omodu|Omulf|Odivf|Omulfs|Odivfs|Omull|Odivl|Odivlu|Omodl|Omodlu), _, _) -> (13, LtoR)
  | Ebinop((Oadd|Osub|Oaddf|Osubf|Oaddfs|Osubfs|Oaddl|Osubl), _, _) -> (12, LtoR)
  | Ebinop((Oshl|Oshr|Oshru|Oshll|Oshrl|Oshrlu), _, _) -> (11, LtoR)
  | Ebinop((Ocmp _|Ocmpu _|Ocmpf _|Ocmpfs _|Ocmpl _|Ocmplu _), _, _) -> (10, LtoR)
  | Ebinop((Oand|Oandl), _, _) -> (8, LtoR)
  | Ebinop((Oxor|Oxorl), _, _) -> (7, LtoR)
  | Ebinop((Oor|Oorl), _, _) -> (6, LtoR)
  | Eload _ -> (15, RtoL)

let ident_name id = "'" ^ Camlcoq.extern_atom id ^ "'"
let temp_name (id: AST.ident) = "$" ^ Z.to_string (Z.Zpos id)

let name_of_unop : unary_operation -> string =
  PrintCminor.name_of_unop

let name_of_binop : binary_operation -> string =
  PrintCminor.name_of_binop

let rec expr p (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Evar id ->
      fprintf p "%s" (ident_name id)
  | Econst(Ointconst n) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Econst(Ofloatconst f) ->
      fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Econst(Osingleconst f) ->
      fprintf p "%.15Ff" (camlfloat_of_coqfloat32 f)
  | Econst(Olongconst n) ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | Eunop(op, a1) ->
      fprintf p "%s %a" (name_of_unop op) expr (prec', a1)
  | Ebinop(op, a1, a2) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_of_binop op) expr (prec2, a2)
  | Eload(chunk, a1) ->
      fprintf p "%s[%a]" (name_of_chunk chunk) expr (0, a1)
  | Eaddrof id -> fprintf p "&%s" (ident_name id)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_expr p e = expr p (0, e)

let rec print_expr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      print_expr_list p (false, rl)

let print_sig p sg =
  List.iter
    (fun t -> fprintf p "%s ->@ " (name_of_type t))
    sg.sig_args;
  match sg.sig_res with
  | None -> fprintf p "void"
  | Some ty -> fprintf p "%s" (name_of_type ty)

let rec just_skips s =
  match s with
  | Sskip -> true
  | Sseq(s1,s2) -> just_skips s1 && just_skips s2
  | _ -> false

let rec print_stmt p s =
  match s with
  | Sskip ->
    fprintf p "/*skip*/;"
  | Sset(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (ident_name id) print_expr e2
  | Sstore(chunk, a1, a2) ->
      fprintf p "@[<hv 2>%s[%a] =@ %a;@]"
              (name_of_chunk chunk) print_expr a1 print_expr a2
  | Scall(None, sg, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Scall(Some id, sg, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@] : @[<hov 0>%a;@]"
                (ident_name id)
                print_expr e1
                print_expr_list (true, el)
                print_sig sg
  | Sbuiltin(None, ef, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@])@ : @[<hov 0>%a@];@]"
                (name_of_external ef)
                print_expr_list (true, el)
	        print_sig (ef_sig ef)
  | Sbuiltin(Some id, ef, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]) : @[<hov 0>%a@];@]"
                (ident_name id)
                (name_of_external ef)
                print_expr_list (true, el)
	        print_sig (ef_sig ef)
  | Sseq(s1,s2) when just_skips s1 && just_skips s2 ->
      ()
  | Sseq(s1, s2) when just_skips s1 ->
      print_stmt p s2
  | Sseq(s1, s2) when just_skips s2 ->
      print_stmt p s1
  | Sseq(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s) ->
      fprintf p "@[<v 2>loop {@ %a@;<0 -2>}@]"
              print_stmt s
  | Sblock(s) ->
      fprintf p "@[<v 3>{{ %a@;<0 -3>}}@]"
              print_stmt s
  | Sexit n ->
      fprintf p "exit %d;" (Nat.to_int n)
  | Sswitch(long, e, cases) -> (* FIXME: There's something to do with long here *)
    fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
      print_expr e
      print_cases cases
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (ident_name lbl) print_stmt s1
  | Sgoto lbl ->
      fprintf p "goto %s;" (ident_name lbl)    
  

and print_cases p cases =
  match cases with
  | LSnil ->
      ()
  | LScons(lbl, Sskip, rem) ->
      fprintf p "%a:@ %a"
              print_case_label lbl
              print_cases rem
  | LScons(lbl, s, rem) ->
      fprintf p "@[<v 2>%a:@ %a@]@ %a"
              print_case_label lbl
              print_stmt s
              print_cases rem

and print_case_label p = function
  | None -> fprintf p "default"
  | Some lbl -> fprintf p "case %s" (Z.to_string lbl)


let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then fprintf p ",@ ";
      fprintf p "%s" (ident_name v1);
      print_varlist p (vl, false) 

let name_optid id =
  if id = "" then "" else " " ^ id

let name_cdecl id sz =
  Printf.sprintf "(%s) %s" (Z.to_string sz) id

let print_function p id f =
  fprintf p "@[<hov 4>\"%s\"(@[<hov 0>%a@])@ : @[<hov 0>%a@]@]@ "
            (extern_atom id)
            print_varlist (f.fn_params, true)
            print_sig f.fn_sig;
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  List.iter
    (fun id ->
      fprintf p "register %s;@ " (extern_atom id))
    f.fn_temps;
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_extfun p id ef =
  fprintf p "@[<v 0>extern @[<hov 2>\"%s\" =@ %s :@ %a@]@]@ "
    (extern_atom id) (name_of_external ef) print_sig (ef_sig ef)

let print_init_data p = function
  | Init_int8 i -> fprintf p "int8 %ld" (camlint_of_coqint i)
  | Init_int16 i -> fprintf p "int16 %ld" (camlint_of_coqint i)
  | Init_int32 i -> fprintf p "%ld" (camlint_of_coqint i)
  | Init_int64 i -> fprintf p "%LdLL" (camlint64_of_coqint i)
  | Init_float32 f -> fprintf p "float32 %.15F" (camlfloat_of_coqfloat f)
  | Init_float64 f -> fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Init_space i -> fprintf p "[%s]" (Z.to_string i)
  | Init_addrof(id,off) -> fprintf p "%ld(\"%s\")" (camlint_of_coqint off) (extern_atom id)


let rec print_init_data_list p = function
  | [] -> ()
  | [item] -> print_init_data p item
  | item::rest ->
      (print_init_data p item;
       fprintf p ",";
       print_init_data_list p rest)

let print_globvar p gv =
  if (gv.gvar_readonly) then
    fprintf p "readonly ";
  if (gv.gvar_volatile) then
    fprintf p "volatile ";
  fprintf p "{";
  print_init_data_list p gv.gvar_init;
  fprintf p "}"

let print_globdef p (id, gd) =
  match gd with
  | Gfun(External ef) ->
      print_extfun p id ef
  | Gfun(Internal f) ->
      print_function p id f
  | Gvar gv ->
     fprintf p "var \"%s\" %a\n" (extern_atom id) print_globvar gv

let print_program p prog =
  fprintf p "@[<v 0>";
  if extern_atom prog.prog_main <> "main" then
    fprintf p "= \"%s\"\n" (extern_atom prog.prog_main);
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."