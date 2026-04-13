(* einsum_lower.ml — Subscript parser for EINSUM lowering.
   Provides pure parsing logic; all IF1 graph mutation lives in to_if1.ml.

   Grammar supported (NumPy convention):
     subscript   ::= inputs "->" output | inputs   (implicit output)
     inputs      ::= spec ("," spec)*
     spec        ::= letters ("..." letters)?         (optional ellipsis)
     output      ::= [a-z]* | ""                    (empty = scalar result)
*)

(** Parsed einsum subscript. *)
type subscript_info = {
  input_specs  : char list list;
  (** One element per input operand.  Each element is the ordered index
      labels for that operand's dimensions (ellipsis-expanded labels are
      excluded; has_ellipsis tracks their presence). *)
  output_spec  : char list;
  (** Ordered output index labels.  Empty list = scalar result. *)
  has_ellipsis : bool;
  (** True when "..." appears anywhere in the subscript. *)
}

(* --- internal helpers --- *)

(* Strip "..." and collect remaining letter labels from a spec string. *)
let parse_label_spec (part : string) : char list =
  let trimmed = String.trim part in
  (* Remove all '.' characters; keep [a-z]. *)
  String.to_seq trimmed
  |> Seq.filter (fun c -> c >= 'a' && c <= 'z')
  |> List.of_seq

(* Re pattern for "->": split the subscript into lhs and optional rhs. *)
let re_arrow = Re.(compile (str "->"))

(** Parse an einsum subscript string.
    Raises [Failure] on malformed input. *)
let parse_einsum_subscript (s : string) : subscript_info =
  let has_ellipsis =
    Re.(execp (compile (str "..."))) s
  in
  let inp_str, out_str_opt =
    match Re.split re_arrow s with
    | [ inp ]       -> (inp, None)
    | [ inp; out ]  -> (inp, Some out)
    | _             -> failwith ("EINSUM: malformed subscript (multiple \"->\": " ^ s ^ ")")
  in
  let input_parts  = String.split_on_char ',' inp_str in
  let input_specs  = List.map parse_label_spec input_parts in
  let output_spec  =
    match out_str_opt with
    | Some s -> parse_label_spec s
    | None   ->
        (* Implicit output: labels appearing exactly once, in alphabetical order. *)
        let tbl = Hashtbl.create 16 in
        List.iter (fun spec ->
          List.iter (fun c ->
            let n = try Hashtbl.find tbl c with Not_found -> 0 in
            Hashtbl.replace tbl c (n + 1))
            spec)
          input_specs;
        Hashtbl.fold (fun c n acc -> if n = 1 then c :: acc else acc) tbl []
        |> List.sort Char.compare
  in
  { input_specs; output_spec; has_ellipsis }

(** For each unique index label, find the FIRST operand + dimension-index
    where it appears.  Returns an association list sorted by label.
    Result: [(label, (operand_index, dim_index_within_operand)); ...] *)
let index_label_sources (info : subscript_info) : (char * (int * int)) list =
  let tbl = Hashtbl.create 16 in
  List.iteri (fun op_idx spec ->
    List.iteri (fun dim_idx label ->
      if not (Hashtbl.mem tbl label) then
        Hashtbl.add tbl label (op_idx, dim_idx))
      spec)
    info.input_specs;
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) tbl []
  |> List.sort (fun (a, _) (b, _) -> Char.compare a b)

(** Contracted labels: appear in at least one input but NOT in the output. *)
let contracted_labels (info : subscript_info) : char list =
  let in_output = List.sort_uniq Char.compare info.output_spec in
  List.concat info.input_specs
  |> List.sort_uniq Char.compare
  |> List.filter (fun c -> not (List.mem c in_output))

(** Free (output) labels, in output order. *)
let free_labels (info : subscript_info) : char list =
  info.output_spec
