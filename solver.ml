let ltrue = 1
let lfalse = -1
let nvars = ref 1
let nclauses = ref 0
let oc = ref stdout
let fresh () = incr nvars; !nvars
let lit l = output_string !oc (string_of_int l); output_char !oc ' '
let fin () = output_string !oc "0\n"; incr nclauses
let clause1 a = lit a; fin ()
let clause2 a b = lit a; lit b; fin ()
let clause3 a b c = lit a; lit b; lit c; fin ()
let lnot l = -l
let land_ a b =
  if a = lfalse || b = lfalse || a = -b then lfalse
  else if a = ltrue || a = b then b else if b = ltrue then a
  else let v = fresh () in clause2 (-v) a; clause2 (-v) b; clause3 v (-a) (-b); v
let lor_ a b = -(land_ (-a) (-b))
let lxor_ a b =
  if a = lfalse then b else if b = lfalse then a
  else if a = ltrue then -b else if b = ltrue then -a
  else if a = b then lfalse else if a = -b then ltrue
  else let v = fresh () in
    clause3 (-v) a b; clause3 (-v) (-a) (-b); clause3 v (-a) b; clause3 v a (-b); v
let and3 a b c = land_ (land_ a b) c
let and4 a b c d = land_ (and3 a b c) d
let or3 a b c = lor_ (lor_ a b) c
let or4 a b c d = lor_ (or3 a b c) d

let cell name : string list * (int array -> int) =
  let n = lnot in
  match name with
  | "inv" -> ["A"], (fun a -> n a.(0))
  | "buf" | "clkbuf" -> ["A"], (fun a -> a.(0))
  | "nand2" -> ["A"; "B"], (fun a -> n (land_ a.(0) a.(1)))
  | "nand2b" -> ["A_N"; "B"], (fun a -> n (land_ (n a.(0)) a.(1)))
  | "nand3" -> ["A"; "B"; "C"], (fun a -> n (and3 a.(0) a.(1) a.(2)))
  | "nand3b" -> ["A_N"; "B"; "C"], (fun a -> n (and3 (n a.(0)) a.(1) a.(2)))
  | "nand4" -> ["A"; "B"; "C"; "D"], (fun a -> n (and4 a.(0) a.(1) a.(2) a.(3)))
  | "nor2" -> ["A"; "B"], (fun a -> n (lor_ a.(0) a.(1)))
  | "nor3" -> ["A"; "B"; "C"], (fun a -> n (or3 a.(0) a.(1) a.(2)))
  | "nor3b" -> ["A"; "B"; "C_N"], (fun a -> n (or3 a.(0) a.(1) (n a.(2))))
  | "nor4" -> ["A"; "B"; "C"; "D"], (fun a -> n (or4 a.(0) a.(1) a.(2) a.(3)))
  | "nor4b" -> ["A"; "B"; "C"; "D_N"], (fun a -> n (or4 a.(0) a.(1) a.(2) (n a.(3))))
  | "and2" -> ["A"; "B"], (fun a -> land_ a.(0) a.(1))
  | "and2b" -> ["A_N"; "B"], (fun a -> land_ (n a.(0)) a.(1))
  | "and3" -> ["A"; "B"; "C"], (fun a -> and3 a.(0) a.(1) a.(2))
  | "and3b" -> ["A_N"; "B"; "C"], (fun a -> and3 (n a.(0)) a.(1) a.(2))
  | "and4" -> ["A"; "B"; "C"; "D"], (fun a -> and4 a.(0) a.(1) a.(2) a.(3))
  | "and4b" -> ["A_N"; "B"; "C"; "D"], (fun a -> and4 (n a.(0)) a.(1) a.(2) a.(3))
  | "and4bb" -> ["A_N"; "B_N"; "C"; "D"], (fun a -> and4 (n a.(0)) (n a.(1)) a.(2) a.(3))
  | "or2" -> ["A"; "B"], (fun a -> lor_ a.(0) a.(1))
  | "or3" -> ["A"; "B"; "C"], (fun a -> or3 a.(0) a.(1) a.(2))
  | "or3b" -> ["A"; "B"; "C_N"], (fun a -> or3 a.(0) a.(1) (n a.(2)))
  | "or4" -> ["A"; "B"; "C"; "D"], (fun a -> or4 a.(0) a.(1) a.(2) a.(3))
  | "or4b" -> ["A"; "B"; "C"; "D_N"], (fun a -> or4 a.(0) a.(1) a.(2) (n a.(3)))
  | "or4bb" -> ["A"; "B"; "C_N"; "D_N"], (fun a -> or4 a.(0) a.(1) (n a.(2)) (n a.(3)))
  | "xor2" -> ["A"; "B"], (fun a -> lxor_ a.(0) a.(1))
  | "xnor2" -> ["A"; "B"], (fun a -> n (lxor_ a.(0) a.(1)))
  | "mux2" -> ["S"; "A1"; "A0"], (fun a -> lor_ (land_ a.(0) a.(1)) (land_ (n a.(0)) a.(2)))
  | "a21o" -> ["A1"; "A2"; "B1"], (fun a -> lor_ (land_ a.(0) a.(1)) a.(2))
  | "a21oi" -> ["A1"; "A2"; "B1"], (fun a -> n (lor_ (land_ a.(0) a.(1)) a.(2)))
  | "a21bo" -> ["A1"; "A2"; "B1_N"], (fun a -> lor_ (land_ a.(0) a.(1)) (n a.(2)))
  | "a21boi" -> ["A1"; "A2"; "B1_N"], (fun a -> n (lor_ (land_ a.(0) a.(1)) (n a.(2))))
  | "a22o" -> ["A1"; "A2"; "B1"; "B2"], (fun a -> lor_ (land_ a.(0) a.(1)) (land_ a.(2) a.(3)))
  | "a22oi" -> ["A1"; "A2"; "B1"; "B2"], (fun a -> n (lor_ (land_ a.(0) a.(1)) (land_ a.(2) a.(3))))
  | "a31o" -> ["A1"; "A2"; "A3"; "B1"], (fun a -> lor_ (and3 a.(0) a.(1) a.(2)) a.(3))
  | "a31oi" -> ["A1"; "A2"; "A3"; "B1"], (fun a -> n (lor_ (and3 a.(0) a.(1) a.(2)) a.(3)))
  | "a32o" -> ["A1"; "A2"; "A3"; "B1"; "B2"], (fun a -> lor_ (and3 a.(0) a.(1) a.(2)) (land_ a.(3) a.(4)))
  | "a41oi" -> ["A1"; "A2"; "A3"; "A4"; "B1"], (fun a -> n (lor_ (and4 a.(0) a.(1) a.(2) a.(3)) a.(4)))
  | "a211o" -> ["A1"; "A2"; "B1"; "C1"], (fun a -> or3 (land_ a.(0) a.(1)) a.(2) a.(3))
  | "a211oi" -> ["A1"; "A2"; "B1"; "C1"], (fun a -> n (or3 (land_ a.(0) a.(1)) a.(2) a.(3)))
  | "a221o" -> ["A1"; "A2"; "B1"; "B2"; "C1"], (fun a -> or3 (land_ a.(0) a.(1)) (land_ a.(2) a.(3)) a.(4))
  | "a221oi" -> ["A1"; "A2"; "B1"; "B2"; "C1"], (fun a -> n (or3 (land_ a.(0) a.(1)) (land_ a.(2) a.(3)) a.(4)))
  | "a311o" -> ["A1"; "A2"; "A3"; "B1"; "C1"], (fun a -> or3 (and3 a.(0) a.(1) a.(2)) a.(3) a.(4))
  | "a2111oi" -> ["A1"; "A2"; "B1"; "C1"; "D1"], (fun a -> n (or4 (land_ a.(0) a.(1)) a.(2) a.(3) a.(4)))
  | "o21a" -> ["A1"; "A2"; "B1"], (fun a -> land_ (lor_ a.(0) a.(1)) a.(2))
  | "o21ai" -> ["A1"; "A2"; "B1"], (fun a -> n (land_ (lor_ a.(0) a.(1)) a.(2)))
  | "o21ba" -> ["A1"; "A2"; "B1_N"], (fun a -> land_ (lor_ a.(0) a.(1)) (n a.(2)))
  | "o21bai" -> ["A1"; "A2"; "B1_N"], (fun a -> n (land_ (lor_ a.(0) a.(1)) (n a.(2))))
  | "o22a" -> ["A1"; "A2"; "B1"; "B2"], (fun a -> land_ (lor_ a.(0) a.(1)) (lor_ a.(2) a.(3)))
  | "o22ai" -> ["A1"; "A2"; "B1"; "B2"], (fun a -> n (land_ (lor_ a.(0) a.(1)) (lor_ a.(2) a.(3))))
  | "o31a" -> ["A1"; "A2"; "A3"; "B1"], (fun a -> land_ (or3 a.(0) a.(1) a.(2)) a.(3))
  | "o31ai" -> ["A1"; "A2"; "A3"; "B1"], (fun a -> n (land_ (or3 a.(0) a.(1) a.(2)) a.(3)))
  | "o32a" -> ["A1"; "A2"; "A3"; "B1"; "B2"], (fun a -> land_ (or3 a.(0) a.(1) a.(2)) (lor_ a.(3) a.(4)))
  | "o32ai" -> ["A1"; "A2"; "A3"; "B1"; "B2"], (fun a -> n (land_ (or3 a.(0) a.(1) a.(2)) (lor_ a.(3) a.(4))))
  | "o211a" -> ["A1"; "A2"; "B1"; "C1"], (fun a -> and3 (lor_ a.(0) a.(1)) a.(2) a.(3))
  | "o211ai" -> ["A1"; "A2"; "B1"; "C1"], (fun a -> n (and3 (lor_ a.(0) a.(1)) a.(2) a.(3)))
  | "o221a" -> ["A1"; "A2"; "B1"; "B2"; "C1"], (fun a -> and3 (lor_ a.(0) a.(1)) (lor_ a.(2) a.(3)) a.(4))
  | "o311a" -> ["A1"; "A2"; "A3"; "B1"; "C1"], (fun a -> and3 (or3 a.(0) a.(1) a.(2)) a.(3) a.(4))
  | "o2bb2a" -> ["A1_N"; "A2_N"; "B1"; "B2"], (fun a -> land_ (n (land_ a.(0) a.(1))) (lor_ a.(2) a.(3)))
  | _ -> failwith ("unknown cell " ^ name)

type gate = { out : int; ins : int array; fn : int array -> int }
type ff = { q : int; d : int; kind : int }

let base t = match String.rindex_opt t '_' with Some i -> String.sub t 0 i | None -> t

let load path =
  let ids = Hashtbl.create 1024 in
  let id n = match Hashtbl.find_opt ids n with
    | Some i -> i | None -> let i = Hashtbl.length ids in Hashtbl.add ids n i; i in
  List.iter (fun n -> ignore (id n)) ["rst_n"; "enable"; "I"; "success"];
  let ic = open_in path in
  let gates = ref [] and ffs = ref [] and consts = ref [] in
  (try
     while true do
       match String.split_on_char ' ' (String.trim (input_line ic)) with
       | [] | [""] -> ()
       | t :: ps ->
         let pins = List.map (fun s -> match String.split_on_char '=' s with
             | [p; n] -> (p, id n) | _ -> failwith ("bad pin " ^ s)) ps in
         (match base t with
          | "dfrtp" -> ffs := { q = List.assoc "Q" pins; d = List.assoc "D" pins; kind = 0 } :: !ffs
          | "dfstp" -> ffs := { q = List.assoc "Q" pins; d = List.assoc "D" pins; kind = 1 } :: !ffs
          | "dfxtp" -> ffs := { q = List.assoc "Q" pins; d = List.assoc "D" pins; kind = 2 } :: !ffs
          | "conb" -> List.iter (fun (p, n) -> consts := (n, if p = "HI" then ltrue else lfalse) :: !consts) pins
          | "diode" | "tapvpwrvgnd" | "decap" | "fill" -> ()
          | b ->
            let names, fn = cell b in
            let out = match List.assoc_opt "X" pins with Some o -> o | None -> List.assoc "Y" pins in
            gates := { out; ins = Array.of_list (List.map (fun p -> List.assoc p pins) names); fn } :: !gates)
     done
   with End_of_file -> close_in ic);
  let n = Hashtbl.length ids in
  let drv = Array.make n None in
  List.iter (fun g -> drv.(g.out) <- Some g) !gates;
  let seen = Array.make n false and order = ref [] in
  let rec visit net = match drv.(net) with
    | Some g when not seen.(net) ->
      seen.(net) <- true;
      Array.iter (fun m -> if m <> net then visit m) g.ins;
      order := g :: !order
    | _ -> () in
  List.iter (fun g -> visit g.out) !gates;
  (Array.of_list (List.rev !order), Array.of_list !ffs, !consts, n, id)

let () =
  let path = if Array.length Sys.argv > 1 then Sys.argv.(1) else "puzzle_nl.txt" in
  let order, ffs, consts, nnets, id = load path in
  let v = Array.make nnets lfalse in
  let args = Array.make 8 0 in
  let i_rst = id "rst_n" and i_en = id "enable" and i_in = id "I" and i_succ = id "success" in
  let i_out = Array.init 8 (fun k -> id (Printf.sprintf "O[%d]" k)) in
  let reset () =
    Array.fill v 0 nnets lfalse;
    List.iter (fun (n, l) -> v.(n) <- l) consts;
    Array.iter (fun f -> v.(f.q) <- if f.kind = 1 then ltrue else lfalse) ffs in
  let eval rst en i =
    v.(i_rst) <- rst; v.(i_en) <- en; v.(i_in) <- i;
    Array.iter (fun g ->
        for k = 0 to Array.length g.ins - 1 do args.(k) <- v.(g.ins.(k)) done;
        v.(g.out) <- g.fn args) order in
  let step rst en i =
    eval rst en i;
    let nq = Array.map (fun f ->
        let d = v.(f.d) in
        if f.kind = 0 then land_ d rst else if f.kind = 1 then lor_ d (-rst) else d) ffs in
    Array.iteri (fun k f -> v.(f.q) <- nq.(k)) ffs in
  let run bits idle =
    reset ();
    for _ = 1 to 3 do step lfalse lfalse lfalse done;
    step ltrue lfalse lfalse;
    Array.iter (fun b -> step ltrue ltrue b) bits;
    step ltrue ltrue lfalse;
    for _ = 1 to idle do step ltrue lfalse lfalse done;
    eval ltrue lfalse lfalse in
  let cnf = "puzzle.cnf" in
  oc := open_out cnf;
  let header = "p cnf                     \n" in
  output_string !oc header;
  let bits = Array.init 120 (fun _ -> fresh ()) in
  run bits 2;
  clause1 ltrue;
  clause1 v.(i_succ);
  seek_out !oc 0;
  output_string !oc (Printf.sprintf "p cnf %d %d" !nvars !nclauses);
  close_out !oc;
  Printf.printf "CNF: %d vars, %d clauses\n%!" !nvars !nclauses;
  if Sys.command ("z3 -dimacs " ^ cnf ^ " > puzzle.model") <> 0 then failwith "z3 failed";
  let model = Bytes.make (!nvars + 1) '0' and sat = ref false in
  let ic = open_in "puzzle.model" in
  (try while true do
       let line = input_line ic in
       if line = "s SATISFIABLE" then sat := true
       else if String.length line > 0 && line.[0] = 'v' then
         List.iter (fun t -> match int_of_string_opt t with
             | Some l when l > 0 -> Bytes.set model l '1' | _ -> ())
           (String.split_on_char ' ' line)
     done with End_of_file -> close_in ic);
  if not !sat then (print_endline "UNSAT"; exit 1);
  let sol = Array.map (fun b -> Bytes.get model b) bits in
  print_string "bits: "; Array.iter print_char sol; print_newline ();
  oc := open_out Filename.null;
  run (Array.map (fun c -> if c = '1' then ltrue else lfalse) sol) 0;
  let msg = Buffer.create 32 and succ = ref false in
  for _ = 1 to 20 do
    let o = ref 0 in
    Array.iteri (fun k n -> if v.(n) = ltrue then o := !o lor (1 lsl k)) i_out;
    if !o <> 0 then Buffer.add_char msg (Char.chr !o);
    if v.(i_succ) = ltrue then succ := true;
    step ltrue lfalse lfalse;
    eval ltrue lfalse lfalse
  done;
  Printf.printf "success: %b\nmessage: %s\n" !succ (Buffer.contents msg)
