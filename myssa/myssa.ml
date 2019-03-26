open Bap.Std

module StrMap = Map.Make(String)
let global_gen = ref StrMap.empty
let reset_gen () = global_gen := StrMap.empty

let get_name_with name_tbl v =
  let n = Var.name v in
  let g = match StrMap.find_opt n name_tbl with
  | Some g -> g
  | None -> 0 in
  Printf.sprintf "%s.%d" n g

let next_gen v =
  let n = Var.name v in
  let g_opt = StrMap.find_opt n !global_gen in
  match g_opt with
  | Some g ->
    let next = g + 1 in
    let _ = global_gen := StrMap.add n next !global_gen in
    next
  | None ->
    let next = 1 in
    let _ = global_gen := StrMap.add n next !global_gen in
    next

let rename name v =
  let ty = Var.typ v in
  Var.create name ty

let rename_exp_with name_tbl =
  Exp.map (object(self)
    inherit Stmt.mapper as super
    method! map_var v =
      let name = get_name_with name_tbl v in
      Bil.Var (rename name v)
  end)

let update_rhs_tbl for_rhs lhs_name lhs_gen = for_rhs := StrMap.add lhs_name lhs_gen !for_rhs

let handle_lhs v for_rhs =
  let orig_name = Var.name v in
  let next_gen = next_gen v in
  update_rhs_tbl for_rhs orig_name next_gen;
  let ret = rename (Printf.sprintf "%s.%d" orig_name next_gen) v in
  ret

let seen = ref Blk.Set.empty
let walk_block blk _for_rhs =
  if Blk.Set.mem !seen blk then
    blk
  else
    let _ = seen := Blk.Set.add !seen blk in
    let for_rhs = ref _for_rhs in
    let blk_phi = Term.map phi_t blk ~f: (fun phi ->
        let lhs =
          let lhs_var = Phi.lhs phi in
          handle_lhs lhs_var for_rhs in
        Phi.with_lhs phi lhs) in
    let blk_def = Term.map def_t blk_phi ~f: (fun def ->
        let rhs = rename_exp_with !for_rhs @@ Def.rhs def in
        let lhs =
          let lhs_var = Def.lhs def in
          handle_lhs lhs_var for_rhs in
        Def.create lhs rhs) in
    let blk_jmp = Term.map jmp_t blk_def ~f: (Jmp.map_exp ~f: (fun e -> rename_exp_with !for_rhs e)) in
    blk_jmp

let gather_vars blk =
  let vars = Term.enum phi_t blk
             |> Seq.fold ~init: Var.Set.empty ~f: (fun vs phi ->
                 Var.Set.add vs @@ Phi.lhs phi
               ) in
  let vars = Term.enum def_t blk
             |> Seq.fold ~init: vars ~f: (fun vs def ->
                 Var.Set.union vs @@ Def.free_vars def) in
  let vars = Term.enum jmp_t blk
             |> Seq.fold ~init: vars ~f: (fun vs j ->
                 Var.Set.union vs @@ Jmp.free_vars j) in
  vars

let orig_name_of ssa_var =
  (* Assume '.' is not contained in the name *)
  let name = Var.name ssa_var in
  let ret = String.split_on_char '.' name |> List.hd in
  ret

let popo parent n v =
  let parent_tid = Term.tid @@ Graphs.Ir.Node.label parent in
  let blk = Graphs.Ir.Node.label n in
  let original = orig_name_of v in
  let target_opt = Term.enum phi_t blk
                   |> Seq.filter ~f: (fun phi ->
                       let match_var = original = (orig_name_of @@ Phi.lhs phi) in
                       let match_blk =
                         match Phi.select phi parent_tid with
                         | Some _ -> true
                         | None -> false in
                       match_var && match_blk
                     )
                   |> Seq.hd in
  (* TODO Error handling *)
  match target_opt with
  | Some phi ->
    let e = Bil.var v in
    let new_phi = Phi.update phi parent_tid e in
    Graphs.Ir.Node.create @@ Term.update phi_t blk new_phi
  | None -> n


(* TODO Check the variables which will be put in phi are latest version  *)
let replace_empty_phis cfg targets entry =
  let vars = gather_vars (Graphs.Ir.Node.label entry) in
  Seq.fold targets ~init: cfg ~f: (fun cfg fnode ->
      let repl = Var.Set.fold vars ~init: fnode ~f: (fun n v -> popo entry n v) in
      Graphs.Ir.Node.update fnode (Graphs.Ir.Node.label repl) cfg
    )

let ssa_no_phi cfg domtree =
  let open Graphlib.Std in
  Graphs.Ir.nodes cfg
  |> Seq.fold ~init: cfg ~f: (fun _cfg node ->
      let children = Tree.children domtree node in
      replace_empty_phis _cfg children node)

let entry_ssa cfg node =
    let new_node = walk_block (Graphs.Ir.Node.label node) !global_gen in
    Graphs.Ir.Node.update node new_node cfg

let domtree cfg =
  let open Graphlib.Std in
  let entry_blk = Graphs.Ir.nodes cfg |> Seq.hd_exn in
  Graphlib.dominators (module Graphs.Ir) cfg entry_blk

let blk_to_ssa cfg node =
  let open Graphlib.Std in
  let ssa_entry = entry_ssa cfg node in
  let no_phi = ssa_no_phi ssa_entry (domtree ssa_entry) in
  no_phi


let replace_empty_phis_dom cfg dom_frontiers node =
  let targets = Graphlib.Std.Frontier.enum dom_frontiers node in
  replace_empty_phis cfg targets node

let put_phis node preds =
  let vars =
    Seq.cons node preds
    |> Seq.fold ~init: Var.Set.empty ~f: (fun vs n ->
        let blk = Graphs.Ir.Node.label n in
        Var.Set.union vs @@ gather_vars blk) in
  let blk = Graphs.Ir.Node.label node in
  Var.Set.fold vars ~init: blk ~f: (fun blk v ->
      let is_defined = Term.enum phi_t blk
                       |> Seq.exists ~f: (fun p ->
                           Var.name v = Var.name @@ Phi.lhs p) in
      if is_defined then
        blk
      else
        let unk = Bil.unknown "empty phi" (Var.typ v) in
        let bindings = Seq.map preds ~f: (fun n ->
            let pred_tid = Term.tid (Graphs.Ir.Node.label n) in
            pred_tid, unk) |> Seq.to_list in
        let phi = Phi.of_list v bindings in
          Term.append phi_t blk phi
    ) |> Graphs.Ir.Node.create

let put_phis_to_blk cfg =
    Graphs.Ir.nodes cfg
    |> Seq.fold ~init: cfg ~f: (fun cfg node ->
        let preds = Graphs.Ir.Node.preds node cfg in
        let new_node = put_phis node preds in
        Graphs.Ir.Node.update node (Graphs.Ir.Node.label new_node) cfg
      )

let redefine blk vars =
  Var.Set.fold vars ~init: blk ~f: (fun blk var ->
      let unk = Bil.unknown "call" (Var.typ var) in
      let def = Def.create var unk in
      Term.append def_t blk def
    )

let end_with_call blk = 
  let open Monads.Std.Monad.Option.Syntax in
  match Term.first jmp_t blk >>| Jmp.kind with
  | Some (Call call) -> true
  | _ -> false

let add_side_effects_blk all_vars blk =
  if end_with_call blk then
    redefine blk all_vars
  else
    blk

let add_side_effects all_vars cfg =
  let open Graphs.Ir in
  nodes cfg
  |> Seq.fold ~init: cfg ~f: (fun cfg node ->
      let new_blk = add_side_effects_blk all_vars @@ Node.label node in
      Node.update node new_blk cfg)

let remove_empties phi =
  let remove_list = Phi.values phi
  |> Seq.filter_map ~f: (function
      | t, Bil.Unknown _ -> Some t
      | _ -> None) in
  Seq.fold remove_list ~init: phi ~f: (fun p t ->
      Phi.remove p t)

let remove_phis cfg =
  Graphs.Ir.nodes cfg
  |> Seq.fold ~init: cfg ~f: (fun _cfg node ->
      let new_blk =
        let blk = Graphs.Ir.Node.label node in
        Term.map phi_t blk ~f: remove_empties in
      Graphs.Ir.Node.update node new_blk _cfg)


(* XXX Refs: https://github.com/BinaryAnalysisPlatform/bap/blob/fd205a26dd21959afda298e02741c8d66d7772f7/lib/bap_sema/bap_sema_ssa.ml *)
let myssa_form = Value.Tag.register
    ~uuid:"9abecd51-c6c3-4363-b9c6-51f923d965ff"
    ~name:"myssa_form"
    (module Core_kernel.Unit)

let ssa sub =
  if Term.has_attr sub myssa_form then
    sub
  else
    let open Graphlib.Std in
    let module CFG = Graphs.Cfg in
    reset_gen ();
    let cfg =
      let _cfg = Sub.to_cfg sub in
      let all_vars = Graphs.Ir.nodes _cfg
                     |> Seq.fold ~init: Var.Set.empty ~f: (fun vs n ->
                         Var.Set.union vs @@ gather_vars (Graphs.Ir.Node.label n))
                     |> Var.Set.filter ~f: (fun v -> not @@ Var.is_virtual v) in
      add_side_effects all_vars @@ put_phis_to_blk _cfg in
    let ssa_no_phi = Graphs.Ir.nodes cfg
                     |> Seq.fold ~init: cfg ~f: (fun cfg node -> blk_to_ssa cfg node) in
    let ssa_phi = Graphs.Ir.nodes ssa_no_phi
                  |> Seq.fold ~init: ssa_no_phi ~f: (fun ssa_no_phi node ->
                      let succs = Graphs.Ir.Node.succs node ssa_no_phi in
                      replace_empty_phis ssa_no_phi succs node) in
    let final = remove_phis ssa_phi in
    let sub = Sub.of_cfg final in
    Term.set_attr sub myssa_form ()

let main proj =
  Project.program proj
  |> Term.map sub_t ~f:ssa
  |> Project.with_program proj

let () = Project.register_pass main
