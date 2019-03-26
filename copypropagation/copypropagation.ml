open Bap.Std

exception TODO

let is_var = function
  | Bil.Var v -> true
  | _ -> false

let gather_copies sub =
  Term.enum blk_t sub |> Seq.fold ~init: Var.Map.empty ~f: (fun v' blk ->
      let v' = Term.enum phi_t blk
               |> Seq.filter ~f: (fun p -> Phi.values p |> Seq.length = 1)
               |> Seq.fold ~init: v' ~f: (fun v' phi ->
                   (* Assume the type of the value is var  *)
                   let _, value = Phi.values phi |> Seq.hd_exn in
                   Var.Map.add v' ~key: (Phi.lhs phi) ~data: value) in
      let v' = Term.enum def_t blk |> Seq.fold ~init: v' ~f: (fun v' def ->
          let rhs = Def.rhs def in
          if is_var rhs then
            Var.Map.add v' ~key: (Def.lhs def) ~data: rhs
          else
            v'
        ) in
      v'
    )

let rec find_leaf vars v = match Var.Map.find vars v with
  | Some (Bil.Var v') -> find_leaf vars v'
  | _ -> v

let replace vars =
  Exp.map (object(self)
    inherit Stmt.mapper as super
    method! map_var v = Bil.Var (find_leaf vars v)
  end)

let replace_vars vars = Blk.map_exp ~f: (replace vars)

let copypropagation sub =
  let module CFG = Graphs.Cfg in
  let open Graphlib.Std in
  let cfg = Sub.to_cfg sub in
  let vars = gather_copies sub in
  Graphs.Ir.nodes cfg
  |> Seq.fold ~init: cfg ~f: (fun _cfg node ->
      let blk = replace_vars vars @@ Graphs.Ir.Node.label node in
      Graphs.Ir.Node.update node blk _cfg)
  |> Sub.of_cfg

let main proj =
  Project.program proj
  |> Term.map sub_t ~f: copypropagation
  |> Project.with_program proj

let () = Project.register_pass ~deps: ["myssa"] main
