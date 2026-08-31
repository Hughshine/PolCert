open TilingWitness

let coeff_of_assoc assoc name =
  match List.assoc_opt name assoc with
  | Some coeff -> coeff
  | None -> Camlcoq.Z.zero

let convert_affine_expr names params
    (expr : PlutoTilingValidator.affine_expr) =
  {
    ae_var_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.var_coeffs) names;
    ae_param_coeffs =
      List.map (coeff_of_assoc expr.PlutoTilingValidator.param_coeffs) params;
    ae_const = expr.PlutoTilingValidator.const;
  }

let convert_statement_witness params
    (stmt : PlutoTilingValidator.statement_witness) =
  let rec convert_links prefix = function
    | [] -> []
    | link :: tl ->
        let names = prefix @ stmt.PlutoTilingValidator.original_iterators in
        let expr =
          convert_affine_expr names params link.PlutoTilingValidator.expr
        in
        let link' =
          {
            tl_expr = expr;
            tl_tile_size = link.PlutoTilingValidator.tile_size;
          }
        in
        link' :: convert_links (prefix @ [link.PlutoTilingValidator.parent]) tl
  in
  {
    stw_point_dim =
      Camlcoq.Nat.of_int
        (List.length stmt.PlutoTilingValidator.original_iterators);
    stw_links = convert_links [] stmt.PlutoTilingValidator.links;
  }

let convert_witness (witness : PlutoTilingValidator.witness) =
  List.map (convert_statement_witness witness.PlutoTilingValidator.params)
    witness.PlutoTilingValidator.statements
