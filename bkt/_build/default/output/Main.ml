open Prims
let (test1 : DataTypes.literal Prims.list Prims.list) =
  [[DataTypes.NotVar Prims.int_one; DataTypes.Var (Prims.of_int (2))];
  [DataTypes.NotVar Prims.int_one; DataTypes.NotVar (Prims.of_int (3))];
  [DataTypes.NotVar (Prims.of_int (2))];
  [DataTypes.Var (Prims.of_int (2)); DataTypes.Var (Prims.of_int (3))]]
let (test4_false : DataTypes.literal Prims.list Prims.list) =
  [[DataTypes.NotVar Prims.int_one]; [DataTypes.Var Prims.int_one]]
let (test2 : (DataTypes.literal * DataTypes.literal) Prims.list Prims.list) =
  [[((DataTypes.Var (Prims.of_int (2))), (DataTypes.Var Prims.int_one))]]
let (test3 : DataTypes.literal Prims.list Prims.list) =
  [[DataTypes.Var Prims.int_one; DataTypes.Var (Prims.of_int (4))];
  [DataTypes.Var Prims.int_one;
  DataTypes.NotVar (Prims.of_int (3));
  DataTypes.NotVar (Prims.of_int (8))];
  [DataTypes.Var Prims.int_one;
  DataTypes.Var (Prims.of_int (8));
  DataTypes.Var (Prims.of_int (12))];
  [DataTypes.Var (Prims.of_int (2)); DataTypes.Var (Prims.of_int (11))];
  [DataTypes.NotVar (Prims.of_int (7));
  DataTypes.NotVar (Prims.of_int (3));
  DataTypes.Var (Prims.of_int (9))];
  [DataTypes.NotVar (Prims.of_int (7));
  DataTypes.Var (Prims.of_int (8));
  DataTypes.NotVar (Prims.of_int (9))];
  [DataTypes.Var (Prims.of_int (7));
  DataTypes.Var (Prims.of_int (8));
  DataTypes.NotVar (Prims.of_int (10))];
  [DataTypes.Var (Prims.of_int (7));
  DataTypes.Var (Prims.of_int (10));
  DataTypes.NotVar (Prims.of_int (12))]]
let (get_literal_variable : DataTypes.literal -> DataTypes.nat_non_zero) =
  fun l -> match l with | DataTypes.Var v -> v | DataTypes.NotVar v -> v
let rec (get_max_var_in_clause :
  DataTypes.clause -> DataTypes.nat_non_zero -> DataTypes.nat_non_zero) =
  fun c ->
    fun max_var ->
      match c with
      | [] -> max_var
      | x::xs ->
          let v = get_literal_variable x in
          if v > max_var
          then get_max_var_in_clause xs v
          else get_max_var_in_clause xs max_var
let rec (get_max_var_in_formula' :
  DataTypes.formula -> DataTypes.nat_non_zero -> DataTypes.nat_non_zero) =
  fun f ->
    fun max_var ->
      match f with
      | [] -> max_var
      | x::xs ->
          let max_var_clause = get_max_var_in_clause x Prims.int_one in
          if max_var_clause > max_var
          then get_max_var_in_formula' xs max_var_clause
          else get_max_var_in_formula' xs max_var
let (get_max_var_in_formula : DataTypes.formula -> DataTypes.nat_non_zero) =
  fun f -> get_max_var_in_formula' f Prims.int_one
let rec (is_variable_in_assignment :
  DataTypes.truth_assignment -> DataTypes.nat_non_zero -> Prims.bool) =
  fun t ->
    fun v ->
      match t with
      | [] -> false
      | x::xs ->
          if x.DataTypes.variable = v
          then true
          else is_variable_in_assignment xs v
let (are_variables_in_truth_assignment :
  DataTypes.formula -> DataTypes.truth_assignment -> Prims.bool) =
  fun f ->
    fun t ->
      FStar_List_Tot_Base.for_all
        (fun c ->
           FStar_List_Tot_Base.for_all (is_variable_in_assignment t)
             (FStar_List_Tot_Base.map get_literal_variable c)) f
let rec (get_variable_info_in_assignment :
  DataTypes.truth_assignment ->
    DataTypes.nat_non_zero -> DataTypes.variable_info)
  =
  fun t ->
    fun var ->
      match t with
      | x::[] -> x
      | x::xs ->
          if x.DataTypes.variable = var
          then x
          else get_variable_info_in_assignment xs var
let (get_literal_value :
  DataTypes.truth_assignment -> DataTypes.literal -> Prims.bool) =
  fun t ->
    fun l ->
      let v = get_literal_variable l in
      match l with
      | DataTypes.Var uu___ ->
          let var_info = get_variable_info_in_assignment t v in
          var_info.DataTypes.value
      | DataTypes.NotVar uu___ ->
          let var_info = get_variable_info_in_assignment t v in
          Prims.op_Negation var_info.DataTypes.value
let rec (get_values_from_clause :
  DataTypes.truth_assignment -> DataTypes.clause -> Prims.bool Prims.list) =
  fun t ->
    fun c ->
      match c with
      | [] -> []
      | x::xs -> (get_literal_value t x) :: (get_values_from_clause t xs)
let (get_clause_value :
  DataTypes.truth_assignment -> DataTypes.clause -> Prims.bool) =
  fun t ->
    fun c -> FStar_List_Tot_Base.contains true (get_values_from_clause t c)
let (is_clause_false_yet :
  DataTypes.truth_assignment -> DataTypes.clause -> Prims.bool) =
  fun t ->
    fun c ->
      if
        (FStar_List_Tot_Base.for_all (is_variable_in_assignment t)
           (FStar_List_Tot_Base.map get_literal_variable c))
          = false
      then false
      else Prims.op_Negation (get_clause_value t c)
let rec (get_formula_value :
  DataTypes.truth_assignment -> DataTypes.formula -> Prims.bool) =
  fun t ->
    fun f ->
      match f with
      | x::[] -> get_clause_value t x
      | x::xs -> (get_clause_value t x) && (get_formula_value t xs)
let (is_partial_solution :
  DataTypes.formula -> DataTypes.truth_assignment -> Prims.bool) =
  fun f -> fun t -> FStar_List_Tot_Base.existsb (is_clause_false_yet t) f
let (is_solution :
  DataTypes.formula -> DataTypes.truth_assignment -> Prims.bool) =
  fun f ->
    fun t ->
      ((FStar_List_Tot_Base.length t) = (get_max_var_in_formula f)) &&
        (get_formula_value t f)
let (get_truth_from_result : DataTypes.result -> DataTypes.truth_assignment)
  = fun r -> match r with | DataTypes.Sat t -> t
let rec (sat_bkt' :
  DataTypes.formula -> DataTypes.truth_assignment -> DataTypes.result) =
  fun f ->
    fun t ->
      if (FStar_List_Tot_Base.length t) = (get_max_var_in_formula f)
      then
        (if (are_variables_in_truth_assignment f t) && (is_solution f t)
         then DataTypes.Sat t
         else DataTypes.NotSat)
      else
        (let newVariable = (FStar_List_Tot_Base.length t) + Prims.int_one in
         let newT =
           FStar_List_Tot_Base.snoc
             (t,
               { DataTypes.value = false; DataTypes.variable = newVariable }) in
         if (is_partial_solution f newT) = true
         then
           let res_1 = sat_bkt' f newT in
           (if (DataTypes.uu___is_NotSat res_1) = true
            then
              let newT2 =
                FStar_List_Tot_Base.snoc
                  (t,
                    {
                      DataTypes.value = true;
                      DataTypes.variable = newVariable
                    }) in
              (if (is_partial_solution f newT2) = true
               then sat_bkt' f newT2
               else DataTypes.NotSat)
            else res_1)
         else
           (let newT2 =
              FStar_List_Tot_Base.snoc
                (t,
                  { DataTypes.value = true; DataTypes.variable = newVariable
                  }) in
            if (is_partial_solution f newT2) = true
            then sat_bkt' f newT2
            else DataTypes.NotSat))
let (sat_bkt : DataTypes.formula -> DataTypes.result) =
  fun f ->
    let t = DataTypes.empty_assignment in
    if is_partial_solution f t then sat_bkt' f t else DataTypes.NotSat
let (main : unit) =
  let res = sat_bkt test3 in
  if (DataTypes.uu___is_Sat res) = true
  then FStar_IO.print_string "True"
  else FStar_IO.print_string "False"