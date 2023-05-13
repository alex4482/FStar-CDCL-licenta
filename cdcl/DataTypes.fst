module DataTypes

module L = FStar.List.Tot

let nat_non_zero = x:int{x > 0}

type literal = 
    | Var : a: nat_non_zero -> literal
    | NotVar : a: nat_non_zero -> literal
    

type clause = c : list literal { L.length c > 0}

type variable_info = {value: bool; variable: nat_non_zero; level: nat}

type formula = f : list clause 
let empty_formula = []

let rec contains_var_info (vars : list variable_info) (value : bool) (var : nat_non_zero) =
    if L.length vars = 0 then false
        else
        let x = L.hd vars in
            if x.variable = var && x.value = value
                then true
                else contains_var_info (L.tl vars) value var

let rec count_variables_occurrence (vars: list variable_info) (v : nat_non_zero) : 
    (res : nat {
        ((res = 1) ==> 
            (contains_var_info vars true v 
                ==> (contains_var_info vars false v = false))
            /\ (contains_var_info vars false v 
                ==> (contains_var_info vars true v  = false)) )
        /\ (res = 0 <==> ((contains_var_info vars true v = false)
                        /\ (contains_var_info vars false v  = false)) )
        /\ (res > 0 <==> ((exists (var: variable_info {List.Tot.contains var vars}). (var.variable = v)) 
                        ) )
     }) = if L.length vars = 0 
            then 0
            else let x = List.Tot.hd vars in 
                    if x.variable = v 
                        then let ress = count_variables_occurrence (List.Tot.tl vars) v in
                            ress + 1
                        else count_variables_occurrence (List.Tot.tl vars) v


let rec ta_contition (ta : list variable_info) 
    = (forall (var : variable_info {List.Tot.contains var ta}). 
            ( count_variables_occurrence ta var.variable = 1 
            ) )
        /\ (L.length ta > 0 ==> ta_contition (List.Tot.tl ta))

type truth_assignment = ta : list variable_info { ta_contition ta }

type result =
    | NotSat
    | Sat : a: truth_assignment{ L.length a > 0} -> result

