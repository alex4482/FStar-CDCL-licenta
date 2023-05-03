module DataTypes

open FStar.List.Tot

let nat_non_zero = x:int{x > 0}

type literal = 
    | Var : a: nat_non_zero -> literal
    | NotVar : a: nat_non_zero -> literal
    

type clause = c : list literal { length  c > 0}

type variable_info = {value: bool; variable: nat_non_zero}

type formula = f : list clause 
let empty_formula = []

//occurence
let rec count_variables_occurrence (vars: list variable_info) (v : nat_non_zero) : 
    (res : nat {
        ((res = 1) ==> 
            ((List.Tot.contains {value=true ; variable=v} vars ==> (List.Tot.contains {value=false; variable=v} vars = false)))
            /\ (List.Tot.contains {value=false ; variable=v} vars ==> (List.Tot.contains {value=true; variable=v} vars = false)) )
        /\ (res = 0 <==> ((List.Tot.contains {value=true; variable=v} vars = false)
                        /\ (List.Tot.contains {value=false; variable=v} vars = false)) )// (forall (var : variable_info {List.Tot.contains var vars}). (var.variable <> v)))
        /\ (res > 0 <==> ((exists (var: variable_info {List.Tot.contains var vars}). (var.variable = v)) 
                        ) )
     }) = if length vars = 0 
            then 0
            else let x = List.Tot.hd vars in 
                    if x.variable = v 
                        then let ress = count_variables_occurrence (List.Tot.tl vars) v in
                            ress + 1
                        else count_variables_occurrence (List.Tot.tl vars) v


let rec ta_contition (ta : list variable_info) 
    = (forall (var : variable_info {List.Tot.contains var ta}). 
            ( count_variables_occurrence ta var.variable = 1 
            ///\ (List.Tot.contains ({value=(not var.value); variable=var.variable}) ta = false)
            ) )
        /\ (length ta > 0 ==> ta_contition (List.Tot.tl ta))

type truth_assignment = ta : list variable_info { ta_contition ta }

let rec is_variable_in_assignment (t: truth_assignment) (v: nat_non_zero) : Tot (res: bool
    {(res = true <==> (length t >= 1 /\ count_variables_occurrence t v = 1 ))
    /\  (res = false <==> (count_variables_occurrence t v = 0))
    /\ (res = true ==> (forall (t2 : truth_assignment{
        forall (var: variable_info { List.Tot.contains var t }). (List.Tot.contains var t2)
            }). (count_variables_occurrence t2 v = 1) ))
    
    }) (decreases t) = 
    if length t = 0
        then false
        else
            let x = List.Tot.hd t in
                let xs = List.Tot.tl t in
                    if x.variable = v
                        then true
                        else is_variable_in_assignment xs v


let add_var_to_truth (t : truth_assignment) (var : variable_info {count_variables_occurrence t var.variable = 0}) 
    : Tot (res : truth_assignment 
        {
            is_variable_in_assignment res var.variable
            /\ List.Tot.contains var res
            /\ count_variables_occurrence res var.variable = 1
            /\ (length res = length t + 1) 
            /\ (forall (v : variable_info {List.Tot.contains v res /\ v <> var}). (List.Tot.contains v t))
            /\ (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v res)))
            /\ (forall (v: variable_info {List.Tot.contains v res = false}). 
    ((List.Tot.contains v t = false)))
                
        }) =
        let result = var :: t in
            result

let rec add_vars_to_truth (t: truth_assignment) ( vs : truth_assignment
        {forall (v : variable_info{List.Tot.contains v vs}). (count_variables_occurrence t v.variable = 0)})
        : Tot ( res : truth_assignment { (forall (var : variable_info{List.Tot.contains var t /\ List.Tot.contains var vs}). (List.Tot.contains var res))
            /\ (forall (v : variable_info
                {count_variables_occurrence t v.variable = 0 && count_variables_occurrence vs v.variable = 0}). 
                (count_variables_occurrence res v.variable = 0))}) (decreases (length vs))
    = if length vs = 0
        then t
        else 
    let x = List.Tot.hd vs in
        let xs = List.Tot.tl vs in
        if length xs = 0
            then add_var_to_truth t x
            else let new_t = add_var_to_truth t x in
                add_vars_to_truth new_t xs 

let get_literal_variable (l:literal) : nat_non_zero = match l with
    | Var v -> v
    | NotVar v -> v


let rec get_var_from_assignment (t : truth_assignment) ( v : nat_non_zero{is_variable_in_assignment t v})
    : (res : variable_info 
        { List.Tot.contains res t 
            /\ res.variable = v 
            /\ (forall (other_t : truth_assignment
                {forall (var : variable_info{List.Tot.contains var t}). (List.Tot.contains var other_t)}). 
                (List.Tot.contains res other_t))})
    = let x = List.Tot.hd t in
        if x.variable = v
            then x
            else get_var_from_assignment (List.Tot.tl t) v

let rec remove_variable_from_assignment (t:truth_assignment) (v: nat_non_zero {is_variable_in_assignment t v}) //{ count_variables_occurrence t v > 0 }) 
        : Tot (res: truth_assignment 
                { (length res = length t - 1) 
                /\ is_variable_in_assignment res v = false
                /\ (forall (v : variable_info {(List.Tot.contains v res)}). ((List.Tot.contains v t)))
                /\ (forall (v: variable_info {List.Tot.contains v t = false}). ((List.Tot.contains v res = false) (* /\ (count_variables_occurrence res v.variable = 0) *)))
                /\ (forall (var : variable_info {(is_variable_in_assignment res var.variable)}). ((is_variable_in_assignment t var.variable)))
                /\ (forall (var: variable_info {is_variable_in_assignment t var.variable = false}). ((is_variable_in_assignment res var.variable = false) (* /\ (count_variables_occurrence res v.variable = 0) *)))
                /\ (forall (var : variable_info {List.Tot.contains var t /\ var.variable <> v}). (is_variable_in_assignment res var.variable /\ List.Tot.contains var res))
                } )
    
    =  if length t = 1
        then []
        else
            let x = List.Tot.hd t in
                let xs = List.Tot.tl t in
                    assert((forall (v : variable_info {(List.Tot.contains v xs)}). ((List.Tot.contains v t))));
                    if x.variable = v 
                        then let result = xs in
                            result
                        else
                            let new_t = remove_variable_from_assignment xs v in
                            let res_t = add_var_to_truth new_t x in 
                                res_t

val empty_assignment : (t:truth_assignment { length t = 0 })
let empty_assignment = []

type result =
    | NotSat
    | Sat : a: truth_assignment{ length a > 0} -> result