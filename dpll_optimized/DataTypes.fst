module DataTypes

open FStar.List.Tot
module L = FStar.List.Tot

let nat_non_zero = x:int{x > 0}

type literal = 
    | Var : a: nat_non_zero -> literal
    | NotVar : a: nat_non_zero -> literal
    

type clause = c : list literal { length  c > 0}

type variable_info = {value: bool; variable: nat_non_zero}

type formula = f : list clause 
let empty_formula = []


let rec count_variables_occurrence (vars: list variable_info) (v : nat_non_zero) : 
    (res : nat {
        ((res = 1) ==> 
            (L.mem {value = true ; variable=v} vars \/ L.mem {value=false ; variable=v} vars )
            /\ ((List.Tot.mem {value=true ; variable=v} vars ==> (List.Tot.mem {value=false; variable=v} vars = false)))
            /\ (List.Tot.mem {value=false ; variable=v} vars ==> (List.Tot.mem {value=true; variable=v} vars = false)) )
        /\ (res = 0 <==> ((List.Tot.mem {value=true; variable=v} vars = false)
                        /\ (List.Tot.mem {value=false; variable=v} vars = false)) )// (forall (var : variable_info {List.Tot.mem var vars}). (var.variable <> v)))
        /\ (res > 0 <==> ((exists (var: variable_info {List.Tot.mem var vars}). (var.variable = v)) 
                        ) )
     }) = if length vars = 0 
            then 0
            else let x = List.Tot.hd vars in 
                    if x.variable = v 
                        then let ress = count_variables_occurrence (List.Tot.tl vars) v in
                            ress + 1
                        else count_variables_occurrence (List.Tot.tl vars) v


let rec ta_contition (ta : list variable_info) 
    = (forall (var : variable_info {List.Tot.mem var ta}). 
            ( count_variables_occurrence ta var.variable = 1 
            ) )
        /\ (length ta > 0 ==> ta_contition (List.Tot.tl ta))

type truth_assignment = ta : list variable_info { ta_contition ta }

let rec is_variable_in_assignment (t: truth_assignment) (v: nat_non_zero) : Tot (res: bool
    {(res = true <==> 
        (length t >= 1 
        /\ count_variables_occurrence t v = 1 
        /\ (L.mem {value=true ; variable=v} t \/ L.mem {value=false ; variable = v} t)))
    /\  (res = false <==> (count_variables_occurrence t v = 0))
    /\ (res = true ==> (forall (t2 : truth_assignment{
        forall (var: variable_info { List.Tot.mem var t }). (List.Tot.mem var t2)
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


let get_literal_variable (l:literal) : nat_non_zero = match l with
    | Var v -> v
    | NotVar v -> v

let rec get_var_from_assignment (t : truth_assignment) ( v : nat_non_zero{is_variable_in_assignment t v})
    : (res : variable_info 
        { List.Tot.mem res t 
            /\ res.variable = v 
            /\ (forall (other_t : truth_assignment
                {forall (var : variable_info{List.Tot.mem var t}). (List.Tot.mem var other_t)}). 
                (List.Tot.mem res other_t))})
    = let x = List.Tot.hd t in
        if x.variable = v
            then x
            else get_var_from_assignment (List.Tot.tl t) v

let get_literal_value (t: truth_assignment) (l: literal {is_variable_in_assignment t (get_literal_variable l) = true}) 
    : (res: bool) =
        match l with
        | Var v ->  let var_info = get_var_from_assignment t v in
                        var_info.value 
        | NotVar v ->  let var_info = get_var_from_assignment t v in
                            not var_info.value 


let add_var_to_truth (t : truth_assignment) (var : variable_info {count_variables_occurrence t var.variable = 0}) 
    : Tot 
    (res : truth_assignment  {
        is_variable_in_assignment res var.variable
        /\ List.Tot.mem var res
        /\ count_variables_occurrence res var.variable = 1
        /\ (length res = length t + 1) 
        /\ (forall (v : variable_info {List.Tot.mem v res /\ v <> var}). (List.Tot.mem v t))
        /\ (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v res)))
        /\ (forall (v: variable_info {List.Tot.mem v res = false}). 
            ((List.Tot.mem v t = false)))
        /\ (forall (l : literal{ is_variable_in_assignment t (get_literal_variable l) }). 
                (
                    is_variable_in_assignment res (get_literal_variable l)
                    /\ get_literal_value t l = get_literal_value res l))     
    }) =
        let result = var :: t in
            result


let rec remove_variable_from_assignment (t:truth_assignment) (v: nat_non_zero {is_variable_in_assignment t v}) 
        : Tot (res: truth_assignment 
                { (length res = length t - 1) 
                /\ is_variable_in_assignment res v = false
                /\ (forall (v : variable_info {(List.Tot.mem v res)}). ((List.Tot.mem v t)))
                /\ (forall (v: variable_info {List.Tot.mem v t = false}). ((List.Tot.mem v res = false) ))
                /\ (forall (var : variable_info {(is_variable_in_assignment res var.variable)}). 
                            ((is_variable_in_assignment t var.variable)))
                /\ (forall (var: variable_info {is_variable_in_assignment t var.variable = false}). 
                            ((is_variable_in_assignment res var.variable = false) ))
                /\ (forall (var : variable_info {List.Tot.mem var t /\ var.variable <> v}). 
                            (is_variable_in_assignment res var.variable /\ List.Tot.mem var res))
                } )
    
    =  if length t = 1
        then []
        else
            let x = List.Tot.hd t in
                let xs = List.Tot.tl t in
                    assert((forall (v : variable_info {(List.Tot.mem v xs)}). ((List.Tot.mem v t))));
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


type aux_occurence_vector = {lit : literal ; clauses : list clause }

type occurence_vector = oc_v : aux_occurence_vector
    {length oc_v.clauses > 0 /\ (forall (c : clause{L.mem c oc_v.clauses}). (L.mem oc_v.lit c))}
    
let rec occurence_matrix_condition (oc_matrix : list occurence_vector) = 
    (   length oc_matrix > 0 
        ==> 
        (forall (ocv : occurence_vector{L.mem ocv (L.tl oc_matrix)}). 
                (ocv.lit <> (L.hd oc_matrix).lit))
    )
    /\ (length oc_matrix > 0 ==> occurence_matrix_condition (List.Tot.tl oc_matrix))

type occurrence_matrix = oc_matrix : list occurence_vector{
    occurence_matrix_condition oc_matrix 
}
