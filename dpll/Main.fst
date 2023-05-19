module Main

open DataTypes
open FStar.List
module O = FStar.Option
open FStar.IO
open DpllPropagation
open OtherFunctions

let test1 = [   [NotVar 1; Var 2]; 
                [NotVar 1; NotVar 3];
                [NotVar 2] ;
                [Var 2; Var 3]
            ]

let test4_false = [
    [NotVar 1];[ Var 1];
]

let test2 = [[Var 2; Var 1]; [Var 3]]

let test3 : (res : formula )=[ [Var 1; Var 4];
    [Var 1; NotVar 3; NotVar 8];
    [ Var 1; Var 8; Var 12];    
    [Var 2; Var 11];
    [NotVar 7; NotVar 3; Var 9];
    [NotVar 7; Var 8; NotVar 9];
    [Var 7; Var 8; NotVar 10];
    [Var 7; Var 10; NotVar 12]]


let rec sat_bkt'    (f: formula { length f > 0 }) 
                    (pre_dpll_t: truth_assignment {(no_vars_in_t_outside_f f pre_dpll_t) })
    : Tot (res: result {
        (Sat? res = true ==> 
            ((length (get_truth_from_result res) = length ( get_vars_in_formula f)) 
            /\ (vars_in_truth_result f (get_truth_from_result res)) 
            /\ ( is_solution f (get_truth_from_result res) = true)))
    /\  
    ((NotSat? res = true) ==> 
           ( forall (whole_t: truth_assignment
                { 
                    (forall (v : variable_info {(List.Tot.contains v pre_dpll_t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    is_solution f whole_t = false))
        })  
       (decreases ((length (get_vars_in_formula f)) - (length pre_dpll_t)))  = 
    lemma_test_9 (get_vars_in_formula f) pre_dpll_t;
    assert(length (get_vars_in_formula f) >= length pre_dpll_t);
    let t = unit_clause_propagation f pre_dpll_t in
    assert((( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v pre_dpll_t)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) ));
    if is_partial_solution f t
    then if are_variables_in_truth_assignment f t
        then 
            let answer = Sat t in
            lemma_test_11 (get_vars_in_formula f) t;
            answer
        else
            let newVariable = get_next_element (get_vars_in_formula f) t in
            let new_var_info_false = {value=false; variable=newVariable} in
            lemma_test_9 (get_vars_in_formula f) t;
            lemma_test_12 (get_vars_in_formula f) t;
            let newT = add_var_to_truth t new_var_info_false in
                let res_1 = sat_bkt' f newT in
                if NotSat? res_1 = true  
                    then 
                        let new_var_info_true = {value=true; variable=newVariable} in
                        assert(( forall (whole_t: truth_assignment{ 
                                    (forall (v : variable_info {(List.Tot.contains v newT)}). ((List.Tot.contains v whole_t)))
                                    /\ are_variables_in_truth_assignment f whole_t 
                                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                                is_solution f whole_t = false));
                        let newT2 = add_var_to_truth t new_var_info_true in
                            let res_2 = sat_bkt' f newT2 in
                            assert((NotSat? res_2 = true) ==> 
                            (forall (b : bool). 
                                ( forall (whole_t: truth_assignment{ 
                                    (forall (v : variable_info {
                                        (List.Tot.contains v (add_var_to_truth t {value=b; variable=newVariable}))}). 
                                        ((List.Tot.contains v whole_t)))
                                    /\ are_variables_in_truth_assignment f whole_t 
                                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                                is_solution f whole_t = false)));

                            assert(count_variables_occurrence t newVariable = 0 /\ List.Tot.contains newVariable (get_vars_in_formula f));

                            assert(forall(whole_t : truth_assignment{
                                (forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v whole_t))
                                /\ are_variables_in_truth_assignment f whole_t
                                /\ length whole_t = length (get_vars_in_formula f)
                            }). ( is_variable_in_assignment whole_t newVariable));
                            res_2
                    else res_1
    else 
    let ress = NotSat in

    assert((exists (c: clause {List.Tot.contains c f}). (is_clause_false_yet t c = true)));

    assert((exists (c: clause {List.Tot.contains c f}). 
        (forall (other_t : truth_assignment{
            forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)
        }). (is_clause_false_yet other_t c = true))));

    assert(forall (other_t : truth_assignment
                        {forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}).
                    (is_partial_solution f other_t = false));
    ress

let lemma_test_13 (f : formula { length f > 0}): Lemma 
    (ensures is_partial_solution f empty_assignment ) = ()           

let sat_bkt (f : formula{length f > 0}) : Tot (res: result {
            ((NotSat? res = true) ==> 
                (forall (some_t: truth_assignment
                    { vars_in_truth_result f some_t   
                    /\ (length (get_vars_in_formula f)) = (length some_t)}). (is_solution f some_t ) = false)) 
            /\
             (Sat? res = true ==> vars_in_truth_result f (get_truth_from_result res) 
                    /\ (length (get_truth_from_result res) = (length (get_vars_in_formula f))) 
                    /\  ( is_solution f (get_truth_from_result res)))
}) =
    let t = empty_assignment in
        lemma_test_13 f;
        sat_bkt' f t

let main = let res = sat_bkt test3 in
                if Sat? res = true
                    then let mess = "True" in
                        print_string mess
                    else let mess = "False" in 
                         print_string mess