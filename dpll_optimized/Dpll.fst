module Dpll

open DataTypes
open DataTypeUtils
open DpllPropagation
open OccurenceMatrixUtils

open FStar.IO
open FStar.List
module L = FStar.List.Tot


let get_most_recent_var_added (t : truth_assignment{
        length t > 0
        /\ t = add_var_to_truth (L.tl t) (L.hd t)
    }) 
    : (res : literal{
        ((Var? res = (L.hd t).value )
            /\ (get_literal_variable res = (L.hd t).variable))
    })
    =   let x = L.hd t in
            if x.value
            then Var (x.variable)
            else NotVar x.variable


let rec dpll'   (f: formula { length f > 0 }) 
                (pre_dpll_t: truth_assignment {
                    length pre_dpll_t > 0 
                    /\ no_variables_outside_f_are_in_t f (L.tl pre_dpll_t)
                    /\ (partial_solution f (L.tl pre_dpll_t))
                    /\ no_variables_outside_f_are_in_t f pre_dpll_t
                    /\ pre_dpll_t = add_var_to_truth (L.tl pre_dpll_t) (L.hd pre_dpll_t)
                })
                (oc_matrix : occurrence_matrix {oc_matrix = get_occurence_matrix f})
    : Tot (res: result {
        (Sat? res = true ==> 
            ((length (get_truth_from_result res) = length ( get_vars_in_formula f)) 
            /\ (all_variables_are_in_truth_assignment f (get_truth_from_result res)) 
            /\ ( is_solution f (get_truth_from_result res) = true)))
        /\  
        ((NotSat? res = true) ==> 
            ( forall (whole_t: truth_assignment
                    { 
                        (forall (v : variable_info {(List.Tot.mem v pre_dpll_t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                        is_solution f whole_t = false))
        })  
       (decreases ((length (get_vars_in_formula f)) - (length pre_dpll_t)))  = 
    lemma_no_vars_in_t_outside_f_length_compare (get_vars_in_formula f) pre_dpll_t;
    //assert(length (get_vars_in_formula f) >= length pre_dpll_t);
    let recent_var = get_most_recent_var_added pre_dpll_t in
    let t_lits = unit_clause_propagation f pre_dpll_t recent_var in
    let t = fst t_lits in
    let new_lits = snd t_lits in
    
    assert(
        (   ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v pre_dpll_t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
            )
    );

    if is_partial_solution_optimized f pre_dpll_t t oc_matrix recent_var new_lits 
    then if are_variables_in_truth_assignment f t
        then 
            let answer = Sat t in
            lemma_truth_and_variable_list_length_equality (get_vars_in_formula f) t;
            answer
        else
            let newVariable = get_next_element (get_vars_in_formula f) t in
            let new_var_info_false = {value=false; variable=newVariable} in
            lemma_no_vars_in_t_outside_f_length_compare (get_vars_in_formula f) t;
            lemma_length_truth_smaller_length_variable_list (get_vars_in_formula f) t;
            let newT = add_var_to_truth t new_var_info_false in
                let res_1 = dpll' f newT oc_matrix in
                if NotSat? res_1 = true  
                    then 
                        let new_var_info_true = {value=true; variable=newVariable} in
                        assert(( forall (whole_t: truth_assignment{ 
                                    (forall (v : variable_info {(List.Tot.mem v newT)}). ((List.Tot.mem v whole_t)))
                                    /\ are_variables_in_truth_assignment f whole_t 
                                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                                is_solution f whole_t = false));
                        let newT2 = add_var_to_truth t new_var_info_true in
                            let res_2 = dpll' f newT2 oc_matrix in
                            assert((NotSat? res_2 = true) ==> 
                            (forall (b : bool). 
                                ( forall (whole_t: truth_assignment{ 
                                    (forall (v : variable_info {
                                        (List.Tot.mem v (add_var_to_truth t {value=b; variable=newVariable}))}). 
                                        ((List.Tot.mem v whole_t)))
                                    /\ are_variables_in_truth_assignment f whole_t 
                                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                                is_solution f whole_t = false)));

                            assert(count_variables_occurrence t newVariable = 0 /\ List.Tot.mem newVariable (get_vars_in_formula f));

                            assert(forall(whole_t : truth_assignment{
                                (forall (v : variable_info{List.Tot.mem v t}). (List.Tot.mem v whole_t))
                                /\ are_variables_in_truth_assignment f whole_t
                                /\ length whole_t = length (get_vars_in_formula f)
                            }). ( is_variable_in_assignment whole_t newVariable));
                            res_2
                    else res_1
    else 
    let ress = NotSat in

    assert((exists (c: clause {List.Tot.mem c f}). (is_clause_false_yet t c = true)));

    assert((exists (c: clause {List.Tot.mem c f}). 
        (forall (other_t : truth_assignment{
            forall (v : variable_info{List.Tot.mem v t}). (List.Tot.mem v other_t)
        }). (is_clause_false_yet other_t c = true))));

    assert(forall (other_t : truth_assignment
                        {forall (v : variable_info{List.Tot.mem v t}). (List.Tot.mem v other_t)}).
                    (is_partial_solution f other_t = false));
    ress


let lemma_empty_truth_partial_solution (f : formula { length f > 0}): Lemma 
    (ensures is_partial_solution f empty_assignment ) = ()           


let dpll (f : formula{length f > 0}) : Tot (res: result {
            ((NotSat? res = true) ==> 
                (forall (some_t: truth_assignment
                    { all_variables_are_in_truth_assignment f some_t   
                    /\ (length (get_vars_in_formula f)) = (length some_t)}). (is_solution f some_t ) = false)) 
            /\
             (Sat? res = true ==> all_variables_are_in_truth_assignment f (get_truth_from_result res) 
                    /\ (length (get_truth_from_result res) = (length (get_vars_in_formula f))) 
                    /\  ( is_solution f (get_truth_from_result res)))
}) =
    let t = empty_assignment in
        lemma_empty_truth_partial_solution f;
        let oc_matrix = get_occurence_matrix f in
            assert(length t = 0);
            assert(is_variable_in_assignment t (L.hd (get_vars_in_formula f)) = false);
            assert(exists (n : nat_non_zero {L.mem n (get_vars_in_formula f)}). (is_variable_in_assignment t n = false));
            let newVariable = get_next_element (get_vars_in_formula f) t in
            let new_var_info_false = {value=false; variable=newVariable} in
            lemma_no_vars_in_t_outside_f_length_compare (get_vars_in_formula f) t;
            lemma_length_truth_smaller_length_variable_list (get_vars_in_formula f) t;
            let newT = add_var_to_truth t new_var_info_false in
            let res_1 = dpll' f newT oc_matrix in
                if NotSat? res_1 = true  
                then 
                    let new_var_info_true = {value=true; variable=newVariable} in
                        assert(( forall (whole_t: truth_assignment{ 
                                (forall (v : variable_info {(List.Tot.mem v newT)}). ((List.Tot.mem v whole_t)))
                                /\ are_variables_in_truth_assignment f whole_t 
                                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                            is_solution f whole_t = false));
                    let newT2 = add_var_to_truth t new_var_info_true in
                    let res_2 = dpll' f newT2 oc_matrix in
                        assert((NotSat? res_2 = true) ==> 
                        (forall (b : bool). 
                            ( forall (whole_t: truth_assignment{ 
                                (forall (v : variable_info {
                                    (List.Tot.mem v (add_var_to_truth t {value=b; variable=newVariable}))}). 
                                    ((List.Tot.mem v whole_t)))
                                /\ are_variables_in_truth_assignment f whole_t 
                                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                            is_solution f whole_t = false)));

                        assert(count_variables_occurrence t newVariable = 0 /\ List.Tot.mem newVariable (get_vars_in_formula f));

                        assert(forall(whole_t : truth_assignment{
                            (forall (v : variable_info{List.Tot.mem v t}). (List.Tot.mem v whole_t))
                            /\ are_variables_in_truth_assignment f whole_t
                            /\ length whole_t = length (get_vars_in_formula f)
                        }). ( is_variable_in_assignment whole_t newVariable));
                        res_2
                else res_1


