module Main

open DataTypes
open DataTypesFunctions
open DpllPropagation
open ConflictFunctions
open OtherFunctions

let sat_cdcl'   (f: formula { length f > 0 }) 
                (t: truth_assignment {(no_vars_in_t_outside_f f t) })
                (level : nat)
    : Tot (res: result {
        (Sat? res = true ==> 
            ((length (get_truth_from_result res) = length ( get_vars_in_formula f)) 
            /\ (vars_in_truth_result f (get_truth_from_result res)) 
            /\ ( is_solution f (get_truth_from_result res) = true)))
    ///\  
    // ((NotSat? res = true) ==> 
    //        ( forall (whole_t: truth_assignment
    //             { 
    //                 (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
    //             /\ are_variables_in_truth_assignment f whole_t 
    //             /\ length whole_t =  length ( get_vars_in_formula f)}). 
    //                 is_solution f whole_t = false))
         })  
       (decreases ((length (get_vars_in_formula f)) - (length t)))  = 
    let all_lits = get_literals_in_formula f in
    let new_t_1 = propagate f t level in
        if exists_conflict f new_t_1
        then 
            if level = 0
            then NotSat
            else
            ///ALREADY HAVE LEMMA SOMEWHERE FOR IF_IS_SOLUTION_FOR_BIGGER_FORMULA THEN SMALLER FORMULA IS ALSO SAT
                let (new_f, new_t_2, new_level) = solve_conflict f new_t_1 level (get_conflict_clause f new_t_1) in
                if exists_unassigned_literal new_f new_t_2 
                then
                    let lit = get_unassigned_literal new_f new_t_2 in
                    let new_t_3 = assign_literal_true lit new_t_2 new_level in
                        // assert((exists (l : literal). 
                        // (   L.contains l all_lits 
                        //     /\ is_variable_in_assignment (get_literal_variable l)
                        //     /\ get_literal_variable l = get_literal_variable lit
                        //     /\ get_literal_value new_t_3 l = false ))
                        //     ==> (L.contains (negate_lit lit) all_lits));
                        sat_cdcl' new_f new_t_3 new_level
                else 
                    Sat new_t_2
        else 
            if exists_unassigned_literal f new_t_1 
            then
                let lit = get_unassigned_literal new_f new_t_2 in
                let new_t_2 = assign_literal_true lit new_t_1 level in
                    sat_cdcl' f new_t_2 (level + 1)
            else Sat new_t_1


let sat_cdcl (f : formula{length f > 0}) : Tot (res: result {
            // ((NotSat? res = true) ==> 
            //     (forall (some_t: truth_assignment
            //         { vars_in_truth_result f some_t   
            //         /\ (length (get_vars_in_formula f)) = (length some_t)}). (is_solution f some_t ) = false)) 
            // /\
             (Sat? res = true ==> vars_in_truth_result f (get_truth_from_result res) 
                    /\ (length (get_truth_from_result res) = (length (get_vars_in_formula f))) 
                    /\  ( is_solution f (get_truth_from_result res)))
}) =
    let t = empty_assignment in
        lemma_test_13 f;
        sat_cdcl' f t 0
        

let main = 3