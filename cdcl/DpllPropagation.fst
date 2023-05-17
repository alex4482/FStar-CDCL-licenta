module DpllPropagation

open FStar.List
open DataTypes
open DataTypesFunctions
open OtherFunctions
module L = FStar.List.Tot

////////////functions for propagation of unit clauses case 
let propagate_unit_clause ( cl : clause) (t: truth_assignment) (current_level :nat) 
    : (res : truth_assignment{
        (length res = length t || length res = length t + 1)
        /\ (forall (v : variable_info{L.contains v t}). (L.contains v res)) 
    })
    =
    let literals = get_unassigned_literals_from_clause cl t in
        if length literals <> 1
        then t
        else 
            if is_clause_true_yet t cl
            then t
            else 
                let x = L.hd literals in
                let x_variable = get_literal_variable x in
                if Var? x 
                then add_var_to_truth t {value = true; variable= x_variable;  level= current_level}
                else add_var_to_truth t {variable = x_variable; value = false; level = current_level}

let rec unit_clause_propagation (f : formula{length f > 0}) (t : truth_assignment) (current_level : nat) 
    : (res : truth_assignment{
        (forall (v : variable_info{L.contains v t}). (L.contains v res)) 
    })
    =
        if length f = 1
        then propagate_unit_clause (L.hd f) t current_level
        else 
            let x = L.hd f in
            let new_t = propagate_unit_clause x t current_level in
            unit_clause_propagation (L.tl f) new_t current_level

//////pure literal propagation functions
///could delete clauses with pure literals, but might not be ok, so keeping them

//repeat remove until no more?
let rec remove_non_pure_literals (all_lits : list literal) 
    : Tot (res : list literal{
        (forall (lit : literal {L.contains lit res}). (L.contains lit all_lits))
    }) (decreases (length all_lits))
    =  if length all_lits = 0 then [] else
        let x = L.hd all_lits in
        let xs = L.tl all_lits in
        let negated_x = negate_lit x in
        if L.contains negated_x xs
        then
            let new_xs = remove_literal_from_list xs negated_x in
            assert((forall (lit : literal{L.contains lit xs}). (L.contains lit all_lits)));
            assert((forall (lit : literal{L.contains lit new_xs}). (L.contains lit xs)));
            remove_non_pure_literals new_xs 
        else x :: (remove_non_pure_literals xs)


let find_one_polarity_literals (f : formula) : (res: list literal)
    =
    let all_literals = get_literals_in_formula f in
    let pure_literals = remove_non_pure_literals all_literals in
    pure_literals

let rec assign_all_literals_true_in_truth (t : truth_assignment) (l : list literal) (current_level : nat) 
    : Tot (res : truth_assignment 
        {
            (forall (v : variable_info{L.contains v t}). (L.contains v res))
            /\ (length res <= length t + length l)
            /\ (forall (lit : literal{L.contains lit l}). (is_variable_in_assignment res (get_literal_variable lit)))
        }) (decreases (length l)) =
    if length l = 0
    then t
    else
        let head = L.hd l in
        let exist = is_variable_in_assignment t (get_literal_variable head) in
            if exist
            then assign_all_literals_true_in_truth t (L.tl l) current_level
            else
                let new_t = assign_literal_true head t current_level in
                assign_all_literals_true_in_truth new_t (L.tl l) current_level

// let rec assign_all_literals_true_in_truth (t : truth_assignment) (l : list literal{
//     forall (lit : literal{L.contains lit l}). (is_variable_in_assignment t lit = false)
// }) (current_level : nat) 
//     : Tot (res : truth_assignment 
//         {
//             (forall (v : variable_info{L.contains v t}). (L.contains v res))
//             /\ (length res = length t + length l)
//             /\ (forall (lit : literal{L.contains lit l}). (is_variable_in_assignment res (get_literal_variable lit)))
//         }) (decreases (length l)) =
//     if length l = 0
//     then t
//     else
//         let head = L.hd l in
//      //   let exist = is_variable_in_assignment t (get_literal_variable head) in
//        //     if exist
//          //   then assign_all_literals_true_in_truth t (L.tl l) current_level
//            // else
//                 let new_t = add_var_to_truth t 
//                     {variable = (get_literal_variable head);
//                     value = (Var? head); level = current_level} in
//                 assign_all_literals_true_in_truth new_t (L.tl l) current_level


let pure_literal_elimination (f : formula) ( t : truth_assignment) ( guess_level : nat)
//    : (res_f, res_t : formula & truth_assignment) (decreases (length f)) =
    : (res : truth_assignment {forall (v : variable_info{L.contains v t}). (L.contains v res)}) =
    let literals_found = find_one_polarity_literals f in
        if length literals_found = 0
       // then (f, t)
        then t
        else 
           // let new_f = eliminate_clauses_containing_literals f literals_found in
            let new_t = assign_all_literals_true_in_truth t literals_found guess_level in
               // (new_f, new_t)
                new_t

let propagate (f : formula{length f > 0}) ( t : truth_assignment) (current_level : nat) 
    : (res : truth_assignment {forall (v : variable_info{L.contains v t}). (L.contains v res)}) =
//    let (new_f, new_t) = pure_literal_elimination f t current_level in
    let new_t = pure_literal_elimination f t current_level in
    //let new_t_2 = unit_clause_propagation new_f new_t current_level in
    let new_t_2 = unit_clause_propagation f new_t current_level in
        new_t_2 
