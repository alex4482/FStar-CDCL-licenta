module OccurenceMatrixUtils

open FStar.List.Tot
module L = FStar.List.Tot

open DataTypes
open DataTypeUtils
open DpllPropagation

let rec is_lit_in_occurence_matrix ( oc_matrix : occurrence_matrix) ( l : literal)
    : (res : bool 
        {(res <==> 
            ((exists (oc_v : occurence_vector {L.mem oc_v oc_matrix}). (oc_v.lit = l))))
        /\ (res = false <==> (forall (oc_v : occurence_vector{L.mem oc_v oc_matrix}). (oc_v.lit <> l)))
        })
    = 
    if length oc_matrix = 0 
    then false
    else
        let x = L.hd oc_matrix in
            if x.lit = l
            then true
            else is_lit_in_occurence_matrix (L.tl oc_matrix) l

let rec get_occurence_vector_for_lit (oc_matrix : occurrence_matrix) (l : literal{
    (exists (oc_v : occurence_vector {L.mem oc_v oc_matrix}). (oc_v.lit = l))
}) : (res : occurence_vector{
    res.lit = l 
    /\ L.mem res oc_matrix
    /\ (forall (c : clause{L.mem c res.clauses}). (L.mem l c))
}) =
    let x = L.hd oc_matrix in
    if x.lit = l
    then 
        let ress = x in
        assert(forall (c : clause{L.mem c x.clauses}). (L.mem x.lit c));
        assert(x.lit = l);
        ress
    else let ress = get_occurence_vector_for_lit (L.tl oc_matrix) l in
        ress


let rec get_clauses_for_literal (f : formula ) (lit : literal ) 
    : (res : list clause{
        (forall (c : clause{L.mem c res}). (L.mem lit c))
        /\ (forall (c : clause{L.mem c f /\ L.mem lit c}). (L.mem c res))
        /\ (forall (c : clause{L.mem c res}). (L.mem c f))
        /\ ((exists (c : clause{L.mem c f}). (L.mem lit c )) <==> length res > 0)
    }) =
    if length f = 0
    then []
    else
        let h = L.hd f in
        let temp_res = get_clauses_for_literal (L.tl f) lit in
            if L.mem lit h 
            then 
                let ress = h :: temp_res in
                assert(forall (c : clause{L.mem c temp_res}). (L.mem c ress));
                assert(L.mem h ress);
                assert(L.mem h f);
                assert(forall (c : clause{L.mem c temp_res}). (L.mem c (L.tl f)));
                assert(forall (c : clause{L.mem c (L.tl f)}). (L.mem c f));
                assert(L.mem lit h);
                assert(forall (c : clause{L.mem c temp_res}). (L.mem lit h));
                assert(forall (c : clause{L.mem c ress}). (L.mem lit h));
                ress
            else temp_res


let rec get_occurence_matrix_helper 
    (f : formula {length f > 0}) 
    (lits : list literal{
        L.noRepeats lits
        /\ (forall (l : literal {L.mem l lits}). ( L.mem l (get_lits_in_formula f) /\ is_lit_in_formula f l))
    }) 
    : (res : occurrence_matrix{
        length res = length lits
        /\ (forall (l : literal{L.mem l lits}). (is_lit_in_occurence_matrix res l))
        /\ (forall (oc_v : occurence_vector{L.mem oc_v res}). (L.mem oc_v.lit lits) )
        /\ (forall (oc_v : occurence_vector {L.mem oc_v res}). (
            forall (c : clause {L.mem c oc_v.clauses}). (L.mem c f)
        ))

        /\ (forall (oc_v : occurence_vector {L.mem oc_v res}). 
            (forall (c : clause {L.mem c f /\ (L.mem c oc_v.clauses = false)}). (L.mem oc_v.lit c = false)))
    })
    = 
    if length lits = 0 
    then []
    else
        let cls = get_clauses_for_literal f (L.hd lits) in
        assert(is_lit_in_formula f (L.hd lits));
        assert(exists (c : clause{L.mem c f}). (L.mem (L.hd lits) c));
        assert(length cls > 0);

        let new_oc_v = {lit = (L.hd lits) ; clauses = cls} in
        let temp_res = get_occurence_matrix_helper f (L.tl lits) in
        assert(L.mem (L.hd lits) (L.tl lits) = false);
        assert(forall (oc : occurence_vector { L.mem oc temp_res}). (oc.lit <> (L.hd lits)));
        assert(forall (oc : occurence_vector{L.mem oc temp_res}). (L.mem oc.lit lits));

        let ress = new_oc_v :: temp_res in
            assert(L.hd lits = new_oc_v.lit);
            assert(L.hd lits = (L.hd ress).lit);
            assert(length ress = length lits);
            assert(forall (oc_v : occurence_vector{L.mem oc_v temp_res}). (L.mem oc_v ress));
            assert(L.mem new_oc_v ress);
            assert(exists (oc_v : occurence_vector{L.mem oc_v ress}). (oc_v.lit = (L.hd lits)));
            assert((forall (l : literal{L.mem l (L.tl lits)}). 
                (exists (oc_v : occurence_vector{L.mem oc_v ress}). (oc_v.lit = l))));

            assert(L.mem new_oc_v ress);

            [@@inline_let]
            let h = L.hd lits in
            assert(new_oc_v.lit = h);
            assert(L.mem h lits);
            assert(occurence_matrix_condition temp_res);
            assert(occurence_matrix_condition ress);

            assert(is_lit_in_occurence_matrix ress h);
            assert(length ress = length lits);
            assert( length ress = length lits);

            assert( (forall (l : literal{L.mem l (L.tl lits)}). (is_lit_in_occurence_matrix temp_res l)));
            assert( (forall (l : literal{L.mem l (L.tl lits)}). (is_lit_in_occurence_matrix ress l)));

            assert( (forall (l : literal{L.mem l lits}). (is_lit_in_occurence_matrix ress l)));
            assert((forall (oc_v : occurence_vector{L.mem oc_v ress}). (L.mem oc_v.lit lits) ));
            ress


let get_occurence_matrix (f : formula {length f > 0}) : (res : occurrence_matrix{
        length res = length (get_lits_in_formula f)
        /\ (forall (l : literal{L.mem l (get_lits_in_formula f)}). (is_lit_in_occurence_matrix res l))
        /\ (forall (oc_v : occurence_vector{L.mem oc_v res}). (L.mem oc_v.lit (get_lits_in_formula f)) )
        /\ (forall (oc_v : occurence_vector {L.mem oc_v res}). (
            forall (c : clause {L.mem c oc_v.clauses}). (L.mem c f)
        ))
        /\ (forall (oc_v : occurence_vector {L.mem oc_v res}). 
            (forall (c : clause {L.mem c f /\ (L.mem c oc_v.clauses = false)}). (L.mem oc_v.lit c = false)))
    })
    =
    let lits = get_lits_in_formula f in
    get_occurence_matrix_helper f lits


let rec get_clauses_of_lit 
    (f : formula {length f > 0}) 
    (oc_matrix : occurrence_matrix {(forall (ocv : occurence_vector {L.mem ocv oc_matrix}). (L.mem ocv (get_occurence_matrix f)))}) 
    (lit : literal {is_lit_in_occurence_matrix oc_matrix lit})
    : (res : list clause {
        length res > 0 
        /\ (forall (c : clause{L.mem c res}). (L.mem lit c))
        /\ (exists (oc : occurence_vector{L.mem oc oc_matrix}). (oc.lit = lit /\ oc.clauses = res))
        })
    = let x = L.hd oc_matrix in
    if x.lit = lit
    then x.clauses
    else let ress = get_clauses_of_lit f (L.tl oc_matrix) lit in
        ress

let rec intersect_lists (l1 : list clause) ( l2 : list clause) : (res : list clause {
    length res = length l1 + length l2
    /\ (forall (c : clause{L.mem c l1}). (L.mem c res))
    /\ (forall (c : clause{L.mem c l2}). (L.mem c res))
    /\ (forall (c : clause{L.mem c res}). (L.mem c l1 \/ L.mem c l2))
}) =
    if length l1 = 0
    then l2
    else
        let x = L.hd l1 in
        intersect_lists (L.tl l1) (x :: l2)

let rec any_lit_from_list_in_clause (c : clause) (lits : list literal) :(res : bool{
   ( res <==> (exists (l : literal{L.mem l lits}). (L.mem l c))) /\
   (res = false <==> (forall (l : literal {L.mem l lits}). (L.mem l c = false)))
})
    =
    if length lits = 0
    then false
    else
        if L.mem (L.hd lits) c
        then true
        else any_lit_from_list_in_clause c (L.tl lits)    


let rec get_clauses_with_new_lits
    (f : formula {length f > 0})
    (oc_matrix : occurrence_matrix {oc_matrix = get_occurence_matrix f}) 
    (lits : list literal)
    : (res : list clause {
        ((exists (l : literal{L.mem l lits}). (is_lit_in_occurence_matrix oc_matrix l)) ==> length res > 0)
        /\ (forall (c : clause{ L.mem c res}). (
            any_lit_from_list_in_clause c lits
            /\ L.mem c f
            ))
        /\ (forall (c : clause {L.mem c f /\ (L.mem c res = false)}). (any_lit_from_list_in_clause c lits = false))
        })
    = 
    if length lits = 0
    then []
    else 
        let lit = L.hd lits in
            if is_lit_in_occurence_matrix oc_matrix lit = false
            then 
                let ress = get_clauses_with_new_lits f oc_matrix (L.tl lits) in
                assert(
                    (forall (l : literal{L.mem l (get_lits_in_formula f)}). (is_lit_in_occurence_matrix oc_matrix l))
                );
                assert(forall (l : literal {is_lit_in_occurence_matrix oc_matrix l = false}). 
                    (L.mem l (get_lits_in_formula f) = false));
                assert(L.mem lit (get_lits_in_formula f) = false);

                assert(forall (l : literal {L.mem l (get_lits_in_formula f) = false }). (
                    is_lit_in_formula f l = false
                ));

                assert(is_lit_in_formula f lit = false);
                ress
            else
                let clauses = get_clauses_of_lit f oc_matrix lit in
                assert(forall (c : clause{L.mem c clauses}). (L.mem c f));
                assert(forall (c : clause{L.mem c clauses}). (L.mem lit c));
                assert(L.mem lit lits);
                assert(forall (c : clause{L.mem c clauses}). (
                    any_lit_from_list_in_clause c lits
                ));
                let tl_lits = L.tl lits in
                let temp_res = get_clauses_with_new_lits f oc_matrix tl_lits in
                assert((forall (c : clause{ L.mem c temp_res}). (
                    any_lit_from_list_in_clause c tl_lits)));

                assert(forall (l : literal{L.mem l (L.tl lits)}). (L.mem l lits));
                assert((forall (c : clause{ L.mem c temp_res}). (
                    any_lit_from_list_in_clause c lits)));

                let ress = intersect_lists clauses temp_res in
                assert(forall (c : clause{L.mem c clauses}). (L.mem c ress));
                assert(forall (c : clause{L.mem c temp_res}). (L.mem c ress));
                assert(forall (c : clause {L.mem c ress}). (L.mem c clauses \/ L.mem c temp_res));
                assert(forall (c : clause{L.mem c clauses \/ L.mem c temp_res}). (
                any_lit_from_list_in_clause c lits
                ));
                assert(forall (c : clause{L.mem c ress}). (
                any_lit_from_list_in_clause c lits
                ));

                assert((forall (c : clause {L.mem c f /\ (L.mem c temp_res = false)}). (any_lit_from_list_in_clause c tl_lits = false)));

                assert(forall (c : clause {L.mem c f /\ L.mem c clauses = false}). (
                    L.mem lit c = false
                ));

                assert((forall (oc_v : occurence_vector {L.mem oc_v oc_matrix}). (
                    forall (c : clause {L.mem c oc_v.clauses}). (L.mem c f)
                )));

                assert(forall (c : clause {L.mem c temp_res \/ L.mem c clauses}). (L.mem c ress));
                assert(forall (c : clause {L.mem c ress}). (L.mem c temp_res \/ L.mem c clauses));

                assert((forall (c : clause {L.mem c f /\ (L.mem c ress = false)}). (any_lit_from_list_in_clause c tl_lits = false)));

                assert((forall (c : clause {L.mem c f /\ (L.mem c ress = false)}). (any_lit_from_list_in_clause c lits = false)));
                ress

let is_partial_solution_optimized 
    (f : formula { length f > 0}) 
    (pre_dpll_t : truth_assignment { 
        length pre_dpll_t >= 1
        /\ no_variables_outside_f_are_in_t f pre_dpll_t
        /\ length (get_vars_in_formula f) >= length pre_dpll_t 
        /\ (is_partial_solution f (L.tl pre_dpll_t))
        }
    )
    (t : truth_assignment ) 
    (oc_matrix : occurrence_matrix {oc_matrix = get_occurence_matrix f}) 
    (new_l : literal {
        is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable new_l) = false
        /\ L.mem (get_literal_variable new_l) (get_vars_in_formula f)
        /\ is_variable_in_assignment pre_dpll_t (get_literal_variable new_l)
        /\ get_literal_value pre_dpll_t new_l
        /\ t = (unit_clause_propagation f pre_dpll_t new_l )._1 
        /\ pre_dpll_t = add_var_to_truth (L.tl pre_dpll_t) {value = Var? new_l ; variable = (get_literal_variable new_l)}
    })
    (new_lits : list literal{
        L.mem new_l new_lits /\
        length new_lits > 0
        /\ ((forall (l : literal {L.mem l new_lits}). 
                (is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l) = false
                /\ is_variable_in_assignment t (get_literal_variable l))) )
        /\ (forall (l : literal {
                is_variable_in_assignment t (get_literal_variable l)
                /\ (L.mem l (negate_lits_list new_lits) = false) 
                /\ (L.mem l new_lits = false)}).
                (is_variable_in_assignment pre_dpll_t (get_literal_variable l)))
        /\ (forall (l : literal{L.mem l new_lits}). 
                (get_literal_value t l 
                /\ (L.mem (negate_lit l) new_lits = false)))
        /\ (forall (c : clause {
                    L.mem c f 
                    /\ any_lit_from_list_in_clause c new_lits }). 
                (is_clause_true_yet t c))      

        /\ (forall (l : literal {
            is_variable_in_assignment pre_dpll_t (get_literal_variable l)
            }). (get_literal_value t l = get_literal_value pre_dpll_t l))
    }) 
    : (res : bool{
        (res <==> partial_solution f t)
        /\ ((res = false) <==> (exists (c : clause{List.Tot.mem c f}). (is_clause_false_yet t c)))
})  =
    if length t = 0 
        then true
        else
            let smaller_f = get_clauses_with_new_lits f oc_matrix (negate_lits_list new_lits) in
                let not_res = exists_false_clause_yet smaller_f t in

                assert(forall (var : variable_info{L.mem var pre_dpll_t}). (L.mem var t));
                assert(forall (var : nat_non_zero{ is_variable_in_assignment pre_dpll_t var}). (is_variable_in_assignment t var));
                assert(forall (l : literal {L.mem l new_lits}). 
                    (is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l) = false
                    /\ is_variable_in_assignment t (get_literal_variable l)));
                
                assert(forall (var : nat_non_zero{ is_variable_in_assignment pre_dpll_t var}). 
                    (is_variable_in_assignment t var));

                assert(
                    forall (c : clause{
                        L.mem c f 
                        /\ (any_lit_from_list_in_clause c new_lits = false)
                        /\ (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false)}). 
                        (forall (l : literal{L.mem l c}). (
                            is_variable_in_assignment pre_dpll_t (get_literal_variable l) 
                                = is_variable_in_assignment t (get_literal_variable l)))
                    );

                assert(
                    forall (c : clause{
                        L.mem c f 
                       /\ (any_lit_from_list_in_clause c new_lits = false)
                        /\ (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false)
                        }). 
                        (forall (l : literal{
                            L.mem l c 
                            /\ is_variable_in_assignment pre_dpll_t (get_literal_variable l)}). (
                                get_literal_value pre_dpll_t l = get_literal_value t l
                        ))
                    );

                assert(
                    forall (c : clause{
                        L.mem c f 
                        /\ (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false)
                        }). 
                        (forall (l : literal{ L.mem l c }). (
                                (is_variable_in_assignment pre_dpll_t (get_literal_variable l) 
                                    ==> (is_variable_in_assignment t (get_literal_variable l) 
                                        /\ get_literal_value pre_dpll_t l = get_literal_value t l))
                                
                        ))
                    );

                assert(
                    forall (c : clause{
                        L.mem c f 
                        /\ (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false)
                        }). 
                        (is_clause_false_yet pre_dpll_t c = is_clause_false_yet t c)
                );

                assert(forall (c : clause{ L.mem c f 
                        /\ (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false)}). (
                    L.mem c smaller_f = false
                ));

                assert(forall (c : clause{ L.mem c smaller_f  }). (
                     (any_lit_from_list_in_clause c (negate_lits_list new_lits) )
                ));

                assert(forall (c : clause{ L.mem c f /\ L.mem c smaller_f = false  }). (
                     (any_lit_from_list_in_clause c (negate_lits_list new_lits) = false )
                ));

                assert(forall (c : clause{L.mem c f /\ (L.mem c smaller_f = false)}). (
                    (L.mem (negate_lit new_l) c = false)
                ));

                assert(forall (c : clause {L.mem c f 
                        /\ any_lit_from_list_in_clause c new_lits
                        }). (is_clause_false_yet t c = false /\ is_clause_true_yet t c));

                assert(forall (c : clause{L.mem c f /\ (L.mem c smaller_f = false)}). (
                    is_clause_false_yet pre_dpll_t c = is_clause_false_yet t c
                ));

                assert(
                     (forall (c : clause {
                        L.mem c f
                        /\ (L.mem new_l c = false) 
                        /\ (L.mem (negate_lit new_l) c = false) }). 
                    (
                        forall (l : literal {L.mem l c}). (
                            is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l) = 
                            is_variable_in_assignment pre_dpll_t (get_literal_variable l)
                        )
                    ))
                );

                assert(forall (l : literal {is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l)}). 
                    (
                        is_variable_in_assignment pre_dpll_t (get_literal_variable l)
                        /\ get_literal_value (L.tl pre_dpll_t) l = get_literal_value pre_dpll_t l
                    ));

                assert(
                     (forall (c : clause {
                        L.mem c f
                        /\ (L.mem new_l c = false) 
                        /\ (L.mem (negate_lit new_l) c = false) 
                        }). 
                    (
                        forall (l : literal {L.mem l c /\ is_variable_in_assignment pre_dpll_t (get_literal_variable l)}). (
                            get_literal_value (L.tl pre_dpll_t) l = 
                            get_literal_value pre_dpll_t l
                        )
                    ))
                );

                assert(
                    forall (c : clause { L.mem c f  }). 
                        ((is_clause_false_yet (L.tl pre_dpll_t) c = false)
                        /\ (exists (l : literal {L.mem l c}). 
                        ((is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l) = false) 
                            \/ get_literal_value (L.tl pre_dpll_t) l)))
                );

                assert(
                    (forall (c : clause {
                        L.mem c f
                        /\ (L.mem new_l c = false) 
                        /\ (L.mem (negate_lit new_l) c = false) }). 
                    (   L.mem c f
                        /\ (is_clause_false_yet (L.tl pre_dpll_t) c = false) 
                        /\ (exists (l : literal {L.mem l c}). 
                        ((is_variable_in_assignment (L.tl pre_dpll_t) (get_literal_variable l) = false) 
                            \/ get_literal_value (L.tl pre_dpll_t) l)))
                ));

                assert(
                    (forall (c : clause {
                        L.mem c f
                        /\ (L.mem new_l c = false) 
                        /\ (L.mem (negate_lit new_l) c = false) }). 
                    (is_clause_false_yet pre_dpll_t c = is_clause_false_yet (L.tl pre_dpll_t) c))
                );

                assert(
                    forall (c : clause {
                            L.mem c f 
                            /\ (L.mem new_l c ) }). 
                        (is_clause_true_yet pre_dpll_t c )
                );

                assert(forall (c : clause{L.mem c f /\ (L.mem c smaller_f = false)}). (
                    is_clause_false_yet pre_dpll_t c = false
                ));

                assert(forall (c : clause {L.mem c smaller_f}). (L.mem c f));
                assert(
                    not_res <==> 
                    (exists (c : clause{L.mem c smaller_f }). (is_clause_false_yet t c))
                );

                assert(
                    not_res <==> 
                    (exists (c : clause{L.mem c smaller_f }). (L.mem c f /\ is_clause_false_yet t c))
                );

                assert(forall (c : clause {L.mem c f 
                    /\ (any_lit_from_list_in_clause c new_lits)}). ( is_clause_false_yet t c = false ));

                 assert(forall (c : clause {L.mem c f }). 
                    (is_clause_false_yet (L.tl pre_dpll_t) c = false));

                assert((exists (c : clause{L.mem c smaller_f }). (is_clause_false_yet t c))
                    <==>
                    (exists (c : clause{L.mem c f }). (is_clause_false_yet t c))
                    );

                assert(not_res <==> (exists (c : clause{L.mem c f }). (is_clause_false_yet t c)));

                not not_res
