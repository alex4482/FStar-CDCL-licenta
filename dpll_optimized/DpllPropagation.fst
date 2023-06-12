module DpllPropagation

open DataTypes
open DataTypeUtils

open FStar.List
open FStar.Pervasives.Native
module L = FStar.List.Tot
module T = FStar.Pervasives.Native

////////////functions for unit clause propagation

let is_unit_clause (c : clause) ( t : truth_assignment) : (res : bool {
    (res) <==> (
        (length (get_unassigned_literals_from_clause c t) = 1) 
        /\ (forall (l : literal{L.mem l c /\ l <> (L.hd (get_unassigned_literals_from_clause c t))}).
            (is_variable_in_assignment t (get_literal_variable l)))
        /\ (is_clause_true_yet t c = false))
}) =
    let xs = get_unassigned_literals_from_clause c t in
    if length xs = 1 && (is_clause_true_yet t c = false)
    then true
    else false

let rec exists_unit_clause (f : formula) ( t : truth_assignment) : (res : bool{
    (res <==> (exists (c : clause{L.mem c f}). (is_unit_clause c t)))
}) =
    if length f = 0 then false
    else let x = L.hd f in
        if is_unit_clause x t
        then true
        else exists_unit_clause (L.tl f) t

let rec get_unit_clause (f : formula{length f > 0}) ( t : truth_assignment {exists_unit_clause f t}) 
    : (res : clause{is_unit_clause res t /\ L.mem res f}) =
    if length f = 1 then L.hd f
    else let x = L.hd f in
        if is_unit_clause x t
        then x
        else get_unit_clause (L.tl f) t

let get_unassigned_literal_in_unit_clause (c : clause) ( t : truth_assignment{is_unit_clause c t}) 
    : (res : literal{
        L.mem res c 
        /\ (forall (l : literal{L.mem l c /\ l <> res}). (is_variable_in_assignment t (get_literal_variable l)))
        /\ (is_variable_in_assignment t (get_literal_variable res) = false)})
    = let lits = get_unassigned_literals_from_clause c t in
        assert(length lits = 1);
        L.hd lits

let assign_literal_true_in_truth 
    (t : truth_assignment) 
    ( l : literal{is_variable_in_assignment t (get_literal_variable l) = false})
    : (res : truth_assignment{
        (forall (v : variable_info{L.mem v t}). (L.mem v res))
        /\ length res = length t + 1
        /\ is_variable_in_assignment res (get_literal_variable l)
        /\ get_literal_value res l = true
        /\ (forall (v : variable_info {L.mem v res}). (L.mem v t \/ v.variable = (get_literal_variable l)))
        /\ (forall (v : literal {
            is_variable_in_assignment res (get_literal_variable v)
            }). 
            (is_variable_in_assignment t (get_literal_variable v) \/ v = l \/ v = (negate_lit l)))
        
         /\ (forall (l : literal{ is_variable_in_assignment t (get_literal_variable l) }). 
                    (
                        is_variable_in_assignment res (get_literal_variable l)
                        /\ get_literal_value t l = get_literal_value res l))    
    }) = 
        let new_var = {value = Var? l; variable= (get_literal_variable l)} in
        let ress = add_var_to_truth t new_var in
        assert(ress = new_var :: t);
        assert(forall (v : variable_info{L.mem v t}). (L.mem v ress));
        assert((forall (v : variable_info {L.mem v ress}). 
            (L.mem v t \/ v.variable = (get_literal_variable l))));

        assert(forall (v : variable_info {L.mem v t}). 
                (is_variable_in_assignment t v.variable));
        
        assert(forall (v : literal {is_variable_in_assignment t (get_literal_variable v)}). 
                (L.mem {value = true ; variable = (get_literal_variable v)} t
                \/ L.mem {value = false ; variable = (get_literal_variable v)} t));

        assert(exists (v : variable_info{L.mem v ress}). 
                (L.mem v t = false /\ v.variable = (get_literal_variable l)));
        
        assert(is_variable_in_assignment ress (get_literal_variable l));
        assert(is_variable_in_assignment t (get_literal_variable l) = false);

        assert(exists (v : literal{
                is_variable_in_assignment ress (get_literal_variable v) }). 
                (is_variable_in_assignment t (get_literal_variable v) = false 
                /\ (get_literal_variable v) = (get_literal_variable l))
                /\ v = l
        );

        assert( (forall (v : literal {
            is_variable_in_assignment ress (get_literal_variable v)
            }). 
            (is_variable_in_assignment t (get_literal_variable v) 
            \/ (v = l)
            \/ (v = negate_lit l))
            ));
        ress

let lemma_dpll_helper_1 (t : truth_assignment) ( c : clause) : Lemma
    (requires are_clause_vars_in_assignment t c /\ (~(exists (l : literal{L.mem l c}). (get_literal_value t l))))
    (ensures get_clause_value t c = false) = ()

let negate_var_info (v : variable_info) : (res :variable_info {res.value = not v.value /\ v.variable=res.variable})
    = {value = (not v.value) ; variable = v.variable}

// let propagate_unit_clause_lemma_helper 
//     (f : formula) 
//     ( cl : clause) 
//     (t: truth_assignment ) 
//     (res : (truth_assignment * literal))
//     : Lemma
//     (requires 
//         L.mem cl f
//         /\ is_unit_clause cl t /\ no_variables_outside_f_are_in_t f t
//         /\ (snd res) = (get_unassigned_literal_in_unit_clause cl t)
//         /\ (fst res) = assign_literal_true_in_truth t (snd res) 
//     )
//     (ensures 
//         is_unit_clause cl res._1 = false
//         /\ is_clause_true_yet res._1 cl
//         /\ (length res._1 = length t + 1)
//         /\ (forall (v : variable_info{L.mem v t}). (L.mem v res._1)) 
//         /\ no_variables_outside_f_are_in_t f res._1
//         /\ (( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) 
//                 <==> 
//                 ( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) )

//         /\ is_variable_in_assignment t (get_literal_variable res._2) = false
//         /\ is_variable_in_assignment res._1 (get_literal_variable res._2)
//         /\ is_lit_in_formula f res._2
//         /\ (forall (l : literal {
//                 is_variable_in_assignment res._1 (get_literal_variable l)
//                 /\ (l <> (negate_lit res._2))
//                 /\ (l <> res._2)}) . 
//                     (is_variable_in_assignment t (get_literal_variable l)))
        
//         /\ (forall (l : literal {
//                 is_variable_in_assignment t (get_literal_variable l)
//             }). (get_literal_value t l = get_literal_value res._1 l)))
//     = 
//     let x = snd res in
//     let x_variable = get_literal_variable x in
//     let ress = fst res in
//     let anti_res = assign_literal_true_in_truth t (negate_lit x) in
//         assert((length (get_unassigned_literals_from_clause cl t) = 1) /\ (L.hd (get_unassigned_literals_from_clause cl t)) = x);
//         assert(forall (n : nat_non_zero{ is_variable_in_assignment t n}). ( is_variable_in_assignment anti_res n));

//         assert(forall (l : literal{L.mem l cl /\ l <> x}). (is_variable_in_assignment anti_res (get_literal_variable l)));
//         assert(is_variable_in_assignment anti_res (get_literal_variable x));
//         assert(forall (l : literal{L.mem l cl}). ((is_variable_in_assignment anti_res (get_literal_variable l)) ));
//         assert(forall (l : literal{L.mem l cl}). ( (get_literal_value anti_res l = false)));

//         assert(((are_clause_vars_in_assignment anti_res cl)));
//         assert(forall (l : literal{L.mem l cl}). (get_literal_value anti_res l = false));
//         assert(~(exists (l : literal{L.mem l cl}). (get_literal_value anti_res l)));
//         assert((get_clause_value anti_res cl) <==> (exists (l : literal{L.mem l cl}). (get_literal_value anti_res l = true)));
//         assert((~(exists (l : literal{L.mem l cl}). (get_literal_value anti_res l))) ==> (get_clause_value anti_res cl = false) );
//         lemma_dpll_helper_1 anti_res cl;
//         assert( get_clause_value anti_res cl = false) ;
//         assert(is_clause_false_yet anti_res cl = true);
//         assert(is_partial_solution f anti_res = false);

//         let v1 = {value = Var? (get_unassigned_literal_in_unit_clause cl t) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) } in
//         let v2 = negate_var_info v1 in

//         assert(
//             forall (other_t : truth_assignment {
//                 (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
//                     (forall (l : literal{L.mem l cl}). (is_variable_in_assignment other_t (get_literal_variable l)))
//         );
//         assert(
//             forall (other_t : truth_assignment {
//                 (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
//                     (forall (l : literal{L.mem l cl}). (get_literal_value anti_res l = get_literal_value other_t l))
//         );
//         assert(
//             forall (other_t : truth_assignment {
//                 (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
//                     (get_clause_value anti_res cl = get_clause_value other_t cl)
//         );
//         assert( get_clause_value anti_res cl = false) ;
//         assert(
//             forall (other_t : truth_assignment {
//                 (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
//                     (false = get_clause_value other_t cl)
//         );
//         assert(
//             forall (other_t : truth_assignment {
//                 (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
//                 (is_partial_solution f other_t = false)
//         );

//         assert(forall (other_t : truth_assignment {
//             (forall (v : variable_info{L.mem v t}). (L.mem v other_t)) 
//             /\ L.mem v2 other_t}). (is_partial_solution f other_t = false));

//         assert(v2 = {value = Var? (negate_lit (get_unassigned_literal_in_unit_clause cl t)) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) });
//         assert(L.mem v2 anti_res);
//         assert(( forall (whole_t: truth_assignment{ 
//                 (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                 /\ are_variables_in_truth_assignment f whole_t 
//                 /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_variable_in_assignment whole_t x_variable)));

//         assert(( forall (whole_t: truth_assignment{ 
//                 (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                 /\ are_variables_in_truth_assignment f whole_t 
//                 /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                    (L.mem v1 whole_t || L.mem v2 whole_t)));

//         assert(( forall (whole_t: truth_assignment{ 
//                 (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                 /\ are_variables_in_truth_assignment f whole_t 
//                 /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                    (L.mem v1 whole_t = not (L.mem v2 whole_t))));

//         assert(( forall (whole_t: truth_assignment{ 
//                 (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                 /\ are_variables_in_truth_assignment f whole_t 
//                 /\ L.mem v2 whole_t
//                 /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                    (is_solution f whole_t = false)));

//         assert(( forall (whole_t: truth_assignment{ 
//                 (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                 /\ are_variables_in_truth_assignment f whole_t 
//                 /\ (exists (v : variable_info  {L.mem v ress}). (L.mem v whole_t = false))
//                 /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                    (is_solution f whole_t = false)));

        
//         assert(( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) 
//                 <==> 
//                 ( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v ress)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) 
//                 );

//         assert(L.mem v1 ress);

//         assert(ress = {value = (Var? x) ; variable = (get_literal_variable x)} :: t);
//         assert(is_variable_in_assignment ress (get_literal_variable x));
//         assert(is_variable_in_assignment t (get_literal_variable x) = false);

//         assert(forall (l : literal{ is_variable_in_assignment t (get_literal_variable l)}). 
//                 (is_variable_in_assignment ress (get_literal_variable l)));

//         assert(forall (l : literal{ is_variable_in_assignment ress (get_literal_variable l)
//             }). 
//                 (x = (negate_lit l) \/ l = x \/ is_variable_in_assignment t (get_literal_variable l)));

//         assert((forall (l : literal {
//                 is_variable_in_assignment ress (get_literal_variable l)
//                 /\ (l <> (negate_lit x))
//                 /\ (l <> x)}) . 
//                     (is_variable_in_assignment t (get_literal_variable l))));

//         assert(
//              is_unit_clause cl res._1 = false);
//         assert( is_clause_true_yet res._1 cl);
//         assert( (length res._1 = length t + 1));
//         assert( (forall (v : variable_info{L.mem v t}). (L.mem v res._1)) );
//         assert( no_variables_outside_f_are_in_t f res._1);
//         assert( (( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) 
//                 <==> 
//                 ( forall (whole_t: truth_assignment{ 
//                     (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
//                     /\ are_variables_in_truth_assignment f whole_t 
//                     /\ length whole_t =  length ( get_vars_in_formula f)}). 
//                     (is_solution f whole_t = false)) ));

//         assert( is_variable_in_assignment t (get_literal_variable res._2) = false);
//         assert( is_variable_in_assignment res._1 (get_literal_variable res._2));
//         assert( is_lit_in_formula f res._2);
//         assert( (forall (l : literal {
//                 is_variable_in_assignment res._1 (get_literal_variable l)
//                 /\ (l <> (negate_lit res._2))
//                 /\ (l <> res._2)}) . 
//                     (is_variable_in_assignment t (get_literal_variable l))));
        
//         assert( (forall (l : literal {
//                 is_variable_in_assignment t (get_literal_variable l)
//             }). (get_literal_value t l = get_literal_value res._1 l)));
//         ()



let propagate_unit_clause 
    (f : formula) 
    ( cl : clause{L.mem cl f}) 
    (t: truth_assignment {is_unit_clause cl t /\ no_variables_outside_f_are_in_t f t}) 
    : (res : (truth_assignment * literal){
        is_unit_clause cl res._1 = false
        /\ is_clause_true_yet res._1 cl
        /\ (length res._1 = length t + 1)
        /\ (forall (v : variable_info{L.mem v t}). (L.mem v res._1)) 
        /\ no_variables_outside_f_are_in_t f res._1
        /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )

        /\ is_variable_in_assignment t (get_literal_variable res._2) = false
        /\ is_variable_in_assignment res._1 (get_literal_variable res._2)
        /\ is_lit_in_formula f res._2
        /\ (forall (l : literal {
                is_variable_in_assignment res._1 (get_literal_variable l)
                /\ (l <> (negate_lit res._2))
                /\ (l <> res._2)}) . 
                    (is_variable_in_assignment t (get_literal_variable l)))
        
        /\ (forall (l : literal {
                is_variable_in_assignment t (get_literal_variable l)
            }). (get_literal_value t l = get_literal_value res._1 l))
    })
    =
    let x = get_unassigned_literal_in_unit_clause cl t in
        let x_variable = get_literal_variable x in
        let ress = assign_literal_true_in_truth t x in
        let anti_res = assign_literal_true_in_truth t (negate_lit x) in
        assert((length (get_unassigned_literals_from_clause cl t) = 1) /\ (L.hd (get_unassigned_literals_from_clause cl t)) = x);
        assert(forall (n : nat_non_zero{ is_variable_in_assignment t n}). ( is_variable_in_assignment anti_res n));

        assert(forall (l : literal{L.mem l cl /\ l <> x}). (is_variable_in_assignment anti_res (get_literal_variable l)));
        assert(is_variable_in_assignment anti_res (get_literal_variable x));
        assert(forall (l : literal{L.mem l cl}). ((is_variable_in_assignment anti_res (get_literal_variable l)) ));
        assert(forall (l : literal{L.mem l cl}). ( (get_literal_value anti_res l = false)));

        assert(((are_clause_vars_in_assignment anti_res cl)));
        assert(forall (l : literal{L.mem l cl}). (get_literal_value anti_res l = false));
        assert(~(exists (l : literal{L.mem l cl}). (get_literal_value anti_res l)));
        assert((get_clause_value anti_res cl) <==> (exists (l : literal{L.mem l cl}). (get_literal_value anti_res l = true)));
        assert((~(exists (l : literal{L.mem l cl}). (get_literal_value anti_res l))) ==> (get_clause_value anti_res cl = false) );
        lemma_dpll_helper_1 anti_res cl;
        assert( get_clause_value anti_res cl = false) ;
        assert(is_clause_false_yet anti_res cl = true);
        assert(is_partial_solution f anti_res = false);

        let v1 = {value = Var? (get_unassigned_literal_in_unit_clause cl t) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) } in
        let v2 = negate_var_info v1 in

        assert(
            forall (other_t : truth_assignment {
                (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
                    (forall (l : literal{L.mem l cl}). (is_variable_in_assignment other_t (get_literal_variable l)))
        );
        assert(
            forall (other_t : truth_assignment {
                (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
                    (forall (l : literal{L.mem l cl}). (get_literal_value anti_res l = get_literal_value other_t l))
        );
        assert(
            forall (other_t : truth_assignment {
                (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
                    (get_clause_value anti_res cl = get_clause_value other_t cl)
        );
        assert( get_clause_value anti_res cl = false) ;
        assert(
            forall (other_t : truth_assignment {
                (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
                    (false = get_clause_value other_t cl)
        );
        assert(
            forall (other_t : truth_assignment {
                (forall (v : variable_info{L.mem v anti_res}). (L.mem v other_t))}). 
                (is_partial_solution f other_t = false)
        );

        assert(forall (other_t : truth_assignment {
            (forall (v : variable_info{L.mem v t}). (L.mem v other_t)) 
            /\ L.mem v2 other_t}). (is_partial_solution f other_t = false));

        assert(v2 = {value = Var? (negate_lit (get_unassigned_literal_in_unit_clause cl t)) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) });
        assert(L.mem v2 anti_res);
        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_variable_in_assignment whole_t x_variable)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (L.mem v1 whole_t || L.mem v2 whole_t)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (L.mem v1 whole_t = not (L.mem v2 whole_t))));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ L.mem v2 whole_t
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (is_solution f whole_t = false)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ (exists (v : variable_info  {L.mem v ress}). (L.mem v whole_t = false))
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (is_solution f whole_t = false)));

        
        assert(( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v ress)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                );

        assert(L.mem v1 ress);

        assert(ress = {value = (Var? x) ; variable = (get_literal_variable x)} :: t);
        assert(is_variable_in_assignment ress (get_literal_variable x));
        assert(is_variable_in_assignment t (get_literal_variable x) = false);

        assert(forall (l : literal{ is_variable_in_assignment t (get_literal_variable l)}). 
                (is_variable_in_assignment ress (get_literal_variable l)));

        assert(forall (l : literal{ is_variable_in_assignment ress (get_literal_variable l)
            }). 
                (x = (negate_lit l) \/ l = x \/ is_variable_in_assignment t (get_literal_variable l)));

        assert((forall (l : literal {
                is_variable_in_assignment ress (get_literal_variable l)
                /\ (l <> (negate_lit x))
                /\ (l <> x)}) . 
                    (is_variable_in_assignment t (get_literal_variable l))));

        T.Mktuple2 ress x

let rec unit_clause_propagation_helper
    (f : formula {length f > 0})
    (original_t : truth_assignment {
        length original_t > 0
        /\ no_variables_outside_f_are_in_t f original_t 
        /\ length original_t <= length (get_vars_in_formula f)})
    (t : truth_assignment {
        no_variables_outside_f_are_in_t f t 
        /\ length t <= length (get_vars_in_formula f)
        /\ (forall (v : variable_info{L.mem v original_t}). (L.mem v t))
        /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v original_t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    })
    (new_lits : list literal{
        (forall (l : literal {L.mem l new_lits}). 
            (L.mem (get_literal_variable l) (get_vars_in_formula f)  
            /\ (L.mem (negate_lit l) new_lits = false)))
        /\ (forall (l : literal {L.mem l new_lits}). 
            (is_variable_in_assignment t (get_literal_variable l))
            /\ (is_variable_in_assignment (L.tl original_t) (get_literal_variable l) = false)
            )
        /\ (forall (l : literal {L.mem l new_lits}). (get_literal_value t l))
        /\ (forall (l : literal {
                is_variable_in_assignment t (get_literal_variable l)
                /\ (L.mem l (negate_lits_list new_lits) = false)
                /\ (L.mem l new_lits = false)
            }). 
                (is_variable_in_assignment original_t (get_literal_variable l)))
    })
    : Tot (res : (truth_assignment & (list literal))
    {
     no_variables_outside_f_are_in_t f res._1
    /\ (forall (v :variable_info{L.mem v t}). (L.mem v res._1)) 
    /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v original_t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    /\ length res._1 >= length t
    /\ (forall (l : literal {L.mem l res._2}). 
        (
            is_variable_in_assignment res._1 (get_literal_variable l)
            /\ (is_variable_in_assignment (L.tl original_t) (get_literal_variable l) = false)
        ))
    /\ (forall (l : literal {L.mem l res._2}). 
        (
            L.mem (get_literal_variable l) (get_vars_in_formula f)
        ))
    /\ (forall (l : literal {L.mem l res._2}). (get_literal_value res._1 l))
    /\ (forall (l : literal{L.mem l res._2}). ((L.mem (negate_lit l) res._2 = false)))
    /\ (forall (c : clause {
        L.mem c f /\ (exists (l : literal{L.mem l res._2}). (L.mem l c))
        }). 
        (is_clause_true_yet res._1 c)) 
    /\ (forall (l : literal {
        is_variable_in_assignment res._1 (get_literal_variable l) 
        /\ (L.mem l (negate_lits_list res._2) = false)
        /\ (L.mem l res._2 = false)}).
            (is_variable_in_assignment original_t (get_literal_variable l)))
        

    /\ (forall (l : literal {
        is_variable_in_assignment t (get_literal_variable l)
    }). (get_literal_value t l = get_literal_value res._1 l))

    /\ (forall (l : literal {L.mem l new_lits}). (L.mem l res._2))

    }) 
        (decreases (length (get_vars_in_formula f) - (length t)))
    =
    if exists_unit_clause f t
    then 
        let x = get_unit_clause f t in
        let new_t = propagate_unit_clause f x t in
        assert(no_variables_outside_f_are_in_t f new_t._1);
        lemma_no_vars_in_t_outside_f_length_compare (get_vars_in_formula f) new_t._1;
        assert(length new_t._1 <= length (get_vars_in_formula f));
        assert(length new_t._1 > length t);

        let new_lits_2 = add_lit_to_list new_lits (snd new_t) in

        assert(is_variable_in_assignment new_t._1 (get_literal_variable new_t._2));

        assert(
              (forall (l : literal {L.mem l new_lits_2}). 
                (L.mem (get_literal_variable l) (get_vars_in_formula f) 
                /\ (L.mem (negate_lit l) new_lits_2 = false))));

         assert((forall (l : literal {L.mem l new_lits}). 
            (is_variable_in_assignment new_t._1 (get_literal_variable l))
            /\ (is_variable_in_assignment (L.tl original_t) (get_literal_variable l) = false)
            ));

        assert(is_variable_in_assignment t (get_literal_variable new_t._2) = false);
        assert(forall (v : variable_info{L.mem v original_t}). (L.mem v t));
        assert(is_variable_in_assignment original_t (get_literal_variable new_t._2) = false);
        assert((forall (l : literal {L.mem l new_lits_2}). 
            (is_variable_in_assignment new_t._1 (get_literal_variable l))
            /\ (is_variable_in_assignment (L.tl original_t) (get_literal_variable l) = false)
            ));

        assert(get_literal_value new_t._1 new_t._2);
        assert((forall (l : literal {L.mem l new_lits}). (get_literal_value t l)));
        assert((forall (l : literal {L.mem l new_lits}). (get_literal_value new_t._1 l)));
        assert(new_lits_2 = new_t._2 :: new_lits);    
        assert((forall (l : literal {L.mem l new_lits_2}). (get_literal_value new_t._1 l)));
        
        assert((forall (l : literal {
                is_variable_in_assignment t (get_literal_variable l)
                /\ (L.mem l (negate_lits_list new_lits) = false)
                /\ (L.mem l new_lits = false)}) . 
                    (is_variable_in_assignment original_t (get_literal_variable l)))
            );

        assert(new_t._1 = ({value = (Var? new_t._2) ; variable = (get_literal_variable new_t._2)}  :: t));

        assert(is_variable_in_assignment t (get_literal_variable new_t._2) = false);
        assert(is_variable_in_assignment original_t (get_literal_variable new_t._2) = false);

        assert(is_variable_in_assignment t (get_literal_variable ( negate_lit new_t._2)) = false);
        assert(is_variable_in_assignment original_t (get_literal_variable (negate_lit new_t._2)) = false);

        assert(L.mem new_t._2 new_lits_2);
        assert(new_lits_2 = new_t._2 :: new_lits);

        assert(is_variable_in_assignment new_t._1 (get_literal_variable new_t._2));
        assert(forall(v : variable_info{L.mem v t}). (L.mem v new_t._1) );
        
        assert(forall (l : literal {L.mem l new_lits_2 /\ l <> new_t._2}). (L.mem l new_lits));

        assert(
            forall (l : literal{is_variable_in_assignment t (get_literal_variable l)}). 
                (l <> new_t._2 /\ l <> (negate_lit new_t._2)));

        assert(forall (l : literal{L.mem l new_lits_2}). (L.mem l new_lits \/ l = new_t._2 ));

        assert(forall (l : literal{L.mem l new_lits}). (L.mem l new_lits_2));
        let negated_new_lits = negate_lits_list new_lits in
        let negated_new_lits_2 = negate_lits_list new_lits_2 in
        
        assert(forall (l : literal{L.mem l new_lits}). 
                (L.mem (negate_lit l) negated_new_lits));

        assert(forall (l : literal{L.mem l new_lits}). 
                (L.mem (negate_lit l) negated_new_lits_2));

        assert(L.mem (negate_lit new_t._2) negated_new_lits_2);

        assert(forall (l : literal{L.mem l new_lits_2}). (L.mem (negate_lit l) negated_new_lits_2));

        assert(forall (l : literal{L.mem (negate_lit l) new_lits}). 
                (L.mem l negated_new_lits_2));

        assert(forall (l : literal{L.mem l negated_new_lits}). 
            (L.mem l negated_new_lits_2));

        assert(L.mem (negate_lit new_t._2) negated_new_lits_2);

        assert(length negated_new_lits + 1 = length negated_new_lits_2);

        lemma_negate_lits_list_helper new_lits_2 negated_new_lits_2;

        assert(negated_new_lits_2 = negate_lits_list new_lits_2);
        assert(negate_lits_list new_lits_2 = (negate_lit (L.hd new_lits_2)) :: (negate_lits_list (L.tl new_lits_2)) );
        assert(negated_new_lits_2 = (negate_lit (L.hd new_lits_2)) :: (negate_lits_list (L.tl new_lits_2)) );
        assert(L.hd new_lits_2 = new_t._2);
        assert(L.tl new_lits_2 = new_lits);
        assert(negated_new_lits_2 = ((negate_lit new_t._2) :: (negate_lits_list new_lits) ));
        assert(negated_new_lits_2 = ((negate_lit new_t._2) :: (negate_lits_list new_lits) ));
        assert(negated_new_lits_2 = ((negate_lit new_t._2) :: negated_new_lits ));

        assert(forall (l : literal{L.mem l negated_new_lits_2}). 
            (L.mem l negated_new_lits \/ l = (negate_lit new_t._2) ));


        assert(forall (l : literal{
               l <> new_t._2
                /\ (L.mem l new_lits = false)}) . 
            (
                L.mem l new_lits_2 = false
            ));

        assert(forall (l : literal{
                l <> (negate_lit new_t._2)
                /\ (L.mem l negated_new_lits = false)
                }) . 
            (
                L.mem l negated_new_lits_2 = false
            ));


        assert((forall (l : literal {
                is_variable_in_assignment t (get_literal_variable l)
                /\ (L.mem l negated_new_lits_2 = false)
                /\ (L.mem l new_lits_2 = false)}) . 
                    (is_variable_in_assignment original_t (get_literal_variable l)))
            );

        assert(L.mem ({value = (Var? new_t._2) ; variable = (get_literal_variable new_t._2)}) new_t._1);

        assert(forall (l : literal{ is_variable_in_assignment (L.tl original_t) (get_literal_variable l)}). 
            (is_variable_in_assignment new_t._1 (get_literal_variable l) 
            /\ (L.mem l new_lits_2 = false)));

        assert((forall (l : literal {
                is_variable_in_assignment new_t._1 (get_literal_variable l)
                /\ (l <> negate_lit (new_t._2))
                /\ (l <> new_t._2)}) . 
                    (is_variable_in_assignment t (get_literal_variable l)))
            );

        assert((forall (l : literal {
                is_variable_in_assignment new_t._1 (get_literal_variable l)
                /\ (L.mem l (negate_lits_list new_lits_2) = false)
                /\ (L.mem l new_lits_2 = false)}) . 
                    (is_variable_in_assignment original_t (get_literal_variable l)))
            );
        let updated_t = fst new_t in
        let ress = unit_clause_propagation_helper f original_t updated_t new_lits_2 in

        assert((forall (l : literal {L.mem l ress._2}). 
        (
            is_variable_in_assignment ress._1 (get_literal_variable l)
            /\ (is_variable_in_assignment (L.tl original_t) (get_literal_variable l) = false)
            //\ is_lit_in_formula f l
        )));

        assert((forall (l : literal{L.mem l ress._2}). 
                (get_literal_value ress._1 l )));
        assert(is_variable_in_assignment new_t._1 (get_literal_variable new_t._2));
        assert(get_literal_value new_t._1 new_t._2);

        assert(forall (v : variable_info {L.mem v new_t._1}). (L.mem v ress._1));

        assert((forall (l : literal{L.mem l ress._2}). 
                (get_literal_value ress._1 l )));

        assert((forall (l : literal{L.mem l ress._2}). 
                (L.mem (negate_lit l) ress._2 = false)));

        assert((forall (c : clause {
            L.mem c f /\ (exists (l : literal{L.mem l ress._2}). (L.mem l c))
            }). 
                (is_clause_true_yet ress._1 c))
        );

        assert((forall (l : literal {
                is_variable_in_assignment ress._1 (get_literal_variable l) 
                /\ (L.mem l (negate_lits_list ress._2) = false)
                /\ (L.mem l ress._2 = false)}).
                    (is_variable_in_assignment original_t (get_literal_variable l)))
        );

        assert((forall (l : literal {
                is_variable_in_assignment ress._1 (get_literal_variable l) 
                /\ (L.mem l (negate_lits_list ress._2) = false)   
                /\ (L.mem l ress._2 = false)}).
                    (is_variable_in_assignment t (get_literal_variable l))));
        
        ress
    
    else 
        let ress = Mktuple2 t new_lits in
            assert(  (forall (l : literal {L.mem l new_lits}). 
                (
                    L.mem (get_literal_variable l) (get_vars_in_formula f)
                )));
            assert(ress._2 = new_lits);
            assert(    (forall (l : literal {L.mem l ress._2}). 
                (
                    L.mem (get_literal_variable l) (get_vars_in_formula f)
                )));
        ress



let unit_clause_propagation
    (f : formula {length f > 0})
    (t : truth_assignment {
        length t > 0
        /\ no_variables_outside_f_are_in_t f t 
        /\ length t <= length (get_vars_in_formula f)})
    (new_l : literal {
        is_variable_in_assignment (L.tl t) (get_literal_variable new_l) = false
        /\ L.mem (get_literal_variable new_l) (get_vars_in_formula f)
        /\ is_variable_in_assignment t (get_literal_variable new_l)
        /\ get_literal_value t new_l
        })
    : Tot (res : (truth_assignment & (list literal))
    {
     no_variables_outside_f_are_in_t f res._1
    /\ (forall (v :variable_info{L.mem v t}). (L.mem v res._1)) 
    /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v t)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.mem v res._1)}). ((List.Tot.mem v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    /\ length res._1 >= length t
    /\ (forall (l : literal {L.mem l res._2}). 
        (
            is_variable_in_assignment res._1 (get_literal_variable l)
            /\ (is_variable_in_assignment (L.tl t) (get_literal_variable l) = false)
        ))
    /\ (forall (l : literal {L.mem l res._2}). (get_literal_value res._1 l))
    /\ (forall (l : literal{L.mem l res._2}). ((L.mem (negate_lit l) res._2 = false)))
    /\ (forall (c : clause {
        L.mem c f /\ (exists (l : literal{L.mem l res._2}). (L.mem l c))
        }). 
        (is_clause_true_yet res._1 c)) 
    /\ (forall (l : literal {
        is_variable_in_assignment res._1 (get_literal_variable l) 
        /\ (L.mem l res._2 = false)
        /\ (L.mem l (negate_lits_list res._2) = false)
        }).
            (is_variable_in_assignment t (get_literal_variable l)))
    /\ (forall (l : literal {L.mem l res._2}).
            (L.mem (get_literal_variable l) (get_vars_in_formula f)))

    /\ (forall (l : literal {
        is_variable_in_assignment t (get_literal_variable l)
    }). (get_literal_value t l = get_literal_value res._1 l))

    /\ (L.mem new_l res._2)
    }) 
        (decreases (length (get_vars_in_formula f) - (length t)))
    = 
    let new_lits = [new_l] in 
        assert( 
            (forall (l : literal {L.mem l new_lits}). 
                (L.mem (get_literal_variable l) (get_vars_in_formula f) 
                /\ (L.mem (negate_lit l) new_lits = false))));

        assert( (forall (l : literal {L.mem l new_lits}). (get_literal_value t l)));
        assert(L.mem new_l new_lits);
        
        let ress = unit_clause_propagation_helper f t t new_lits in
        assert(forall (l : literal {L.mem l new_lits}). (L.mem l ress._2));
        assert( (L.mem new_l ress._2)
                );

        ress