module DpllPropagation

open FStar.List
open DataTypes
module L = FStar.List.Tot
open OtherFunctions

////////////functions for propagation of unit clauses 

let is_unit_clause (c : clause) ( t : truth_assignment) : (res : bool {
    (res) <==> ((length (get_unassigned_literals_from_clause c t) = 1) /\ (is_clause_true_yet t c = false))
}) =
    let xs = get_unassigned_literals_from_clause c t in
    if length xs = 1 && (is_clause_true_yet t c = false)
    then true
    else false

let rec exists_unit_clause (f : formula) ( t : truth_assignment) : (res : bool{
    (res <==> (exists (c : clause{L.contains c f}). (is_unit_clause c t)))
}) =
    if length f = 0 then false
    else let x = L.hd f in
        if is_unit_clause x t
        then true
        else exists_unit_clause (L.tl f) t

let rec get_unit_clause (f : formula{length f > 0}) ( t : truth_assignment {exists_unit_clause f t}) 
    : (res : clause{is_unit_clause res t /\ L.contains res f}) =
    if length f = 1 then L.hd f
    else let x = L.hd f in
        if is_unit_clause x t
        then x
        else get_unit_clause (L.tl f) t

let get_unassigned_literal_in_unit_clause (c : clause) ( t : truth_assignment{is_unit_clause c t}) 
    : (res : literal{L.contains res c /\ (is_variable_in_assignment t (get_literal_variable res) = false)})
    = let lits = get_unassigned_literals_from_clause c t in
        assert(length lits = 1);
        L.hd lits

let assign_literal_true_in_truth (t : truth_assignment) ( l : literal{is_variable_in_assignment t (get_literal_variable l) = false})
    : (res : truth_assignment{
        (forall (v : variable_info{L.contains v t}). (L.contains v res))
        /\ length res = length t + 1
        /\ is_variable_in_assignment res (get_literal_variable l)
        /\ get_literal_value res l = true
    }) = 
        let new_var = {value = Var? l; variable= (get_literal_variable l)} in
        let ress = add_var_to_truth t new_var in
        assert(ress = new_var :: t);
        assert(forall (v : variable_info{L.contains v t}). (L.contains v ress));
        ress

let negate_lit (l : literal) : (res : literal {(Var? l = NotVar? res) /\ l <> res /\ (get_literal_variable l = get_literal_variable res)})
    = match l with
    | Var x -> NotVar x
    | NotVar x -> Var x

let lemma_dpll_helper_1 (t : truth_assignment) ( c : clause) : Lemma
    (requires are_clause_vars_in_assignment t c /\ (~(exists (l : literal{L.contains l c}). (get_literal_value t l))))
    (ensures get_clause_value t c = false) = ()

let negate_var_info (v : variable_info) : (res :variable_info {res.value = not v.value /\ v.variable=res.variable})
    = {value = (not v.value) ; variable = v.variable}

let propagate_unit_clause 
    (f : formula) 
    ( cl : clause{L.contains cl f}) 
    (t: truth_assignment {is_unit_clause cl t /\ no_vars_in_t_outside_f f t}) 
    : (res : truth_assignment{
        is_unit_clause cl res = false
        /\ (forall (l : literal{L.contains l cl}). (is_variable_in_assignment res (get_literal_variable l)))
        /\ is_clause_true_yet res cl
        /\ (length res = length t + 1)
        /\ (forall (v : variable_info{L.contains v t}). (L.contains v res)) 
        /\ no_vars_in_t_outside_f f res
        /\ (is_partial_solution f (assign_literal_true_in_truth t (negate_lit (get_unassigned_literal_in_unit_clause cl t))) = false)
        /\ (forall (other_t : truth_assignment {
            (forall (v : variable_info{L.contains v t}). (L.contains v other_t)) 
            /\ L.contains {value = Var? (negate_lit (get_unassigned_literal_in_unit_clause cl t)) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) } other_t
            }). (is_partial_solution f other_t = false))
        /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v res)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    })
    =
    let x = get_unassigned_literal_in_unit_clause cl t in
        let x_variable = get_literal_variable x in
        let ress = assign_literal_true_in_truth t x in
        let anti_res = assign_literal_true_in_truth t (negate_lit x) in
        assert(forall (l : literal{L.contains l cl}). ((is_variable_in_assignment anti_res (get_literal_variable l)) /\ (get_literal_value anti_res l = false)));
        assert(((are_clause_vars_in_assignment anti_res cl)));
        assert(forall (l : literal{L.contains l cl}). (get_literal_value anti_res l = false));
        assert(~(exists (l : literal{L.contains l cl}). (get_literal_value anti_res l)));
        assert((get_clause_value anti_res cl) <==> (exists (l : literal{L.contains l cl}). (get_literal_value anti_res l = true)));
        assert((~(exists (l : literal{L.contains l cl}). (get_literal_value anti_res l))) ==> (get_clause_value anti_res cl = false) );
        lemma_dpll_helper_1 anti_res cl;
        assert( get_clause_value anti_res cl = false) ;
        assert(is_clause_false_yet anti_res cl = true);
        assert(is_partial_solution f anti_res = false);

        let v1 = {value = Var? (get_unassigned_literal_in_unit_clause cl t) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) } in
        let v2 = negate_var_info v1 in

        assert(forall (other_t : truth_assignment {
            (forall (v : variable_info{L.contains v anti_res}). (L.contains v other_t))}). (is_partial_solution f other_t = false));

        assert(forall (other_t : truth_assignment {
            (forall (v : variable_info{L.contains v t}). (L.contains v other_t)) 
            /\ L.contains v2 other_t}). (is_partial_solution f other_t = false));

        assert(v2 = {value = Var? (negate_lit (get_unassigned_literal_in_unit_clause cl t)) ; variable = (get_literal_variable (get_unassigned_literal_in_unit_clause cl t)) });
        assert(L.contains v2 anti_res);
        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_variable_in_assignment whole_t x_variable)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (L.contains v1 whole_t || L.contains v2 whole_t)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (L.contains v1 whole_t = not (L.contains v2 whole_t))));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ L.contains v2 whole_t
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (is_solution f whole_t = false)));

        assert(( forall (whole_t: truth_assignment{ 
                (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                /\ are_variables_in_truth_assignment f whole_t 
                /\ (exists (v : variable_info  {L.contains v ress}). (L.contains v whole_t = false))
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
                   (is_solution f whole_t = false)));

        
        assert(( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v ress)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                );

        assert(L.contains v1 ress);
        ress

let rec unit_clause_propagation
    (f : formula {length f > 0})
    (t : truth_assignment {no_vars_in_t_outside_f f t /\ length t <= length (get_vars_in_formula f)})
    : Tot (res : truth_assignment 
    {length res >= length t 
    /\ no_vars_in_t_outside_f f res
    /\ (forall (v :variable_info{L.contains v t}). (L.contains v res)) 
    /\ (( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v t)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) 
                <==> 
                ( forall (whole_t: truth_assignment{ 
                    (forall (v : variable_info {(List.Tot.contains v res)}). ((List.Tot.contains v whole_t)))
                    /\ are_variables_in_truth_assignment f whole_t 
                    /\ length whole_t =  length ( get_vars_in_formula f)}). 
                    (is_solution f whole_t = false)) )
    }) 
        (decreases (length (get_vars_in_formula f) - (length t)))
    =
    if exists_unit_clause f t
    then 
        let x = get_unit_clause f t in
        let new_t = propagate_unit_clause f x t in
        assert(no_vars_in_t_outside_f f new_t);
        lemma_test_9 (get_vars_in_formula f) new_t;
        assert(length new_t <= length (get_vars_in_formula f));
        assert(length new_t > length t);
        unit_clause_propagation f new_t
    else t
