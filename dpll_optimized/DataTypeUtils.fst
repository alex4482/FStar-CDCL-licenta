module DataTypeUtils

open FStar.List.Tot
module L = FStar.List.Tot

open DataTypes


let negate_lit (l : literal) 
    : (res : literal {
        (Var? l = NotVar? res) 
        /\ l <> res 
        /\ (get_literal_variable l = get_literal_variable res)})
    = match l with
    | Var x -> NotVar x
    | NotVar x -> Var x

let rec negate_lits_list (lits : list literal ) : Tot (res : list literal {
    (forall (l : literal{L.mem l lits}). ( L.mem (negate_lit l) res))
    /\ (forall (l : literal{L.mem l res}). ( L.mem (negate_lit l) lits))
    /\ length lits = length res
})
    = 
        if length lits = 0 then []
        else
        if length lits = 1
        then [negate_lit (L.hd lits)]
        else 
            let x = L.hd lits in
            let neg_x = negate_lit x in
            let temp_res = (negate_lits_list (L.tl lits)) in
            let ress = neg_x :: temp_res in
            assert(ress = (negate_lit x) :: (negate_lits_list (L.tl lits)));
            assert((forall (l : literal{L.mem l (L.tl lits)}). (L.mem (negate_lit l) temp_res)));
            assert(forall (l : literal{L.mem l temp_res}). (L.mem l ress));
            assert(L.mem (negate_lit x) ress);
            ress

let lemma_negate_lits_list_helper (lits : list literal {length lits > 0}) (negated_lits : list literal) : Lemma
    (requires negated_lits = negate_lits_list lits)
    (ensures negated_lits = (negate_lit (L.hd lits)) :: (negate_lits_list (L.tl lits)))
    = ()


let rec are_clause_vars_in_assignment (t : truth_assignment) (c : clause)
     : (res : bool {res = true <==> (forall (l : literal{L.mem l c}). (is_variable_in_assignment t (get_literal_variable l) ))}) = 
    let x = L.hd c in
        let xs = L.tl c in
            if length xs = 0
                then is_variable_in_assignment t (get_literal_variable x)
                else is_variable_in_assignment t (get_literal_variable x) && are_clause_vars_in_assignment t xs

let rec add_uniq_vars_from_clause_to_list 
    (vars: list nat_non_zero {L.noRepeats vars /\ length vars > 0}) (c : clause) 
    : Tot (res: list nat_non_zero {L.noRepeats res /\ length res > 0
    /\ (forall (var : literal{ L.mem var c}). (L.mem (get_literal_variable var) res))
    /\ (forall (var : nat_non_zero {L.mem var vars}). (L.mem var res))
    /\ length res <= length vars + length c
    /\ length res >= length vars
    }) 
        (decreases (length c)) =
        let x = L.hd c in
        let xs = L.tl c in
        if length xs = 0
            then if L.mem (get_literal_variable x) vars 
                    then vars
                    else let new_list =  L.append [(get_literal_variable x)] vars in
                        new_list
            else
                let x_var = get_literal_variable x in
                    if L.mem x_var vars 
                        then let final_list = add_uniq_vars_from_clause_to_list vars xs in
                            assert(L.mem (get_literal_variable x) vars);
                            final_list
                        else add_uniq_vars_from_clause_to_list (x_var :: vars) xs



let rec get_total_formula_var_count (f : formula) : (res : nat) =
    if length f = 0 then 0 else
    let x = L.hd f in
        let xs = L.tl f in
            if length xs = 0
                then length x
                else length x + (get_total_formula_var_count xs)


let rec get_vars_in_formula (f : formula ) 
    : Tot (vars: list nat_non_zero { 
        length f > 0 ==> length vars > 0 /\
        L.noRepeats vars 
        /\ (forall (cl : clause{L.mem cl f}). (forall (var : literal{L.mem var cl}). (L.mem (get_literal_variable var) vars)))
        /\ (length vars <= get_total_formula_var_count f)
        }) =
        if length f = 0
        then []
        else
        if length f = 1
            then
                let some_var = get_literal_variable ( L.hd (L.hd f)) in
                add_uniq_vars_from_clause_to_list [some_var] (L.hd f)
            else
                let tl_vars = get_vars_in_formula (L.tl f) in
                    let result = add_uniq_vars_from_clause_to_list tl_vars (L.hd f) in
                    assert(get_total_formula_var_count f = 
                       get_total_formula_var_count (L.tl f) + length (L.hd f));
                    assert(length result <= length tl_vars + length (L.hd f));
                    assert(length result >= length tl_vars);
                    result



let all_variables_are_in_truth_assignment' (vars: list nat_non_zero { L.noRepeats vars }) (t: truth_assignment) 
        : Tot (res : Type0) =
            ( 
            (forall (var : nat_non_zero {L.mem var vars}). (is_variable_in_assignment t var))
            )

let no_variables_outside_f_are_in_t' (vars : list nat_non_zero { L.noRepeats vars}) ( t : truth_assignment)
    : Tot (res : Type0) = (
        (forall (var : nat_non_zero {is_variable_in_assignment t var}). (L.mem var vars))
    )

let add_var_to_list (vars: list nat_non_zero {L.noRepeats vars}) (n : nat_non_zero{L.mem n vars = false}) :
    Tot (res : list nat_non_zero 
    {L.noRepeats res /\ L.mem n res /\ length res = length vars + 1
    /\ (forall (n2 : nat_non_zero{L.mem n2 vars}). (L.mem n2 res))
    /\ (forall (n2 : nat_non_zero {L.mem n2 res /\ n2 <> n}). (L.mem n2 vars))
    })
    = n :: vars

let rec remove_var_from_list (vars : list nat_non_zero{L.noRepeats vars}) (n : nat_non_zero{L.mem n vars}) :
    Tot (res : list nat_non_zero {L.noRepeats res /\ (L.mem n res = false) /\ length vars = length res + 1
        /\ (forall (n2 : nat_non_zero { L.mem n2 vars /\ n2 <> n}). (L.mem n2 res))
        /\ (forall (n2 : nat_non_zero{L.mem n2 res}). (L.mem n2 vars))})
    = let x = L.hd vars in
        if x = n 
            then L.tl vars
            else let new_l = remove_var_from_list (L.tl vars) n in 
                    assert(L.mem (L.hd vars) (L.tl vars)=false);
                    let result = x :: new_l in
                    assert(forall (some : nat_non_zero{L.mem some new_l}). (L.mem some result));
                    assert(L.mem x result);
                    assert(L.noRepeats result);
                    assert(L.mem n result = false);
                    assert(forall (some : nat_non_zero{L.mem some new_l}). (L.mem some (L.tl vars)));
                    assert(forall (some : nat_non_zero{L.mem some (L.tl vars)}). (L.mem some vars));
                    assert(forall (some : nat_non_zero{L.mem some result}). (L.mem some vars));
                    result
//
// for any t - truth_assignment
// and vars - list of variables
// if all variables are in truth_assignment (respect all_variables_are_in_truth_assignment' vars t)
// then by removing any given variable v: smaller_vars = (vars - v)
// the sublist smaller_vars still respects the property (all_variables_are_in_truth_assignment' smaller_vars t)
let lemma_vars_in_truth_without_var_helper_2 (t : truth_assignment) ( vars : list nat_non_zero) ( v : nat_non_zero) : Lemma
    (requires (
        L.noRepeats vars 
        /\ L.mem v vars 
        /\ is_variable_in_assignment t v)
    )
    (ensures 
        (all_variables_are_in_truth_assignment' vars t) 
            ==> (forall (var : nat_non_zero { 
                        L.mem var (remove_var_from_list vars v)}). 
                    (is_variable_in_assignment t var)
                )
    )
    = ()

//
// for any t - truth_assignment
// and vars - list of variables
// if all variables are in truth_assignment (respect all_variables_are_in_truth_assignment' vars t)
// then by removing any given variable v
// from the list of variables: smaller_vars = (vars - v)
// and from the truth_assignment: smaller_t = (t - v)
// the sublist smaller_vars and truth_assignment smaller_t still respects the property (all_variables_are_in_truth_assignment' smaller_vars smaller_t)
let lemma_vars_in_truth_without_var_helper_1
    (t : truth_assignment) 
    (vars : list nat_non_zero) 
    (v : nat_non_zero) 
    : Lemma
    (requires (
        L.noRepeats vars 
        /\ L.mem v vars 
        /\ is_variable_in_assignment t v))
    (ensures 
        (all_variables_are_in_truth_assignment' vars t) 
        ==> 
        (forall (var : nat_non_zero{
                    L.mem var (remove_var_from_list vars v)}
                ). 
                (is_variable_in_assignment (remove_variable_from_assignment t v) var)))
    =
    lemma_vars_in_truth_without_var_helper_2 t vars v;
    assert(length (remove_variable_from_assignment t v) = length t - 1);
    assert(forall (var : variable_info{L.mem var (remove_variable_from_assignment t v)}). 
        (L.mem var t /\ is_variable_in_assignment t var.variable  )); 
    ()
//
// same description as lemma_vars_in_truth_without_var_helper_1
let lemma_vars_in_truth_without_var 
    (t : truth_assignment) 
    (vars : list nat_non_zero) 
    (v : nat_non_zero) 
    : Lemma
    (requires 
        L.noRepeats vars 
        /\ L.mem v vars 
        /\ is_variable_in_assignment t v)
    (ensures 
        (all_variables_are_in_truth_assignment' vars t) 
        ==> 
        (all_variables_are_in_truth_assignment' (remove_var_from_list vars v) (remove_variable_from_assignment t v)))
    = let t2 = remove_variable_from_assignment t v in
        let vars2 = remove_var_from_list vars v in
        lemma_vars_in_truth_without_var_helper_1 t vars v;
        ()

//
// if all variables in truth_assignment 't' 
// can be found in the variables list 'vars'
// and there are no duplicate variables in 'vars'
// then the length of 'vars' is sure to be equal or bigger then the length of 't'
// length t <= length vars
// ('t' doesn't have duplicates by definition)
let rec lemma_no_vars_in_t_outside_f_length_compare
    (vars: list nat_non_zero) 
    (t : truth_assignment) 
    : Lemma
    (requires 
        L.noRepeats vars 
        /\ (no_variables_outside_f_are_in_t' vars t)
    )
    (ensures length t <= length vars ) 
    (decreases (length t)) = 
        if length t = 0
            then let l = length vars in
                    ()
            else let new_t = (remove_variable_from_assignment t (L.hd t).variable) in
                    let new_vars = (remove_var_from_list vars (L.hd t).variable) in
                        lemma_no_vars_in_t_outside_f_length_compare new_vars new_t
//
// if all variables in list 'vars' 
// can be found in the truth_assignment 't'
// and there are no duplicate variables in 'vars'
// then the length of 't' is sure to be equal or bigger then the length of 'vars'
// length t >= length vars
// ('t' doesn't have duplicates by definition)
let rec lemma_vars_in_truth_length_compare 
    (vars : list nat_non_zero) 
    ( t : truth_assignment) 
    : Lemma
    (requires 
        L.noRepeats vars 
        /\ (all_variables_are_in_truth_assignment' vars t)
    )
    (ensures length t >= length vars) 
    = if length vars = 0
        then ()
        else let new_t = (remove_variable_from_assignment t (L.hd vars)) in 
            let new_vars = (remove_var_from_list vars (L.hd vars)) in
                lemma_vars_in_truth_without_var t vars (L.hd vars);
                lemma_vars_in_truth_length_compare new_vars new_t

//
// for any truth_assignment 't'
// and list of variables 'vars' (with no duplicates)
// if (length t >= length vars) and (length t <= length vars) are true
// then (length t = length vars)
let rec lemma_truth_and_variable_list_length_equality 
    ( vars : list nat_non_zero) 
    ( t : truth_assignment) 
    : Lemma
    (requires 
        L.noRepeats vars 
        /\ all_variables_are_in_truth_assignment' vars t
        /\ (no_variables_outside_f_are_in_t' vars t)
    )
    (ensures length t = length vars)
    =   lemma_no_vars_in_t_outside_f_length_compare vars t;
        lemma_vars_in_truth_length_compare vars t;
        ()

//
// if for a truth_assignment 't'
// and list of variables 'vars' (with no duplicates)
// exists a variable 'v' in vars, such that by removing it from the list 'vars'
// the property (no_variables_outside_f_are_in_t' (smaller_vars) t) is true,
// then (length t <= length smaller_vars) and thus 
// (length t < length vars)
let rec lemma_length_truth_smaller_length_variable_list 
    ( vars : list nat_non_zero) 
    ( t : truth_assignment)
    : Lemma
    (requires 
        L.noRepeats vars
        /\ (exists (n : nat_non_zero{L.mem n vars}). 
            (   is_variable_in_assignment t n = false
                /\ (no_variables_outside_f_are_in_t' (remove_var_from_list vars n ) t)
            )) 
    )
    (ensures length t < length vars)
    = if length t = 0 then ()
        else 
            if is_variable_in_assignment t (L.hd vars) = false 
            then let vars2 = remove_var_from_list vars (L.hd vars) in
                assert(no_variables_outside_f_are_in_t' vars2 t);
                lemma_no_vars_in_t_outside_f_length_compare vars2 t;
                assert(length vars2 >= length t);
                assert(length vars > length t);  
                ()
            else let new_t = (remove_variable_from_assignment t (L.hd vars)) in 
                    let new_vars = (remove_var_from_list vars (L.hd vars)) in 
                        assert(is_variable_in_assignment t (L.hd vars));
                        assert(is_variable_in_assignment new_t (L.hd vars) = false);

                        assert(forall (n : nat_non_zero{L.mem n vars 
                                    /\ is_variable_in_assignment t n = false}). 
                                (L.mem n new_vars));

                        assert(forall (n : nat_non_zero{L.mem n new_vars}). (L.mem n vars));

                        assert(forall (n : variable_info{
                                L.mem n t /\ n.variable <> (L.hd vars)}). 
                                (L.mem n new_t));

                        assert(forall (n : nat_non_zero{
                                is_variable_in_assignment t n /\ n <> (L.hd vars)}). 
                                (is_variable_in_assignment new_t n));

                        assert(forall (n : nat_non_zero{
                            is_variable_in_assignment t n = false
                        }). (is_variable_in_assignment new_t n = false));

                        assert((exists (n : nat_non_zero{L.mem n vars}). 
                                (is_variable_in_assignment t n = false 
                                    /\ (no_variables_outside_f_are_in_t' (remove_var_from_list vars n ) t))));
                    

                        assert((exists (n : nat_non_zero{L.mem n new_vars}). 
                                (is_variable_in_assignment new_t n = false 
                                    /\ (no_variables_outside_f_are_in_t' (remove_var_from_list vars n ) t))));
                        
                        assert(
                            (forall (n1 : nat_non_zero{ L.mem n1 new_vars /\ is_variable_in_assignment new_t n1}). 
                                ( forall (n : nat_non_zero{
                                    L.mem n new_vars
                                    /\ is_variable_in_assignment new_t n = false
                                }). (L.mem n (remove_var_from_list new_vars n1 ))))
                           );

                        assert(forall (n : nat_non_zero{
                            is_variable_in_assignment t n = false
                            /\ L.mem n vars
                        }). (is_variable_in_assignment new_t n = false));

                        assert(forall (n : nat_non_zero{
                            is_variable_in_assignment t n = false
                            /\ L.mem n new_vars
                        }). (is_variable_in_assignment new_t n = false));

                        assert((exists (n : nat_non_zero{L.mem n new_vars}). 
                                (is_variable_in_assignment new_t n = false 
                                    /\ (no_variables_outside_f_are_in_t' (remove_var_from_list new_vars n ) new_t))));

                        lemma_length_truth_smaller_length_variable_list new_vars new_t  


//
// for any 't' truth_assignment
// and 'vars' a variable list with only one element 'v'
// 'v' appears in 't' iff all variables in 'vars' appear in 't'
// also meaning that 
// if 'v' appears in 't' 
// then the property 'all_variables_are_in_truth_assignment' vars t' will be true  
let lemma_vars_in_truth_when_length_list_is_1
    (t : truth_assignment) 
    ( vars : list nat_non_zero{length vars = 1}) 
    : Lemma
   (requires L.noRepeats vars) 
   (ensures 
        (is_variable_in_assignment t (L.hd vars)) 
        <==> 
        (all_variables_are_in_truth_assignment' vars t)
    )
   = ()

//
// if for any 't' truth_assignment and 'vars' list of variables (no duplicates)
// and variable 'v' which doesn't exist in 't' nor in 'vars'
// if all variables in 'vars' are in 't' 
// then after adding the 'v' to 'vars' and 't'
// then all variables in 'bigger_vars' are in 'bigger_t'
// bigger_vars = (vars + v) | bigger_t = (t + v)
let lemma_vars_in_truth_with_extra_variable_helper_1 
    (t : truth_assignment) 
    (vars : list nat_non_zero) 
    (v : variable_info) 
    : Lemma 
    (requires 
        L.noRepeats vars
        /\ (is_variable_in_assignment t v.variable = false) 
        /\ (L.mem (v.variable) vars = false)
    )
    (ensures 
        all_variables_are_in_truth_assignment' vars t 
        ==> 
        all_variables_are_in_truth_assignment' (add_var_to_list vars v.variable) (add_var_to_truth t v)
    )
     = let new_t = add_var_to_truth t v in
        let new_vars = add_var_to_list vars v.variable in
        assert(all_variables_are_in_truth_assignment' vars t ==> (forall (var : nat_non_zero {L.mem var vars}). (is_variable_in_assignment new_t var)));
        assert(all_variables_are_in_truth_assignment' vars t ==> (forall (var : nat_non_zero {L.mem var new_vars}). (is_variable_in_assignment new_t var)));
        ()

//
// if for any 't' truth_assignment and 'vars' list of variables (no duplicates)
// and variable 'v' which doesn't exist in 't' nor in 'vars'
// all variables in 'vars' appear in 't'
// if and only if
// all variables in (vars + v) appear in (t + v)
let lemma_vars_in_truth_with_extra_variable 
    (t : truth_assignment) 
    ( vars :list nat_non_zero) 
    (v : variable_info) 
    : Lemma
    (requires 
        L.noRepeats vars 
        /\ (is_variable_in_assignment t v.variable = false) 
        /\ (L.mem (v.variable) vars = false)
    )
    (ensures 
        (all_variables_are_in_truth_assignment' vars t ) 
        <==> 
        (all_variables_are_in_truth_assignment' (add_var_to_list vars v.variable) (add_var_to_truth t v))
    )
    = 
    lemma_vars_in_truth_with_extra_variable_helper_1 t vars v;
    lemma_vars_in_truth_without_var (add_var_to_truth t v) (add_var_to_list vars v.variable) v.variable;
    ()

let all_variables_are_in_truth_assignment (f : formula ) (t : truth_assignment) = 
    all_variables_are_in_truth_assignment' (get_vars_in_formula f) t

let no_variables_outside_f_are_in_t (f : formula) ( t : truth_assignment) =
    no_variables_outside_f_are_in_t' (get_vars_in_formula f) t
    
let rec are_variables_in_truth_assignment' 
    (vars: list nat_non_zero { 
        L.noRepeats vars 
        /\ length vars > 0 }
    ) 
    (t: truth_assignment) 
    : Tot 
    (res : bool { 
        ((all_variables_are_in_truth_assignment' vars t ) <==> res) }
    ) 
    (decreases length vars)
    = 
    if length vars = 1
    then 
        let result = is_variable_in_assignment t (L.hd vars) in
            lemma_vars_in_truth_when_length_list_is_1 t vars;
            result
    else let xs = L.tl vars in
            if is_variable_in_assignment t (L.hd vars) 
            then 
                let new_t = remove_variable_from_assignment t (L.hd vars) in
                let result = are_variables_in_truth_assignment' xs new_t in

                 [@@inline_let]
                let v = get_var_from_assignment t (L.hd vars) in
                    lemma_vars_in_truth_with_extra_variable_helper_1 new_t xs v;
                    lemma_vars_in_truth_with_extra_variable new_t xs v;
                    result
            else false

let are_variables_in_truth_assignment (f : formula { length f > 0}) (t : truth_assignment)
    : Tot (res: bool {(res = true <==> ( all_variables_are_in_truth_assignment f t))
    }) (decreases (length f))
    = 
    let vars_in_formula = get_vars_in_formula f in
        let result = are_variables_in_truth_assignment' vars_in_formula t in
            result


let rec get_values_from_clause  
        (t: truth_assignment)  
        (c:clause {are_clause_vars_in_assignment t c}) 
        : (res : list bool{
            (L.mem true res = false) <==> (forall (l : literal{L.mem l c}). (get_literal_value t l = false))
        }) =
        if length c = 1
            then [(get_literal_value t (L.hd c))]
            else 
                let x = L.hd c in
                    let xs = L.tl c in
                    (get_literal_value t x) :: get_values_from_clause t xs 

//
// for 't' truth_assignment
// and 'c' a clause
// where all variables in 'c' can be found in 't'
// then for every truth_assignment 'other_t'
// where 't' is a subset of 'other_t'
// then all literals in 'c' have the same value in 't' and 'other_t' 
// (even if their order may differ in 'other_t')
// so the value of 'c' is the same for 't' and 'other_t'
let rec lemma_values_from_clause_same_for_all_supra_set_of_t_helper_1
    (t : truth_assignment) 
    (c : clause) 
    : Lemma
    (requires are_clause_vars_in_assignment t c)
    (ensures 
        (forall (other_t : truth_assignment
                    {forall (v : variable_info{L.mem v t}). 
                            (L.mem v other_t)}).
                (L.mem true (get_values_from_clause t c) = L.mem true (get_values_from_clause other_t c)))
    )
    = 
        if length c = 1 
            then ()
            else lemma_values_from_clause_same_for_all_supra_set_of_t_helper_1 t (L.tl c)

let get_clause_value (t: truth_assignment) (c:clause {are_clause_vars_in_assignment t c}) 
    : (res : bool {res <==> (exists (l : literal{L.mem l c}). (get_literal_value t l = true))})
        = let ress = L.mem true (get_values_from_clause t c) in
        ress
//
// same description like 'lemma_values_from_clause_same_for_all_supra_set_of_t_helper_1'
let lemma_values_from_clause_same_for_all_supra_set_of_t 
    (t : truth_assignment) 
    (c : clause) 
    : Lemma
    (requires (are_clause_vars_in_assignment t c))
    (ensures 
         (forall (other_t : truth_assignment 
                    { forall (v : variable_info{L.mem v t}). (L.mem v other_t)}). 
                 (get_clause_value other_t c = get_clause_value t c)) 
    )
    = lemma_values_from_clause_same_for_all_supra_set_of_t_helper_1 t c;
        ()

let is_clause_false_yet (t: truth_assignment) (c: clause) : (res: bool{
    (res = true <==> 
    ((are_clause_vars_in_assignment t c)
        /\ (get_clause_value t c) = false) 
        /\ (forall (other_t : truth_assignment { forall (v : variable_info{L.mem v t}). (L.mem v other_t)}). 
            (get_clause_value other_t c = false)))
    /\ (res = false <==> (exists (l : literal {L.mem l c}). 
            ((is_variable_in_assignment t (get_literal_variable l) = false )
            \/ get_literal_value t l)))
            }) 
    = if (are_clause_vars_in_assignment t c) = false
        then false
        else let ress = not (get_clause_value t c) in
            lemma_values_from_clause_same_for_all_supra_set_of_t t c;
            ress

let partial_solution (f : formula) (t: truth_assignment) = 
    (forall (c : clause{L.mem c f}). (is_clause_false_yet t c = false))

let rec exists_false_clause_yet (f : formula) (t : truth_assignment) : (res : bool {
       ((res = false) <==> partial_solution f t)
        /\ ((res = true) <==> (exists (c : clause{L.mem c f}). (is_clause_false_yet t c)))
        }) =
    if length f = 0
        then false
        else 
            if length f = 1 
            then is_clause_false_yet t (L.hd f)
            else (is_clause_false_yet t (L.hd f)) || (exists_false_clause_yet (L.tl f) t)


let is_partial_solution (f:formula { length f > 0}) (t: truth_assignment) : (res : bool {
        (res <==> partial_solution f t)
        /\ ((res = false) <==> (exists (c : clause{L.mem c f}). (is_clause_false_yet t c)))
        })=
    if length t = 0 
        then true
        else not (exists_false_clause_yet f t)

let is_solution 
            (f: formula  { length f > 0 })
            (t: truth_assignment {
                ((length (get_vars_in_formula f)) = length t)
                /\ all_variables_are_in_truth_assignment f t  
                })
    = is_partial_solution f t 

let t1_is_sublist_of_t2 
    (t1 : truth_assignment)
    (t2 : truth_assignment)
    = 
    (forall (v : variable_info {(List.Tot.mem v t1)}). ((List.Tot.mem v t2)))

let t_cant_be_solution_for_f  
    (f : formula {length f > 0})
    (t : truth_assignment)
    = 
    ( forall (whole_t: truth_assignment{ 
                t1_is_sublist_of_t2 t whole_t
                /\ are_variables_in_truth_assignment f whole_t 
                /\ length whole_t =  length ( get_vars_in_formula f)}). 
             (is_solution f whole_t = false)) 

let get_truth_from_result (r: result{ Sat? r = true}) = match r with 
    | Sat t -> t

let rec get_next_element 
    (l : list nat_non_zero) 
    ( t : truth_assignment {exists (n : nat_non_zero{L.mem n l}). 
        (is_variable_in_assignment t n = false)}) : 
    (res : nat_non_zero{ is_variable_in_assignment t res = false /\ L.mem res l})
    = if not (is_variable_in_assignment t (L.hd l))
        then L.hd l
        else get_next_element (L.tl l) t


let rec is_clause_true_yet (t : truth_assignment) ( c : clause) : (res : bool {
    res <==> (exists (l : literal{L.mem l c}). (is_variable_in_assignment t (get_literal_variable l) /\ get_literal_value t l))
})
    = 
        if length c > 1
        then 
            let temp_res = is_clause_true_yet t (L.tl c) in
                if is_variable_in_assignment t (get_literal_variable (L.hd c))
                then if get_literal_value t (L.hd c) 
                        then true
                        else is_clause_true_yet t (L.tl c)
                else is_clause_true_yet t (L.tl c)
        else
            if is_variable_in_assignment t (get_literal_variable (L.hd c))
            then get_literal_value t (L.hd c)
            else false

let add_lit_to_list ( lits : list literal) ( l : literal) : (res : list literal{
    (forall (lit : literal{L.mem lit lits}). (L.mem lit res))
    /\ (forall (lit : literal {L.mem lit res /\ lit <> l}). (L.mem lit lits))
    /\ L.mem l res
    /\ length res = length lits + 1
}) = l :: lits

let rec get_unassigned_literals_from_clause (c : clause) ( t : truth_assignment) : (res : list literal{
    (forall (lit : literal{L.mem lit res}). ((is_variable_in_assignment t (get_literal_variable lit) = false)))
    /\ (forall (lit : literal{L.mem lit res}). (L.mem lit c))
    /\ (forall (lit : literal{L.mem lit res = false /\ L.mem lit c}). (is_variable_in_assignment t (get_literal_variable lit)))
    /\ (forall (lit : literal{L.mem lit res /\ L.mem lit c}). (is_variable_in_assignment t (get_literal_variable lit) = false))
})
    = 
    if length c = 1
    then
        if is_variable_in_assignment t (get_literal_variable (L.hd c))
        then [] 
        else [(L.hd c)]
    else
        let x = L.hd c in
        if is_variable_in_assignment t (get_literal_variable x)
        then get_unassigned_literals_from_clause (L.tl c) t
        else 
            let temp_res = get_unassigned_literals_from_clause (L.tl c ) t in
            assert( (forall (lit : literal{L.mem lit temp_res}). (L.mem lit (L.tl c))));
            assert( (forall (lit : literal{L.mem lit temp_res}). (L.mem lit c)));
            let ress = add_lit_to_list temp_res x in
            assert(ress = x :: temp_res );
            assert(L.mem x c);
            assert(is_variable_in_assignment t (get_literal_variable x) = false);
            assert(forall (lit : literal{L.mem lit temp_res}). ((is_variable_in_assignment t (get_literal_variable lit) = false)));
            assert((forall (lit : literal{L.mem lit ress}). ((is_variable_in_assignment t (get_literal_variable lit) = false))));
            assert( (forall (lit : literal{L.mem lit ress}). (L.mem lit c)));
            ress


let rec add_uniq_lits_from_clause_to_list 
    (vars: list literal {L.noRepeats vars /\ length vars > 0}) (c : clause) 
    : Tot (res: list literal {
        L.noRepeats res 
        /\ length res > 0
        /\ (forall (l : literal {L.mem l res}). (L.mem l c \/ L.mem l vars))
        /\ (forall (var : literal{ L.mem var c}). (L.mem var res))
        /\ (forall (var : literal {L.mem var vars}). (L.mem var res))
        /\ length res <= length vars + length c
        /\ length res >= length vars
    }) 
        (decreases (length c)) =
        let x = L.hd c in
        let xs = L.tl c in
        if length xs = 0
            then if L.mem x vars 
                    then vars
                    else let new_list =  L.append [ x] vars in
                        new_list
            else
                    if L.mem x vars 
                        then let final_list = add_uniq_lits_from_clause_to_list vars xs in
                            assert(L.mem x vars);
                            final_list
                        else add_uniq_lits_from_clause_to_list (x :: vars) xs

let rec is_lit_in_formula (f : formula) ( l : literal) 
    :(res : bool{
        (res <==> (exists (c : clause{L.mem c f}). (L.mem l c)))
        /\ (res = false <==> (forall (c : clause {L.mem c f}). (L.mem l c = false)))
    })
    = if length f = 0 then false
    else 
        let x = L.hd f in
        if L.mem l x
        then true
        else is_lit_in_formula (L.tl f) l

let rec get_lits_in_formula (f : formula ) 
    : Tot (vars: list literal { 
        (length f > 0 ==> length vars > 0) /\
        (L.noRepeats vars )
        /\ (forall (l : literal{L.mem l vars}). (is_lit_in_formula f l))
        /\ (forall (cl : clause{L.mem cl f}). 
            (forall (var : literal{L.mem var cl}). (L.mem var vars)))
        /\ (length vars <= get_total_formula_var_count f)
        /\ (forall (l : literal{ L.mem l vars = false}). (
            is_lit_in_formula f l = false
        ))
        }) =
        if length f = 0
        then []
        else
        if length f = 1
            then
                let some_var = ( L.hd (L.hd f)) in
                assert(L.mem some_var (L.hd f));
                assert(exists (c : clause{L.mem c f}). (L.mem some_var c));
                let ress = add_uniq_lits_from_clause_to_list [some_var] (L.hd f) in
                assert(forall (l : literal{L.mem l (L.hd f)}). (is_lit_in_formula f l));
                assert(forall (l : literal{L.mem l ress}). (L.mem l (L.hd f)));
                assert(forall (l : literal{ L.mem l ress}). (is_lit_in_formula f l));
                assert(L.noRepeats ress);
                assert(length ress > 0);
                assert((forall (cl : clause{L.mem cl f}). 
                    (forall (var : literal{L.mem var cl}). (L.mem var ress))));
                ress
            else
                let f_tl = L.tl f in
                let tl_vars = get_lits_in_formula f_tl in
                    assert(forall (c : clause{L.mem c f_tl}). (L.mem c f));
                    assert(forall (l : literal{L.mem l tl_vars}). (is_lit_in_formula f_tl l));
                    let result = add_uniq_lits_from_clause_to_list tl_vars (L.hd f) in
                    assert(get_total_formula_var_count f = 
                       get_total_formula_var_count f_tl + length (L.hd f));
                    assert(length result <= length tl_vars + length (L.hd f));
                    assert(length result >= length tl_vars);
                    assert(forall (l : literal{L.mem l tl_vars}). (is_lit_in_formula f l));
                    assert(forall (l : literal{L.mem l (L.hd f)}). (is_lit_in_formula f l));
                    assert(forall (l : literal{L.mem l result}). (is_lit_in_formula f l));
                    assert(L.noRepeats result);
                    assert(length result > 0);
                    assert((forall (cl : clause{L.mem cl f}). 
                        (forall (var : literal{L.mem var cl}). (L.mem var result))));
                    result
