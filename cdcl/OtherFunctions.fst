module OtherFunctions

open DataTypes
open DataTypesFunctions
open FStar.List.Tot
module L = FStar.List.Tot


let rec are_clause_vars_in_assignment (t : truth_assignment) (c : clause)
     : (res : bool {res = true <==> (forall (l : literal{List.Tot.contains l c}). (is_variable_in_assignment t (get_literal_variable l) ))}) = 
    let x = List.Tot.hd c in
        let xs = List.Tot.tl c in
            if length xs = 0
                then is_variable_in_assignment t (get_literal_variable x)
                else is_variable_in_assignment t (get_literal_variable x) && are_clause_vars_in_assignment t xs

let lemma_test_20 (t : truth_assignment) ( c : clause) : Lemma
    (requires are_clause_vars_in_assignment t c)
    (ensures (forall (c2 : clause{forall (l : literal{L.contains l c2}). (L.contains l c)}). (are_clause_vars_in_assignment t c2)))
    =()

let rec add_uniq_vars_from_clause_to_list 
    (vars: list nat_non_zero {List.Tot.noRepeats vars /\ length vars > 0}) (c : clause) 
    : Tot (res: list nat_non_zero {List.Tot.noRepeats res /\ length res > 0
    /\ (forall (var : literal{ List.Tot.contains var c}). (List.Tot.contains (get_literal_variable var) res))
    /\ (forall (var : nat_non_zero {List.Tot.contains var vars}). (List.Tot.contains var res))
    /\ length res <= length vars + length c
    /\ length res >= length vars
    }) 
        (decreases (length c)) =
        let x = List.Tot.hd c in
        let xs = List.Tot.tl c in
        if length xs = 0
            then if List.Tot.contains (get_literal_variable x) vars 
                    then vars
                    else let new_list =  List.Tot.append [(get_literal_variable x)] vars in
                        new_list
            else
                let x_var = get_literal_variable x in
                    if List.Tot.contains x_var vars 
                        then let final_list = add_uniq_vars_from_clause_to_list vars xs in
                            assert(List.Tot.contains (get_literal_variable x) vars);
                            final_list
                        else add_uniq_vars_from_clause_to_list (x_var :: vars) xs

// let rec get_vars_in_clause (c : clause) 
//     : Tot (vars : list nat_non_zero { length vars > 0 /\ (forall (var : literal{ List.Tot.contains var c}). (List.Tot.contains (get_literal_variable var) vars))}) =   
//         if length c = 1
//             then [(get_literal_variable (List.Tot.hd c))]
//             else (get_literal_variable (List.Tot.hd c)) :: (get_vars_in_clause (List.Tot.tl c))

let rec get_total_formula_var_count (f : formula) : (res : nat) =
    if length f = 0 then 0 else
    let x = List.Tot.hd f in
        let xs = List.Tot.tl f in
            if length xs = 0
                then length x
                else length x + (get_total_formula_var_count xs)


let rec get_vars_in_formula (f : formula ) 
    : Tot (vars: list nat_non_zero { 
        length f > 0 ==> length vars > 0 /\
        List.Tot.noRepeats vars 
        /\ (forall (cl : clause{List.Tot.contains cl f}). (forall (var : literal{List.Tot.contains var cl}). (List.Tot.contains (get_literal_variable var) vars)))
        /\ (length vars <= get_total_formula_var_count f)
        }) =
        if length f = 0
        then []
        else
        if length f = 1
            then
                let some_var = get_literal_variable ( List.Tot.hd (List.Tot.hd f)) in
                add_uniq_vars_from_clause_to_list [some_var] (List.Tot.hd f)
            else
                let tl_vars = get_vars_in_formula (List.Tot.tl f) in
                    let result = add_uniq_vars_from_clause_to_list tl_vars (List.Tot.hd f) in
                    assert(get_total_formula_var_count f = 
                       get_total_formula_var_count (List.Tot.tl f) + length (List.Tot.hd f));
                    assert(length result <= length tl_vars + length (List.Tot.hd f));
                    assert(length result >= length tl_vars);
                    result


let rec get_max' (max_x : nat_non_zero) (x_list : list nat_non_zero) 
    : Tot (res : nat_non_zero { 
        (res = max_x \/ List.Tot.contains res x_list) 
        /\ max_x > res = false 
        /\ (forall (some_x: nat_non_zero{List.Tot.contains some_x x_list }). (some_x > res = false) )}) 
    (decreases (length x_list)) =
    match x_list with
    | [] -> max_x
    | x :: xs -> if x > max_x then get_max' x xs else get_max' max_x xs

let get_max (x_list : list nat_non_zero {length x_list > 0}) : Tot (res : nat_non_zero { List.Tot.contains res x_list}) =
    get_max' (List.Tot.hd x_list) (List.Tot.tl x_list)

let get_max_var_in_formula (f: formula {length f > 0}) : (res: nat_non_zero {List.Tot.contains res (get_vars_in_formula f)})
    = let vars = (get_vars_in_formula f) in
        let max_var = get_max vars in
            max_var

let rec get_vars_from_assingment (l : list variable_info) = 
    if length l = 0
        then []
        else
    let x = List.Tot.hd l in
    let xs = List.Tot.tl l in
        (x.variable) :: get_vars_from_assingment xs

let rec add_vars_to_list (l : list nat_non_zero { List.Tot.noRepeats l }) ( l2 : list nat_non_zero {List.Tot.noRepeats l2 /\
    (forall (var : nat_non_zero { List.Tot.contains var l2}). (List.Tot.contains var l = false))}) : 
    Tot (res : list nat_non_zero {List.Tot.noRepeats res}) (decreases (length l2)) =
    if length l2 = 0 
        then l
        else
            let x = List.Tot.hd l2 in
            let xs = List.Tot.tl l2 in
                assert(List.Tot.contains x l = false);
                assert(List.Tot.contains x xs = false);
                assert((forall (var : nat_non_zero { List.Tot.contains var xs}). (List.Tot.contains var l = false)));
                add_vars_to_list (x :: l) xs

let rec add_vars_to_list2 (l : list nat_non_zero {List.Tot.noRepeats l}) (l2 : truth_assignment{
    (forall (v : variable_info{List.Tot.contains v l2}). (List.Tot.contains v.variable l = false))})
    : Tot (res : list nat_non_zero {List.Tot.noRepeats res}) (decreases (length l2)) =
    if length l2 = 0
        then l
        else let x = List.Tot.hd l2 in
            let xs = List.Tot.tl l2 in
                assert(List.Tot.contains x.variable l = false);
                assert(List.Tot.contains x xs = false);
                assert((forall (var : nat_non_zero { is_variable_in_assignment xs var}). (List.Tot.contains var l = false)));
                add_vars_to_list2 (x.variable :: l) xs

let vars_in_truth_result' (vars: list nat_non_zero { List.Tot.noRepeats vars }) (t: truth_assignment
    ) 
        : Tot (res : Type0) (decreases length vars) =
            ( 
            (forall (var : nat_non_zero {List.Tot.contains var vars}). (is_variable_in_assignment t var))
            )

let no_vars_in_t_outside_f' (vars : list nat_non_zero { List.Tot.noRepeats vars}) ( t : truth_assignment)
    : Tot (res : Type0) = (
        (forall (var : nat_non_zero {is_variable_in_assignment t var}). (List.Tot.contains var vars))
    )

let add_var_to_list (vars: list nat_non_zero {List.Tot.noRepeats vars}) (n : nat_non_zero{List.Tot.contains n vars = false}) :
    Tot (res : list nat_non_zero 
    {List.Tot.noRepeats res /\ List.Tot.contains n res /\ length res = length vars + 1
    /\ (forall (n2 : nat_non_zero{List.Tot.contains n2 vars}). (List.Tot.contains n2 res))})
    = n :: vars

let rec remove_var_from_list (vars : list nat_non_zero{List.Tot.noRepeats vars}) (n : nat_non_zero{List.Tot.contains n vars}) :
    Tot (res : list nat_non_zero {List.Tot.noRepeats res /\ (List.Tot.contains n res = false) /\ length vars = length res + 1
        /\ (forall (n2 : nat_non_zero { List.Tot.contains n2 vars /\ n2 <> n}). (List.Tot.contains n2 res))
        /\ (forall (n2 : nat_non_zero{List.Tot.contains n2 res}). (List.Tot.contains n2 vars))})
    = let x = List.Tot.hd vars in
        if x = n 
            then List.Tot.tl vars
            else let new_l = remove_var_from_list (List.Tot.tl vars) n in 
                    assert(List.Tot.contains (List.Tot.hd vars) (List.Tot.tl vars)=false);
                    let result = x :: new_l in
                    assert(forall (some : nat_non_zero{List.Tot.contains some new_l}). (List.Tot.contains some result));
                    assert(List.Tot.contains x result);
                    assert(List.Tot.noRepeats result);
                    assert(List.Tot.contains n result = false);
                    assert(forall (some : nat_non_zero{List.Tot.contains some new_l}). (List.Tot.contains some (List.Tot.tl vars)));
                    assert(forall (some : nat_non_zero{List.Tot.contains some (List.Tot.tl vars)}). (List.Tot.contains some vars));
                    assert(forall (some : nat_non_zero{List.Tot.contains some result}). (List.Tot.contains some vars));
                    result


let lemma_test_6 (t : truth_assignment) ( vars : list nat_non_zero) ( v : nat_non_zero) : Lemma
    (requires (List.Tot.noRepeats vars /\ List.Tot.contains v vars /\ is_variable_in_assignment t v))
    (ensures (vars_in_truth_result' vars t) ==> (forall (var : nat_non_zero { List.Tot.contains var (remove_var_from_list vars v)}). 
        (is_variable_in_assignment t var)))
    = ()


let lemma_test_5 (t : truth_assignment) (vars : list nat_non_zero) (v : nat_non_zero) : Lemma
    (requires (List.Tot.noRepeats vars /\ List.Tot.contains v vars /\ is_variable_in_assignment t v))
    (ensures (vars_in_truth_result' vars t) ==> (forall (var : nat_non_zero{List.Tot.contains var (remove_var_from_list vars v)}). 
        (is_variable_in_assignment (remove_variable_from_assignment t v) var)))
    =
    lemma_test_6 t vars v;
    assert(length (remove_variable_from_assignment t v) = length t - 1);
    assert(forall (var : variable_info{List.Tot.contains var (remove_variable_from_assignment t v)}). 
        (List.Tot.contains var t /\ is_variable_in_assignment t var.variable  )); 
    ()

let lemma_test_4 (t : truth_assignment) (vars : list nat_non_zero) (v : nat_non_zero) : Lemma
    (requires List.Tot.noRepeats vars /\ List.Tot.contains v vars /\ is_variable_in_assignment t v)
    (ensures (vars_in_truth_result' vars t) ==> (vars_in_truth_result' (remove_var_from_list vars v) (remove_variable_from_assignment t v)))
    = let t2 = remove_variable_from_assignment t v in
        let vars2 = remove_var_from_list vars v in
        lemma_test_5 t vars v;
        ()

let rec lemma_test_9 (vars: list nat_non_zero) (t : truth_assignment) : Lemma
    (requires List.Tot.noRepeats vars /\ (no_vars_in_t_outside_f' vars t))
    (ensures length t <= length vars ) (decreases (length t)) = 
        if length t = 0
            then let l = length vars in
                ()
            else let new_t = (remove_variable_from_assignment t (List.Tot.hd t).variable) in
                    let new_vars = (remove_var_from_list vars (List.Tot.hd t).variable) in
                        lemma_test_9 new_vars new_t

let rec lemma_test_10 (vars : list nat_non_zero) ( t : truth_assignment) : Lemma
    (requires List.Tot.noRepeats vars /\ (vars_in_truth_result' vars t))
    (ensures length t >= length vars) 
    = if length vars = 0
        then ()
        else let new_t = (remove_variable_from_assignment t (List.Tot.hd vars)) in 
            let new_vars = (remove_var_from_list vars (List.Tot.hd vars)) in
                lemma_test_4 t vars (List.Tot.hd vars);
                lemma_test_10 new_vars new_t

let rec lemma_test_11 ( vars : list nat_non_zero) ( t : truth_assignment) : Lemma
    (requires List.Tot.noRepeats vars /\ vars_in_truth_result' vars t
        /\ (no_vars_in_t_outside_f' vars t))
    (ensures length t = length vars)
    = lemma_test_9 vars t;
        lemma_test_10 vars t;
        ()

// let rec lemma_test_12 ( vars : list nat_non_zero) ( t : truth_assignment) : Lemma
//     (requires List.Tot.noRepeats vars
//         /\ (exists (n : nat_non_zero{List.Tot.contains n vars}). 
//             (is_variable_in_assignment t n = false
//                 /\ (no_vars_in_t_outside_f' (remove_var_from_list vars n ) t))) )
//     (ensures length vars > length t)
//     = if length t = 0 then ()
//         else 
//             if is_variable_in_assignment t (List.Tot.hd vars) = false 
//             then let vars2 = remove_var_from_list vars (List.Tot.hd vars) in
//                 assert(no_vars_in_t_outside_f' vars2 t);
//                 lemma_test_9 vars2 t;
//                 assert(length vars2 >= length t);
//                 assert(length vars > length t);  
//                 ()
//             else let new_t = (remove_variable_from_assignment t (List.Tot.hd vars)) in 
//                     let new_vars = (remove_var_from_list vars (List.Tot.hd vars)) in 
//                         // assert((exists (n : nat_non_zero{List.Tot.contains n new_vars}). 
//                         //         (is_variable_in_assignment t n = false
//                         //         /\ (no_vars_in_t_outside_f' (remove_var_from_list new_vars n ) t))));
//                         assert((exists (n : nat_non_zero{List.Tot.contains n vars}). 
//             (is_variable_in_assignment new_t n = false
//                 /\ (no_vars_in_t_outside_f' (remove_var_from_list vars n ) new_t))));
//                         assert(
//                             (exists (n : nat_non_zero{List.Tot.contains n new_vars}). 
//                                 (is_variable_in_assignment new_t n = false 
//                                 /\ (no_vars_in_t_outside_f' (remove_var_from_list new_vars n ) new_t))));
//                         lemma_test_12 new_vars new_t;
//                         ()

let lemma_test_2 (t : truth_assignment) ( vars : list nat_non_zero{length vars = 1}) : Lemma
   (requires List.Tot.noRepeats vars) 
   (ensures (is_variable_in_assignment t (List.Tot.hd vars)) <==> (vars_in_truth_result' vars t))
   = ()

let lemma_test_1 (t : truth_assignment) (vars : list nat_non_zero) (v : variable_info) 
    : Lemma 
        (requires 
        List.Tot.noRepeats vars
        /\ (is_variable_in_assignment t v.variable = false) 
        /\ (List.Tot.contains (v.variable) vars = false))
        (ensures 
           vars_in_truth_result' vars t ==> vars_in_truth_result' (add_var_to_list vars v.variable) (add_var_to_truth t v)
         )
     = let new_t = add_var_to_truth t v in
        let new_vars = add_var_to_list vars v.variable in
        assert(vars_in_truth_result' vars t ==> (forall (var : nat_non_zero {List.Tot.contains var vars}). (is_variable_in_assignment new_t var)));
        assert(vars_in_truth_result' vars t ==> (forall (var : nat_non_zero {List.Tot.contains var new_vars}). (is_variable_in_assignment new_t var)));
        ()

let lemma_test_0 (t : truth_assignment) ( vars :list nat_non_zero) (v : variable_info) : Lemma
    (requires 
        List.Tot.noRepeats vars 
        /\ (is_variable_in_assignment t v.variable = false) 
        /\ (List.Tot.contains (v.variable) vars = false))
    (ensures (vars_in_truth_result' vars t ) <==> (vars_in_truth_result' (add_var_to_list vars v.variable) (add_var_to_truth t v)))
    = 
    lemma_test_1 t vars v;
    lemma_test_4 (add_var_to_truth t v) (add_var_to_list vars v.variable) v.variable;
    ()

let vars_in_truth_result (f : formula ) (t : truth_assignment) = 
                           vars_in_truth_result' (get_vars_in_formula f) t

let no_vars_in_t_outside_f (f : formula) ( t : truth_assignment) = no_vars_in_t_outside_f' (get_vars_in_formula f) t
    
let rec are_variables_in_truth_assignment' (vars: list nat_non_zero { List.Tot.noRepeats vars && length vars > 0 }) (t: truth_assignment) 
    : Tot (res : bool 
    { (((vars_in_truth_result' vars t ) <==> res = true)
    ) }) (decreases length vars)
    = if length vars = 1
        then let result = is_variable_in_assignment t (List.Tot.hd vars) in
            lemma_test_2 t vars;
            result
        else let xs = List.Tot.tl vars in
                if is_variable_in_assignment t (List.Tot.hd vars) 
                    then 
                    let new_t = remove_variable_from_assignment t (List.Tot.hd vars) in
                        let result = are_variables_in_truth_assignment' xs new_t in
                        let v = get_var_from_assignment t (List.Tot.hd vars) in
                                lemma_test_1 new_t xs v;
                                lemma_test_0 new_t xs v;
                                result
                else false

let are_variables_in_truth_assignment (f : formula { length f > 0}) (t : truth_assignment)
    : Tot (res: bool {(res = true <==> ( vars_in_truth_result f t))
    }) (decreases (length f))
    = 
    let vars_in_formula = get_vars_in_formula f in
        let result = are_variables_in_truth_assignment' vars_in_formula t in
            result


let get_literal_value (t: truth_assignment) (l: literal {is_variable_in_assignment t (get_literal_variable l) = true}) : (res: bool) =
        let v = get_literal_variable l in
        match l with
        | Var _ ->  let var_info = get_var_from_assignment t v in
                        var_info.value 
        | NotVar _ ->  let var_info = get_var_from_assignment t v in
                            not var_info.value 

// let lemma_test_19 (t : truth_assignment) (n : nat_non_zero{is_variable_in_assignment t n}) : Lemma
//     (ensures (forall 
//                 (other_t : truth_assignment {forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}). 
//                 (((get_var_from_assignment t n).value = (get_var_from_assignment other_t n).value)))) = ()

// let lemma_test_18 (t : truth_assignment) (l : literal) : Lemma
//  (requires is_variable_in_assignment t (get_literal_variable l) = true)
//  (ensures (forall 
//                 (other_t : truth_assignment {forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}). 
//                 (get_literal_value t l = get_literal_value other_t l))) = ()

let rec get_values_from_clause  
        (t: truth_assignment)  
        (c:clause {are_clause_vars_in_assignment t c}) :
        (res : list bool{
            (exists (b : bool{L.contains b res}). (b)) <==> (exists (l : literal{L.contains l c}). (get_literal_value t l))
        }) =
        if length c = 1
            then [(get_literal_value t (List.Tot.hd c))]
            else 
                let x = List.Tot.hd c in
                    let xs = List.Tot.tl c in
                    (get_literal_value t x) :: get_values_from_clause t xs 

// let rec lemma_test_17 (t : truth_assignment) (c : clause) : Lemma
//     (requires are_clause_vars_in_assignment t c)
//     (ensures (forall (other_t : truth_assignment
//                         {forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}).
//                     //(List.Tot.contains true (get_values_from_clause t c) = List.Tot.contains true (get_values_from_clause other_t c))
//                     (get_values_from_clause t c = get_values_from_clause other_t c)
//                     ))
//     =   
//         lemma_test_20 t c;
//         if length c > 1
//         then
//             let xs = L.tl c in
//             assert(length xs > 0);
//             assert(are_clause_vars_in_assignment t xs);
//             lemma_test_17 t xs
//         else ()

let get_clause_value (t: truth_assignment) (c:clause {are_clause_vars_in_assignment t c}) : (res : bool{
    (res = false) <==> (forall (l : literal{L.contains l c}). (get_literal_value t l = false))
})
        = let ress = List.Tot.contains true (get_values_from_clause t c) in
        ress

// let lemma_test_15 (t : truth_assignment) (c : clause) : Lemma
//     (requires (are_clause_vars_in_assignment t c))
//     (ensures 
//          (forall (other_t : truth_assignment 
//             { forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}). 
//                 (get_clause_value other_t c = get_clause_value t c)) )
//     = lemma_test_17 t c;
//         ()

let is_clause_false_yet (t: truth_assignment) (c: clause) : (res: bool{
    res = true ==> 
    ((are_clause_vars_in_assignment t c)
        /\ (get_clause_value t c) = false) 
        /\ (forall (l : literal{L.contains l c}). (get_literal_value t l = false))
        ///\ (forall (other_t : truth_assignment { forall (v : variable_info{List.Tot.contains v t}). (List.Tot.contains v other_t)}). 
        //    (get_clause_value other_t c = false))
            }) 
    = if (are_clause_vars_in_assignment t c) = false
        then false
        else let ress = not (get_clause_value t c) in
            //lemma_test_15 t c;
            ress

///NEW FUNCTIONS FOR CDCL

let rec is_clause_true_yet (t : truth_assignment) ( c : clause) : (res : bool {
    res <==> (exists (l : literal{L.contains l c}). (is_variable_in_assignment t (get_literal_variable l) /\ get_literal_value t l))
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

let rec add_uniq_literals_from_clause_to_list 
    (vars: list literal {List.Tot.noRepeats vars /\ length vars > 0}) (c : clause) 
    : Tot (res: list literal {List.Tot.noRepeats res /\ length res > 0
    /\ (forall (var : literal{ List.Tot.contains var c}). (List.Tot.contains var res))
    /\ (forall (var : literal {List.Tot.contains var vars}). (List.Tot.contains var res))
    /\ (forall (var : literal{L.contains var res = false}). ((L.contains var vars = false) && (L.contains var c = false )))
    /\ (forall (l : literal{L.contains l res}). (L.contains l vars || L.contains l c))
    /\ length res <= length vars + length c
    /\ length res >= length vars
    }) 
        (decreases (length c)) =
        let x = List.Tot.hd c in
        let xs = List.Tot.tl c in
        if length xs = 0
            then if List.Tot.contains x vars 
                    then vars
                    else let new_list =  List.Tot.append [x] vars in
                        new_list
            else
                    if List.Tot.contains x vars 
                        then let final_list = add_uniq_literals_from_clause_to_list vars xs in
                            assert(List.Tot.contains x vars);
                            final_list
                        else add_uniq_literals_from_clause_to_list (x :: vars) xs

let rec exists_literal_in_formula (f : formula) (l : literal) :
    (res : bool{ 
        ((res = true) <==> (exists(c : clause{L.contains c f}). (L.contains l c)) )
        /\ ((res = false) <==> (forall (c : clause{L.contains c f}). (L.contains l c = false)))}) =
    if length f = 0 then false
    else
        if L.contains l (L.hd f)
        then true
        else exists_literal_in_formula (L.tl f) l

let rec get_literals_in_formula ( f : formula)
    : (lits : list literal { 
         (forall (l : literal{L.contains l lits}). (exists_literal_in_formula f l)) 
         /\ (length f > 0 ==> length lits > 0)
         /\ (L.noRepeats lits)
        /\ (forall (cl : clause{List.Tot.contains cl f}). 
                (forall (var : literal{List.Tot.contains var cl}). (List.Tot.contains var lits)))
        /\ (length lits <= get_total_formula_var_count f)
        // /\ (forall (l : literal {L.contains l lits}). 
        //          ((exists (c : clause{L.contains c f}). (L.contains l c))))
    }) = if length f = 0
        then []
        else
        if length f = 1
            then
                let some_var =  ( List.Tot.hd (List.Tot.hd f)) in
                let ress = add_uniq_literals_from_clause_to_list [some_var] (List.Tot.hd f) in
                assert((forall (l : literal{L.contains l ress}). (exists_literal_in_formula f l)) );
                //assert((~ (exists (l : literal{L.contains l ress}). (exists (c : clause {L.contains c f}). (L.contains l c)))));
                ress
            else
                let xs = L.tl f in
                let tl_lits = get_literals_in_formula xs in
                    assert((forall (l : literal{L.contains l tl_lits}). (exists_literal_in_formula xs l)) );
                    let ress = add_uniq_literals_from_clause_to_list tl_lits (List.Tot.hd f) in
                    assert(get_total_formula_var_count f = 
                       get_total_formula_var_count xs + length (List.Tot.hd f));
                    assert(length ress <= length tl_lits + length (List.Tot.hd f));
                    assert(length ress >= length tl_lits);
                    assert((forall (l : literal {L.contains l tl_lits}). (exists_literal_in_formula f l)));
                    assert((forall (l : literal {L.contains l (L.hd f)}). (exists_literal_in_formula f l)));
                    assert(forall (l : literal {L.contains l ress}). (L.contains l tl_lits || L.contains l (L.hd f)));
                    assert(forall (l : literal {L.contains l tl_lits || L.contains l (L.hd f)}). 
                        (exists_literal_in_formula f l));
                    assert((forall (l : literal {L.contains l ress}). ((exists_literal_in_formula f l))));
                    ress

let rec get_unassigned_literals_from_clause (c : clause) ( t : truth_assignment) : (res : list literal{
    (forall (lit : literal{L.contains lit res}). (is_variable_in_assignment t (get_literal_variable lit) = false))
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
        else x :: get_unassigned_literals_from_clause (L.tl c ) t

let negate_lit (l : literal) : (res : literal {res <> l /\ get_literal_variable res = get_literal_variable l})
    = if Var? l
        then NotVar (get_literal_variable l)
        else Var (get_literal_variable l)

let add_literal_to_list (lit : literal) ( lits : list literal) : (res : list literal{
    (forall (l : literal{L.contains l lits}). (L.contains l res)) 
    /\ (length res = length lits + 1)
    /\ (L.contains lit res)
    /\ (forall (l : literal{L.contains l res = false}). (L.contains l lits = false))
}) = let ress = lit :: lits in
    ress

let rec remove_literal_from_list (lits : list literal) (lit : literal{L.contains lit lits}) 
    : (res : list literal {
        (forall (l : literal{L.contains l lits /\ l <> lit}). (L.contains l res))
        /\ (length res = length lits - 1)
        /\ (forall (l : literal{L.contains l res}). (L.contains l lits))
    })
    = let x = L.hd lits in
        if x = lit 
        then L.tl lits
        else
            let temp_res = (remove_literal_from_list (L.tl lits) lit) in
            let ress = add_literal_to_list x temp_res in
            assert(forall (l : literal{L.contains l temp_res}). (L.contains l (L.tl lits)));
            assert(ress = (x :: temp_res));
            assert(forall (l : literal{L.contains l temp_res}). (L.contains l lits));
            ress

let assign_literal_true 
    (l : literal) 
    ( t : truth_assignment{ is_variable_in_assignment t (get_literal_variable l) = false}) 
    ( guess_level : nat) 
    : (res : truth_assignment{
        (is_variable_in_assignment res (get_literal_variable l))
        /\ (forall (v : variable_info{L.contains v t}). (L.contains v res))
        /\ (get_literal_value res l = true)
    })
    =
    let new_var_info = {value = (Var? l); variable= (get_literal_variable l) ; level=guess_level} in
    new_var_info :: t