module ConflictFunctions

open DataTypes
open DataTypesFunctions
open OtherFunctions
open FStar.List.Tot
module L = FStar.List.Tot

let rec contains_var_with_bigger_level (t : truth_assignment) ( new_level : nat) : (res : bool{
    (res = true <==> (exists (v : variable_info{L.contains v t}). (v.level > new_level)))
    /\ (res = false <==> (forall (v : variable_info{L.contains v t}). (v.level <= new_level)))
}) =
    if length t = 0 then false
    else
        let x = L.hd t in
            if x.level > new_level
            then true
            else contains_var_with_bigger_level (L.tl t) new_level 

let rec backtrack_to (t : truth_assignment {
    length t > 0
    }) (new_level : nat{
        (exists (v : variable_info{v.level > new_level}). (L.contains v t))
    }) : (res : truth_assignment{
    (length res < length t)
    /\ (forall (v : variable_info{L.contains v t && v.level <= new_level}). (L.contains v res))
    /\ (forall (v : variable_info{L.contains v res }). (L.contains v t))
}) =
            let x = L.hd t in
            if contains_var_with_bigger_level (L.tl t) new_level
            then  
                let temp_res = backtrack_to (L.tl t) new_level in
                    if x.level > new_level
                    then temp_res
                    else let ress = add_var_to_truth temp_res x in
                        assert(ress = x :: temp_res);
                        assert(forall (v : variable_info{L.contains v temp_res}). (L.contains v (L.tl t)));
                        assert(forall (v : variable_info{L.contains v temp_res}). (L.contains v t));
                        assert((forall (v : variable_info{L.contains v ress }). (L.contains v t)));
                        ress
            else 
                (L.tl t)

let rec combine_clauses (cl1 : clause) (cl2 : clause) 
    : Tot (res : clause{ 
        //(forall (lit : literal{L.contains lit cl1 || L.contains lit cl2}). (L.contains lit res)) 
        (forall (lit : literal{L.contains lit cl1}). (L.contains lit res))
        /\ (forall (lit : literal{L.contains lit cl2}). (L.contains lit res))
        /\ (forall (lit : literal{L.contains lit res}). (L.contains lit cl1 || L.contains lit cl2))
        /\ length res = length cl1 + length cl2})
    (decreases (length cl2))
    = if length cl2 = 1 then ((L.hd cl2) :: cl1)
        else let x = L.hd cl2 in
                combine_clauses (x :: cl1) (L.tl cl2)

let rec exists_literal_in_truth_from_clause ( t : truth_assignment) (c  :clause) : (res : bool{
    (res <==> (exists (l : literal {L.contains l c}). (is_variable_in_assignment t ( get_literal_variable l ))))
})
    = let b = is_variable_in_assignment t (get_literal_variable (L.hd c)) in
        if length c = 1
        then b
        else if b 
                then true
                else exists_literal_in_truth_from_clause t (L.tl c)


let get_literal_level (t : truth_assignment) ( l : literal {is_variable_in_assignment t (get_literal_variable l)}) : (res : nat) 
    = let v = get_var_from_assignment t (get_literal_variable l) in
        v.level


let rec get_smallest_level_from_new_clause (t : truth_assignment) (c : clause{
    exists_literal_in_truth_from_clause t c
}) : (res : nat {forall (l : literal{L.contains l c /\ is_variable_in_assignment t (get_literal_variable l)}). (res <= get_literal_level t l)})
    = 
    if length c = 1 
    then get_literal_level t (L.hd c) 
    else
        if is_variable_in_assignment t (get_literal_variable (L.hd c))
        then
            let var = get_literal_level t (L.hd c)  in
                if exists_literal_in_truth_from_clause t (L.tl c)
                then
                    let temp_res = get_smallest_level_from_new_clause t (L.tl c) in
                        if var < temp_res
                        then var
                        else temp_res
                else var
        else get_smallest_level_from_new_clause t (L.tl c)


let get_level_from_resolution_res (r : (clause & nat)) : (res : nat)
    = let x , y = r in
    y

let resolution 
    (t : truth_assignment) 
    (guess_level : nat) 
    (second_clause : clause{length second_clause > 1
        /\ (forall (l :literal{L.contains l second_clause /\ is_variable_in_assignment t (get_literal_variable l)}). (get_literal_level t l <= guess_level))
      }) 
    (conflict_clause : clause{length conflict_clause > 1
        /\ (forall (l : literal{L.contains l conflict_clause}). (is_variable_in_assignment t (get_literal_variable l) /\ get_literal_level t l <= guess_level))}) 
    (pivot : literal{
        is_variable_in_assignment t (get_literal_variable pivot) 
        /\ L.contains pivot conflict_clause 
        /\ L.contains (negate_lit pivot) second_clause})
    : (res : (clause & nat) {get_level_from_resolution_res res < guess_level}) =
    let cl1_no_pivot = remove_literal_from_list conflict_clause pivot in
    assert(exists_literal_in_truth_from_clause t conflict_clause);
    assert(exists_literal_in_truth_from_clause t cl1_no_pivot);
    let cl2_no_pivot = remove_literal_from_list second_clause (negate_lit pivot) in
    let new_clause = combine_clauses cl1_no_pivot cl2_no_pivot in
    assert(forall (l : literal{L.contains l cl1_no_pivot}). (L.contains l new_clause));
    let new_level = get_smallest_level_from_new_clause t new_clause in
    new_clause , new_level

let rec negate_clause (c : clause) : (res : clause {(length c = length res)
    /\ (forall (l : literal{L.contains l c}). (L.contains (negate_lit l) res))
    }) =
    if length c = 1 then [(negate_lit (L.hd c))]
    else
        let x = L.hd c in
        (negate_lit x) :: (negate_clause (L.tl c))

// let rec intersect (#a:Type0) (l1 : list a) (l2 : list a) : (res : list a{
//     (length res <= length l1 + length l2)
//     /\ (forall (x : a{L.contains x res}). (L.contains x l1 && L.contains x l2))
//     /\ (forall (x : a{L.contains x l1 && L.contains x l2}). (L.contains x res))
// })
//     =   if length l1 = 0 then []
//         else
//             let temp_res = intersect (L.tl l1) l2 in
//                 if L.contains (L.hd l1) l2 
//                 then (L.hd l1) :: temp_res
//                 else temp_res

let rec intersect_literals (l1 : list literal) (l2 : list literal) : (res : list literal{
    (length res <= length l1 + length l2)
 //   /\ (forall (x : literal{L.contains x res}). (L.contains x l1 && L.contains x l2))
    /\ (forall (x : literal{L.contains x l1 && L.contains x l2}). (L.contains x res))
    /\ (length res = 0 <==> 
        ((forall (l : literal{L.contains l l1}). (L.contains l l2 = false)) 
        /\ (forall (l : literal{L.contains l l2}). (L.contains l l1 = false))))
    /\ (length res > 0 <==> (exists (l : literal{L.contains l l1}). (L.contains l l2)))
})
    =   if length l1 = 0 then []
        else
            let temp_res = intersect_literals (L.tl l1) l2 in
                if L.contains (L.hd l1) l2 
                then 
                    let ress = add_literal_to_list (L.hd l1) temp_res in
                    assert(ress = (L.hd l1) :: temp_res);
                    assert(L.contains (L.hd l1) l1);
                    assert(forall (x : literal{L.contains x temp_res}). (L.contains x ress));
                    assert(length ress <= length l1 + length l2);
                    //assert((forall (x : literal{L.contains x ress}). (L.contains x l1 && L.contains x l2)));
                    assert((forall (x : literal{L.contains x l1 && L.contains x l2}). (L.contains x ress)));
                    ress
                else temp_res


// let rec find_clause_for_resolution 
//     (f : formula {length f > 0}) 
//     (faulty_literals : list literal{
//         length faulty_literals > 0 /\
//         (forall (l : literal{L.contains l faulty_literals}). (
//             (exists (c : clause{L.contains c f}). (L.contains (negate_lit l) c))
//         ))
//         //  (exists (c : clause{L.contains c f}). 
//         //     (exists (l : literal{L.contains l c}). (L.contains (negate_lit l) faulty_literals)))
//     }) 
//     : (res : ( clause & literal)) =
//     let cl = L.hd f in
//     let common_faulty_literals = intersect_literals (negate_clause faulty_literals) cl in
//         if length common_faulty_literals = 0
//         then 
//             let xs = L.tl f in
//                 assert(forall(l : literal{L.contains l faulty_literals}). (L.contains (negate_lit l) cl = false));
//                 assert((forall (l : literal{L.contains l faulty_literals}). (
//                         (exists (c : clause{L.contains c xs}). (L.contains (negate_lit l) c))
//                         )));
//                 let x = L.hd faulty_literals in
//                 assert(exists(c : clause{L.contains c f}). (L.contains (negate_lit x) c));
//                 assert(L.contains (negate_lit x) cl = false);
//                 assert(exists(c : clause{L.contains c xs}). (L.contains (negate_lit x) c));
//                 assert(length xs > 0);
//                 find_clause_for_resolution xs faulty_literals
//         else cl , (L.hd common_faulty_literals)

let rec find_clause_for_resolution 
    (f : formula {length f > 0}) 
    (faulty_literal : literal{  exists_literal_in_formula f (negate_lit faulty_literal)
        /\ (forall (c : clause{L.contains c f /\ L.contains (negate_lit faulty_literal) c}). (length c > 1))}) 
    : (res : clause { L.contains res f /\ length res > 1 /\  L.contains (negate_lit faulty_literal) res}) =
    let cl = L.hd f in
        if L.contains (negate_lit faulty_literal) cl
        then cl
        else find_clause_for_resolution (L.tl f) faulty_literal

let rec find_faulty_literal_in_conflict
    (t : truth_assignment)
    (conf_level : nat)
    (conflict_clause : clause{
            (forall (l : literal{L.contains l conflict_clause}). (
                is_variable_in_assignment t (get_literal_variable l) 
                /\ (get_literal_value t l = false)))
            /\ (exists (l : literal {L.contains l conflict_clause 
                    /\ is_variable_in_assignment t (get_literal_variable l)
                    /\ get_literal_value t l = false}). 
                    ((get_var_from_assignment t (get_literal_variable l)).level = conf_level))
            })
    : (res : literal{
        L.contains res conflict_clause
        /\ is_variable_in_assignment t (get_literal_variable res)
        /\ get_literal_value t res = false
        /\ (get_var_from_assignment t (get_literal_variable res)).level = conf_level
    }) =
    if length conflict_clause = 1
    then
        let lit_x = L.hd conflict_clause in
        lit_x
    else
        let lit_x = L.hd conflict_clause in
        let var_x = get_var_from_assignment t (get_literal_variable lit_x) in
            if var_x.level = conf_level
            then 
                lit_x
            else find_faulty_literal_in_conflict t conf_level (L.tl conflict_clause)

//exists vars cu acel conf_level, toate din clause sunt in t
// let rec find_faulty_literals_in_conflict 
//     (t : truth_assignment) 
//     (conf_level : nat) 
//     (conflict_clause : clause{
//         (forall (l : literal{L.contains l conflict_clause}). 
//             (
//                 is_variable_in_assignment t (get_literal_variable l) 
//                 /\ (get_literal_value t l = false)
//             ))}) 
//     : (res : list literal {
//             (forall (l : literal{L.contains l res}). 
//                 L.contains l conflict_clause
//                 /\ (is_variable_in_assignment t (get_literal_variable l) 
//                 /\ (get_literal_value t l = false) 
//                 /\ (get_var_from_assignment t (get_literal_variable l)).level = conf_level))})
//     =
//     if length conflict_clause = 1 
//     then
//         let lit_x = L.hd conflict_clause in
//         let var_x = get_var_from_assignment t (get_literal_variable lit_x) in
//             if var_x.level = conf_level
//             then [lit_x]
//             else []
//     else
//         let lit_x = L.hd conflict_clause in
//         let var_x = get_var_from_assignment t (get_literal_variable lit_x) in
//         let xs = find_faulty_literals_in_conflict t conf_level (L.tl conflict_clause) in
//             if var_x.level = conf_level
//             then 
//                 let ress = add_literal_to_list lit_x xs in
//                 assert(ress = lit_x :: xs);
//                 assert(forall (l : literal{L.contains l xs}). (L.contains l (L.tl conflict_clause)));
//                 assert(forall (l : literal{L.contains l (L.tl conflict_clause)}). (L.contains l conflict_clause));
//                 ress
//             else xs

let rec exists_conflict (f : formula) (t : truth_assignment) 
    : Tot (res : bool{ 
        ((res = true) <==> (exists (c : clause {L.contains c f}). (is_clause_false_yet t c)))
        /\ ((res = false) <==> (forall (c : clause{L.contains c f}). (is_clause_false_yet t c = false)))
        }) 
    (decreases (L.length f)) = 
    if length f = 0
        then false
        else 
            if length t = 0
            then false
            else
                if is_clause_false_yet t (L.hd f) 
                then true
                else exists_conflict (L.tl f) t

let rec exists_literal_with_level_in_clause (t : truth_assignment) ( c : clause) (current_level : nat) 
    : (res : bool { (res = true) <==> ((exists (l: literal{L.contains l c}). 
                ( ((is_variable_in_assignment t (get_literal_variable l)) /\ (get_var_from_assignment t (get_literal_variable l)).level = current_level))))})
    =
        if is_variable_in_assignment t (get_literal_variable (L.hd c))
        then
            let var = (get_var_from_assignment t (get_literal_variable (L.hd c))) in
                if length c = 1
                then 
                    var.level = current_level
                else if var.level = current_level
                        then true
                        else 
                            if exists_literal_in_truth_from_clause t (L.tl c)
                            then exists_literal_with_level_in_clause t (L.tl c) current_level
                            else false                        
        else 
            if length c = 1 
            then false
            else exists_literal_with_level_in_clause t (L.tl c) current_level

let rec get_conflict_clause 
    (f : formula ) 
    (current_level : nat {current_level > 0})
    (t : truth_assignment {
        exists_conflict f t = true /\ 
        (exists (c : clause{L.contains c f}). (is_clause_false_yet t c = true) ) /\
        (forall (c : clause{L.contains c f /\ is_clause_false_yet t c = true}). (exists_literal_with_level_in_clause t c current_level))
       // /\ (forall (c : clause{L.contains c f /\ length c = 1}). (is_clause_false_yet t c = false))
        })
    : Tot (res : clause{
            L.contains res f 
        //    /\ length res > 1
            /\ is_clause_false_yet t res = true
            /\ (forall (l : literal{L.contains l res}). (is_variable_in_assignment t (get_literal_variable l))) 
            /\ exists_literal_with_level_in_clause t res current_level
            // (exists (l: literal{L.contains l res}). ((get_var_from_assignment t (get_literal_variable l)).level = current_level))
            }) 
    (decreases (L.length f)) = 
    if is_clause_false_yet t (L.hd f) 
    then (L.hd f)
    else let xs = L.tl f in
        assert( exists_conflict xs t = true );
        assert((exists (c : clause{L.contains c xs}). (is_clause_false_yet t c = true) ));
        assert(forall (c : clause {L.contains c xs}). (L.contains c f));
        // assert((forall (c : clause{L.contains c xs /\ is_clause_false_yet t c = true}). (
        //     (exists (l: literal{L.contains l c}). ((get_var_from_assignment t (get_literal_variable l)).level = current_level)))));
     //   assert( (forall (c : clause{L.contains c xs /\ length c = 1}). (is_clause_false_yet t c = false)));
        get_conflict_clause xs current_level t


let solve_conflict
    (current_level : nat {current_level > 0}) 
    (f : formula) 
    (t : truth_assignment {
    (forall (l : literal{L.contains l (get_literals_in_formula f)}). (get_literal_level t l <= current_level))

    /\ (exists (c : clause{L.contains c f}). (exists_literal_with_level_in_clause t c current_level))
    /\ (forall (c : clause{L.contains c f /\ exists_literal_with_level_in_clause t c current_level}). (length c > 1))
    
    /\ (forall (c : clause{L.contains c f /\ is_clause_false_yet t c = true}). (
            (exists (l: literal{L.contains l c}). ((get_var_from_assignment t (get_literal_variable l)).level = current_level))))
    /\ (forall (c : clause{L.contains c f /\ is_clause_false_yet t c = true}). ((length c > 1)))
    
    /\ exists_conflict f t
    /\ no_vars_in_t_outside_f f t
    
    /\ (forall (l : literal{L.contains l (get_literals_in_formula f)
            /\ is_variable_in_assignment t (get_literal_variable l) 
            /\ (get_literal_value t l = false)}). 
        (L.contains (negate_lit l) (get_literals_in_formula f)))
    
    /\ (forall (c : clause{L.contains c f /\ length c = 1}). 
        (is_variable_in_assignment t (get_literal_variable (L.hd c))
        /\ (get_var_from_assignment t (get_literal_variable (L.hd c))).level = 0 
        /\ is_clause_true_yet t c))
    }) 
    : (res : (formula & truth_assignment & nat))
    = let conflict_clause = get_conflict_clause f current_level t in
        let faulty_literal = find_faulty_literal_in_conflict t current_level conflict_clause in
        let clause_for_resolution = find_clause_for_resolution f faulty_literal in
        // assert(is_clause_true_yet t clause_for_resolution);
        // assert(L.contains clause_for_resolution f);
        // assert((forall (c : clause{L.contains c f /\ length c = 1}). (is_clause_false_yet t c = false)));
        // assert((forall (c : clause{L.contains c f /\ is_clause_false_yet t c = true}). (length c > 1)));
        let (new_clause, new_level) = resolution t clause_for_resolution conflict_clause current_level faulty_literal in
            new_clause :: f, (backtrack_to t new_level ), new_level
        // let faulty_literals = find_faulty_literals_in_conflict t current_level conflict_clause in
        // assert(forall (l : literal{L.contains l conflict_clause}). (get_literal_value t l = false));
        // assert(forall (l : literal{L.contains l faulty_literals}). (L.contains (negate_lit l) (get_literals_in_formula f)));
        // let (clause_for_resolution, pivot) = find_clause_for_resolution f faulty_literals in
        // let (new_clause, new_level) = resolution t clause_for_resolution conflict_clause current_level pivot in
        //     new_clause :: f, (backtrack_to t new_level ), new_level
