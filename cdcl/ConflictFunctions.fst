module ConflictFunctions

open DataTypes
open DataTypesFunctions
module L = FStar.List.Tot

let rec backtrack_to (t : truth_assignment) (new_level : nat) : (res : truth_assignment{
    (length res < length t)
    /\ (forall (v : variable_info{L.contains v t && v.level <= new_level}). (L.contains v res))
    /\ (forall (v : variable_info{L.contains v res }). (L.contains v t))
})
    = if length t = 0 then []
        else
            let x = L.hd t in
            let temp_res = backtrack_to (L.tl t) new_level in
                if x.level > new_level
                then temp_res
                else x :: temp_res

let combine_clauses (cl1, cl2 : clause) 
    : (res : clause{ 
        (forall (lit : literal{L.contains lit cl1 || L.contains lit cl2}). (L.contains lit res)) 
        /\ length res = length cl1 + length cl2})
    = L.append cl1 cl2

let get_smallest_level_from_new_clause (t : truth_assignment) (c : clause) : (res : nat)
    = 
    if length c = 0 then 0
    else
        let var = get_var_from_assignment t (L.hd c) in
        let temp_res = get_smallest_level_from_new_clause t (L.tl c) in
            if var.level < temp_res
            then var.level
            else temp_res

let resolution (t : truth_assignment) (second_clause : clauses) (conflict_clause : clause) (guess_level : nat) (pivot : literal)
    : (res : clause & nat) =
    let cl1_no_pivot = remove_literal_from_list conflict_clause pivot in
    let cl2_no_pivot = remove_literal_from_list second_clause (negate_lit pivot) in
    let new_clause = combine_clauses cl1_no_pivot cl2_no_pivot in
    let new_level = get_smallest_level_from_new_clause t new_clause in
    (new_clause, new_level)

let negate_clause (c : clause) : (res : clause {(length c = length res)}) =
    let x = L.hd c in
    (negate_lit x) :: (negate_clause (L.tl c))

let intersect (#a:Type0) (l1 : list a) (l2 : list a) : (res : list a{
    (length res <= length l1 + length l2)
    /\ (forall (x : a{L.contains x res}). (L.contains x l1 && L.contains x l2))
    /\ (forall (x : a{L.contains l1 && L.contains x l2}). (L.contains x res))
})
    =   if length l1 = 0 then []
        else
            let temp_res = intersect (L.tl l1) l2 in
                if L.contains (L.hd l1) l2 
                then (L.hd l1) :: temp_res
                else temp_res

let rec find_clause_for_resolution (f : formula) (faulty_lits : list literals) : (res : list clause & literal) =
    if length f = 0 then []
    else 
        let cl = L.hd f in
        let cls = L.tl f in
        let common_faulty_literals = intersect faulty_literals (negate_clause cl) in
            if length common_faulty_literals = 0
            then find_clause_for_resolution cls faulty_literals
            else (cl , (L.hd common_faulty_literals))

//exists vars cu acel conf_level, toate din clause sunt in t
let rec find_faulty_literals_in_conflict (t : truth_assignment) (conf_level : nat) (conflict_clause : clause) =
    if length conflict_clause = 0 then []
    else
        let lit_x = L.hd conflict_clause in
        let var_x = get_var_from_assignment t (get_literal_variable lit_x) in
        let xs = find_faulty_literals_in_conflict t conf_level (L.tl conflict_clause) in
            if var_x.level = conf_level
            then lit_x :: xs
            else xs

let solve_conflict (f : formula) (t : truth_assignment {exists_conflict f t}) (current_level : nat) 
    : (res : formula & truth_assignment & nat)
    = let conflict_clause = get_conflict_clause f t in
        let faulty_literals = find_faulty_literals_in_conflict t current_level conflict_clause in
        let (clause_for_resolution, pivot) = find_clause_for_resolution f faulty_literals in
        let (new_clause, new_level) = resolution t clause_for_resolution conflict_clause current_level pivot in
        //am modif putin, vezi dif
            (new_clause :: f, (backtrack_to t new_level ), new_level)

val exists_conflict : formula -> truth_assignment -> bool
let rec existsConflict f t 
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

let rec get_conflict_clause 
    (f : formula) 
    (t : truth_assignment {exists_conflict f t = true})
    : Tot (res : clause{L.contains res f /\ is_clause_false_yet res t = true}) 
    (decreases (L.length f)) = 
    if is_clause_false_yet t (L.hd f) 
    then (L.hd f)
    else get_conflict_clause (L.tl f) t