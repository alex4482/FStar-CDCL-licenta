module ConvertorToString 

open FStar.String
open FStar.List.Tot

module L = FStar.List.Tot

open DataTypes

let new_line_string = "\n"

let concat_to_truth (s1 : string) (s2 : string) = concat new_line_string [s1 ; s2]


let rec int_to_string (i : nat) =
    if i = 0
    then "0"
    else 
        if i > 9
        then    
            let last_digit = i `op_Modulus` 10 in
            let other_digits = i `op_Division` 10 in
            let res = concat "" [(int_to_string other_digits) ; (int_to_string last_digit)] in
            res
        else
            if i = 1
            then "1"
            else
            if i = 2
            then "2"
            else
            if i = 3
            then "3"
            else
            if i = 4
            then "4"
            else
            if i = 5
            then "5"
            else
            if i = 6
            then "6"
            else
            if i = 7
            then "7"
            else
            if i = 8
            then "8"
            else "9"

let bool_to_string (b : bool) =
    if b 
    then "True"
    else "False"

let literal_to_string (l : literal) =
    match l with
    | Var x -> int_to_string x
    | NotVar x -> concat "" [ "-" ; int_to_string x]

let rec clause_to_string (c : clause) =
    let x = L.hd c in
    let x_str = literal_to_string x in
        if length c = 1
        then x_str
        else
            let xs_str = clause_to_string (L.tl c) in
            concat "  /\\  " [x_str ; xs_str]

let rec formula_to_string (f : formula{length f > 0}) : (res : string)
    = 
    let x = L.hd f in
    let x_str = clause_to_string x in
        if length f = 1
        then x_str
        else
            let xs_str = formula_to_string (L.tl f) in
            concat "\n" [x_str ; xs_str]



let var_info_to_string (v : variable_info) : (res : string)
    = 
    let var_string = int_to_string v.variable in
    let var_value = bool_to_string v.value in
    concat " = " [var_string ; var_value]

let rec truth_to_string (t : truth_assignment {length t > 0}) : (t_string : string) =
    let x = L.hd t in
    let x_to_string = var_info_to_string x in
        if length t = 1
        then concat_to_truth x_to_string "\nSatisfiable"
        else
            let xs = L.tl t in
            let xs_to_string = truth_to_string xs in
            let res = concat_to_truth x_to_string xs_to_string in
            res 