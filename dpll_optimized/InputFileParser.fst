module InputFileParser

open DataTypes
open ConvertorToString

open FStar.All
open FStar.IO
open FStar.String
open FStar.List
open FStar.Char
open FStar.List.Tot

module L = FStar.List.Tot
module NT = FStar.List


let spaceSeparator = list_of_string " "
let minusChar = hd (list_of_string "-")
let pChar = hd (list_of_string "p")

let x0 = L.hd (list_of_string "0")
let x1 = L.hd (list_of_string "1")
let x2 = L.hd (list_of_string "2")
let x3 = L.hd (list_of_string "3")
let x4 = L.hd (list_of_string "4")
let x5 = L.hd (list_of_string "5")
let x6 = L.hd (list_of_string "6")
let x7 = L.hd (list_of_string "7")
let x8 = L.hd (list_of_string "8")
let x9 = L.hd (list_of_string "9")




let rec multiply (x1 : nat) (x2 : nat) : (res : nat {res > 0 <==> (x1 > 0 /\ x2 > 0)})
    = 
    if x1 = 0 || x2 = 0 then 0
    else x2 + multiply (x1 - 1) x2

let rec powx (x:nat) (n:nat) : (res : nat {x > 0 ==> res > 0})=
    if x = 0 then 0 else
  match n with
  | 0 -> 1
  | _ -> 
        let temp = powx x (n - 1) in
        assert(temp > 0);
        multiply x (powx x (n - 1))

let rec get_index_in_list (#a : eqtype ) (l : list a) (x : a {L.mem x l}) : (res : nat) =
    let h = L.hd l in
    if h = x then 0
    else 1 + get_index_in_list (L.tl l) x


let check_var_string ( l : list char) =
    let res = L.mem x1 l
                || L.mem x2 l 
                || L.mem x3 l 
                || L.mem x4 l 
                || L.mem x5 l 
                || L.mem x6 l 
                || L.mem x7 l
                || L.mem x8 l
                || L.mem x9 l    in
    res

let char_to_int (c : char {L.mem c (list_of_string "0123456789") }) : (res : nat {
    res > 0 <==> check_var_string [c]
}) =
    let res = get_index_in_list (list_of_string "0123456789") c in
    res

let rec string_to_int_helper (str: list char { length str > 0}) : ML (res : nat {
    check_var_string str ==> res > 0
})= 
    let currentChar = hd str in
        if L.mem currentChar (list_of_string "0123456789") = false
        then failwith "variable contains invalid character"
        else
            let currentDigit = char_to_int currentChar in
                if length str = 1
                then char_to_int currentChar
                else
                    let remainingChars = tl str in
                    let powerOf10 = powx 10 (length remainingChars) in
                    let lesserDigitsNumber = string_to_int_helper remainingChars in
                    assert(powerOf10 > 0);
                    let c_digit_with_zeros = multiply currentDigit powerOf10 in
                    assert((powerOf10 > 0 /\ currentDigit > 0) ==> c_digit_with_zeros > 0);
                    let ress = c_digit_with_zeros + lesserDigitsNumber in
                    assert(check_var_string [currentChar] ==> currentDigit > 0);
                    assert(currentDigit > 0 ==> c_digit_with_zeros > 0);
                    ress

let string_to_int (str: list char { 
    length str > 0
    /\ check_var_string str
}) : ML (res : nat {res > 0})= 
    string_to_int_helper str

val getNumberOfClauses : fd_read -> ML( nat & fd_read)
let rec getNumberOfClauses (fileStream: fd_read)  = 
    try
        let line = read_line fileStream in
            if strlen line = 0
            then
                failwith "did not find line that starts with 'p' to indicate number of clauses"
            else
                if hd (list_of_string line) = pChar
                    then  
                        let lineParts = String.split spaceSeparator line in
                        let numberOfClausesStr = NT.last lineParts in
                        let numberOfVariables = NT.last (NT.init lineParts) in
                        if check_var_string (list_of_string numberOfClausesStr) = false
                        then failwith "number of clauses must be a number"
                        else
                            let numberOfClausesInt = string_to_int (list_of_string numberOfClausesStr) in
                                numberOfClausesInt, fileStream 
                    else  
                        getNumberOfClauses fileStream 
    with 
    | _ -> failwith "error eof, did not find number of clauses line"


let createVar (varString: string) =
    let charsList = list_of_string varString in
        match charsList with
        | [] -> failwith varString
        | headList :: others ->
        if headList = minusChar
            then
                let varName = string_of_list ( tl charsList) in
                    if check_var_string (tl charsList)
                    then
                        let var_integer = string_to_int (tl charsList) in
                        NotVar var_integer
                    else failwith "wrong variable input. only non null integers."
            else
                if check_var_string charsList
                then
                    let var_integer = string_to_int charsList in
                    Var var_integer
                else failwith "wrong variable input. only non null integers."

let add_lit_to_clause (c : clause) (l : literal) 
    : (res : clause {
        L.mem l res 
        /\ (forall (l2  :literal {L.mem l2 c}). (L.mem l2 res))})
    = l :: c

val createClause : list string -> ML clause
let rec createClause (variables: list string) = 
    let headVar = NT.hd variables in
        if strlen headVar = 0 
            then createClause (NT.tl variables)
            else let newVar = createVar (NT.hd variables) in
                if length variables = 1
                    then 
                        [newVar]
                    else 
                        let subClause = createClause (NT.tl variables) in
                            add_lit_to_clause subClause newVar 
    

let rec fromStringArrayToLog (stringList : list string) = 
    match stringList with
    |   [] -> ""
    |   x :: [] -> x
    |   x :: xs -> 
         String.concat "+" [x; (fromStringArrayToLog xs)]
        

let rec removeConsecutiveSpaces' (s : list char) (f : bool) =
    match s with
    | [] -> list_of_string ""
    | x :: xs -> if (string_of_char x) = " " 
        then 
            if f
                then removeConsecutiveSpaces' xs true
                else x :: (removeConsecutiveSpaces' xs true)
        else x :: ( removeConsecutiveSpaces' xs false)

let removeConsecutiveSpaces (s : string) = string_of_list ( removeConsecutiveSpaces' (list_of_string s) false)

val readInputFormula : fd_read -> int -> ML formula
let rec readInputFormula (fileStream: fd_read) (numberOfClausesLeft: int) =
    try
    if numberOfClausesLeft = 0
        then
            []
        else 
            let newLine = read_line fileStream in
                let same_line = removeConsecutiveSpaces newLine in
                    let variables = NT.init ( String.split spaceSeparator same_line) in
                        let newClause = createClause variables in
                          newClause :: (readInputFormula fileStream (numberOfClausesLeft - 1) )
    with
    | EOF -> []
    | _ -> failwith "error at read input formula"


val getInput : string -> ML formula
let getInput (fileName: string ) = 
    let fileStream = open_read_file fileName in
        let numberOfClauses, fileStream' = getNumberOfClauses fileStream in
            let f = readInputFormula fileStream' numberOfClauses in
            if length f = 0
            then failwith (concat " - " ["error" ; (int_to_string numberOfClauses)])
            else f

