module InputFileParser

open DataTypes

open FStar.All
open FStar.IO
open FStar.String
open FStar.List
open FStar.Char
open FStar.List.Tot

module L = FStar.List.Tot
module NT = FStar.List

let add_lit_to_clause (c : clause) (l : literal) 
    : (res : clause {
        L.mem l res 
        /\ (forall (l2  :literal {L.mem l2 c}). (L.mem l2 res))})
    = l :: c

let spaceSeparator = list_of_string " "
let spaceString = " "
let minusChar = hd (list_of_string "-")
let pChar = hd (list_of_string "p")

val powx : x:nat -> n:nat -> Tot nat
let rec powx x n =
  match n with
  | 0 -> 1
  | _ -> op_Multiply x (powx x (n - 1))

val stringToInt : list char -> ML nat
let rec stringToInt (str: list char) = 
    if length str = 0
        then 
            0
        else
            let remainingChars = tl str in
                let powerOf10 = powx 10 (length remainingChars) in
                    let lesserDigitsNumber = stringToInt remainingChars in
                        assert(lesserDigitsNumber >= 0);
                        let currentChar = hd str in
                            let currentDigit = (int_of_char currentChar) in // - (int_of_char (hd (list_of_string "0"))) 
                                assert(currentDigit >= 0);
                                (op_Multiply currentDigit powerOf10) + lesserDigitsNumber



val getNumberOfClauses : fd_read -> ML( int & fd_read)
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
                        let numberOfClausesInt = stringToInt (list_of_string numberOfClausesStr) in
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
                    let var_integer = stringToInt (tl charsList) in
                    NotVar (var_integer + 1)
            else
                let var_integer = stringToInt charsList in
                Var (var_integer + 1)

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
    | _ -> []


val getInput : string -> ML formula
let getInput (fileName: string ) = 
    let fileStream = open_read_file fileName in
        let numberOfClauses, fileStream' = getNumberOfClauses fileStream in
            readInputFormula fileStream' numberOfClauses

