module Main

open DataTypes
open Dpll
open InputFileParser
open FStar.IO
open FStar.List.Tot

open FStar.IO

let main = 
    let file_name = input_line () in
    let input_formula = getInput file_name in
    if (length input_formula = 0)
    then 
        print_string "formula has length 0"
    else 
        let res = dpll input_formula in
            if Sat? res = true
            then 
                let mess = "True" in
                print_string mess
            else 
                let mess = "False" in 
                print_string mess