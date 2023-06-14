module Main

open DataTypes
open DataTypeUtils
open Dpll
open InputFileParser
open ConvertorToString

open FStar.IO
open FStar.List.Tot
open FStar.String

let main = 
    let file_name = input_line () in
    let input_formula = getInput file_name in
    if (FStar.List.Tot.length input_formula = 0)
    then 
        print_string "formula has length 0"
    else 
        let res = dpll input_formula in
        let formula_str = formula_to_string input_formula in
            if Sat? res 
            then 
                let truth_str = truth_to_string (get_truth_from_result res) in 
                let formula_truth_to_str = truth_str in// concat "\n\n" [formula_str ; truth_str] in
                print_string formula_truth_to_str
            else 
                let str_res = "Unsatisfiable" in // concat "\n" [formula_str ; "Unsatisfiable"] in
                print_string str_res
