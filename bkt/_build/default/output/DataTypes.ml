open Prims
type nat_non_zero = Prims.int
type literal =
  | Var of nat_non_zero 
  | NotVar of nat_non_zero 
let (uu___is_Var : literal -> Prims.bool) =
  fun projectee -> match projectee with | Var a -> true | uu___ -> false
let (__proj__Var__item__a : literal -> nat_non_zero) =
  fun projectee -> match projectee with | Var a -> a
let (uu___is_NotVar : literal -> Prims.bool) =
  fun projectee -> match projectee with | NotVar a -> true | uu___ -> false
let (__proj__NotVar__item__a : literal -> nat_non_zero) =
  fun projectee -> match projectee with | NotVar a -> a
type clause = literal Prims.list
type variable_info = {
  value: Prims.bool ;
  variable: nat_non_zero }
let (__proj__Mkvariable_info__item__value : variable_info -> Prims.bool) =
  fun projectee -> match projectee with | { value; variable;_} -> value
let (__proj__Mkvariable_info__item__variable : variable_info -> nat_non_zero)
  = fun projectee -> match projectee with | { value; variable;_} -> variable
type truth_assignment = variable_info Prims.list
type formula = clause Prims.list
type result =
  | NotSat 
  | Sat of truth_assignment 
let (uu___is_NotSat : result -> Prims.bool) =
  fun projectee -> match projectee with | NotSat -> true | uu___ -> false
let (uu___is_Sat : result -> Prims.bool) =
  fun projectee -> match projectee with | Sat a -> true | uu___ -> false
let (__proj__Sat__item__a : result -> truth_assignment) =
  fun projectee -> match projectee with | Sat a -> a
let (empty_assignment : truth_assignment) = []
let empty_formula : 'uuuuu . unit -> 'uuuuu Prims.list = fun uu___ -> []