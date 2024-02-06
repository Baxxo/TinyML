﻿(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// evaluator
//

let rec eval_expr (venv : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit 
    
    | Var var_name -> lookup venv var_name

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | App (e1, e2) -> 
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1 with
        | Closure (venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e

        | _ -> unexpected_error "non-closure on left hand of application"

    | BinOp (e1: expr, ("+" | "-" | "*" | "/" as op), e2: expr) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1, v2, op with
        | VLit (LInt x), VLit (LInt y), op ->
            match op with
            | "+" -> VLit(LInt( (+) x y))
            | "-" -> VLit(LInt( (-) x y))
            | "*" -> VLit(LInt( (*) x y))
            | "/" -> VLit(LInt( (/) x y))
            | _ -> unexpected_error "eval_expr: unsupported int operator for BinOp"

        | _ -> unexpected_error "eval_expr: unsupported expression BinOp"
        
    | BinOp (e1: expr, ("and" | "or" as op), e2: expr) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1, v2, op with
        | VLit (LBool x), VLit (LBool y), op ->
            match op with
            | "and" -> VLit(LBool( x && y))
            | "or" -> VLit(LBool(x || y))
            | _ -> unexpected_error "eval_expr: unsupported boolean operator for BinOp"

        | _ -> unexpected_error "eval_expr: unsupported expression BinOp"
        

    | BinOp (e1: expr, ("=" | "<" | ">" | "<=" | ">=" | "and" | "or" as op), e2: expr) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match op with
        | "=" -> VLit(LBool(v1 = v2))
        | "<" -> VLit(LBool(v1 < v2))
        | ">" -> VLit(LBool(v1 > v2))
        | "<=" -> VLit(LBool(v1 <= v2))
        | ">=" -> VLit(LBool(v1 >= v2))
        | _ -> unexpected_error "eval_expr: unsupported boolean operator for BinOp"

    | BinOp (_, op, _) -> unexpected_error "eval_expr: unsupported operator (%s) for BinOp" op
    
    | IfThenElse (e1, e2, Some e3) ->
        let value_guard = eval_expr venv e1
        match value_guard with
        | VLit(LBool(true)) ->  eval_expr venv e2 
        | VLit(LBool(false)) -> eval_expr venv e3
        | _ -> unexpected_error "eval_expr: unsupported guard value (%O) for IfThenElse" value_guard
        
    | IfThenElse (e1, e2, None) ->
        let value_guard = eval_expr venv e1
        match value_guard with
        | VLit(LBool(true)) ->  eval_expr venv e2 
        | VLit(LBool(false)) -> VLit(LUnit)
        | _ -> unexpected_error "eval_expr: unsupported guard value (%O) for IfThenElse" value_guard

    | LetIn (_, e) -> eval_expr venv e

    | Tuple l -> // TODO
        // la funzione map modifica la lista o ne crea una nuova?
        (*let new_tuple = List.map (fun (f, l) -> f l) eval_expr l
        VTuple(new_tuple)*)

    | UnOp (op,e) ->
        match op with
        | "not" ->
            let v = eval_expr venv e
            match v with
            | VLit(LBool(true)) ->  VLit(LBool(false))
            | VLit(LBool(false)) -> VLit(LBool(true))
            | _ -> unexpected_error "eval_expr: unsupported value (%O) for not operator" v
        | _ ->  unexpected_error "eval_expr: unsupported operator (%O) for UnOp" op

    // TODO complete this implementation

    //| _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e