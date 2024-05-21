(*
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

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | Var x -> lookup venv x

    | BinOp (e1: expr, ("+" | "-" | "*" | "/" | "%" as op), e2: expr) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1, v2, op with
        | VLit (LInt x), VLit (LInt y), op ->
            match op with
            | "+" -> VLit(LInt( (+) x y))
            | "-" -> VLit(LInt( (-) x y))
            | "*" -> VLit(LInt( (*) x y))
            | "/" -> VLit(LInt( (/) x y))
            | "%" -> VLit(LInt( (%) x y))
            | _ -> unexpected_error "eval_expr: unsupported int operator for BinOp"

        | _ -> unexpected_error "eval_expr: unsupported expression BinOp"
        
    | BinOp (e1: expr, ("and" | "or" as op), e2: expr) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1, v2, op with
        | VLit (LBool x), VLit (LBool y), op ->
            match op with
            | "and" -> VLit(LBool( (&&) x y))
            | "or" -> VLit(LBool((||)x y))
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
        
    | App (e1, e2) ->

        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2

        match v1 with
        | Closure (venv', x, e0) ->
            let venv0 = (x, v2) :: venv'
            eval_expr venv0 e0

        | RecClosure (venv',f, x, e0) ->

            let venv0 = (f, v1) :: (x, v2) :: venv'

            eval_expr venv0 e0

        | _ -> unexpected_error "not closure nor rec-closure on left hand of application"
    
    | Let (x, _, e1, e2) ->
        let v1 = eval_expr venv e1
        let venv' = (x, v1) :: venv
        eval_expr venv' e2

    | LetRec (f, _, e1, e2) ->

        let v1 = eval_expr venv e1

        // calcolo della rec-closure
        let vc =
            match v1 with
            | Closure (venv', x, e) ->
                RecClosure(venv', f, x, e)

            | _ -> unexpected_error "not rec-closure on left hand of application"

        printf "vc: %O\n\n" vc

        eval_expr ((f, vc) :: venv) e2

    | UnOp (op,e) ->
        match op with
        | "not" ->
            let v = eval_expr venv e
            match v with
            | VLit(LBool(true)) ->  VLit(LBool(false))
            | VLit(LBool(false)) -> VLit(LBool(true))
            | _ -> unexpected_error "eval_expr: unsupported value (%O) for not operator" v
        | _ ->  unexpected_error "eval_expr: unsupported operator (%O) for UnOp" op

    | Tuple tuple ->
        let new_tuple = List.map (fun x -> eval_expr venv x) tuple in VTuple(new_tuple)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e