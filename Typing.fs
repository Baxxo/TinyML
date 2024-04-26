(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list


// Freevar
// 

// global counter for new name for variables
let mutable free_var_name = 0

let new_fresh_name () :ty =
    free_var_name <- free_var_name + 1
    TyVar free_var_name 

// calculates the free type var occuring in a type 
let rec freevars_ty t =
    match t with
    | TyName tn -> Set.empty
    | TyVar tv -> Set.singleton tv
    | TyArrow (t1, t2) -> (freevars_ty t1) +  (freevars_ty t2)
    | TyTuple tl -> List.fold (fun l_set x -> l_set + freevars_ty x) Set.empty tl

// calculates the free type var occuring in a scheme 
let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) tvs 

// calculates the free type var occuring in an enviroment
let freevars_scheme_env (env : ('a * scheme) list) =
    List.fold (fun ftv_env (s_tyvar, ty) -> ftv_env + freevars_scheme ty) Set.empty env

let rec apply_subst (t : ty) (s : subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar n -> let _, r = List.find (fun (n', t) -> n = n') s in r
    | TyArrow (t1, t2) -> TyArrow (apply_subst t1 s, apply_subst t2 s)
    | TyTuple tuple -> let new_tuple =  List.map (fun x -> apply_subst x s) tuple in TyTuple(new_tuple)

let rec apply_subst_to_subst (s1: subst) (s2:subst): subst =
    match s2 with
    | [] -> []
    | (v, t_y) :: t -> (v, apply_subst t_y s1) :: apply_subst_to_subst s1 t

// devo applicare le substitution a tutte le coppie che non contengono la prima parte della substitution
let apply_subst_to_scheme (Forall(tvs, t)) (s: subst): scheme =
    let new_subst = List.filter (fun (tv,_) -> not (Set.contains tv tvs)) s
    Forall(tvs, apply_subst t new_subst)

let rec apply_subst_to_env (env: scheme env) (s: subst): scheme env =
    match env with
    | [] -> []
    | (tv, t) :: tail ->
        (tv, apply_subst_to_scheme t s) :: apply_subst_to_env tail s
    

let rec compose_subst (s1 : subst) (s2 : subst) : subst = //s1 @ s2
    match s1 with
    | [] -> []
    | (v,ty) :: t ->  // appplicare s2 a t
        apply_subst_to_subst t s2
        

let ($) = compose_subst

// accept two types and produces a substitution that makes the 2 types equal
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match (t1, t2) with
    | (TyName s1, TyName s2) when s1 = s2 -> []
    | (TyVar n, t)
    | (t, TyVar n) -> [n, t]
    | (TyArrow (t1, t2), TyArrow (t3, t4)) -> compose_subst (unify t1 t3) (unify t2 t4)
    | (TyTuple(t1), TyTuple(t2)) ->
        if t1.Length <> t2.Length then
            type_error "unify: t1 and t2 have different legntgh (%d, %d)" t1.Length t2.Length
        else
            match t1, t2 with
            | [], [] -> []
            | h1 :: tail1, h2 :: tail2 -> compose_subst (unify h1 h2) (unify (TyTuple(tail1)) (TyTuple(tail2)))
            | _ -> type_error "unify Tuple: t1 and t2 are not type (%O %O)" t1 t2

    | _ -> type_error "%s does not unify with %s" (pretty_ty t1) (pretty_ty t2)

// basic environment: add builtin operators at will
//

let gamma0 = [
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (">", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    ("<=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
    (">=", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
]
// Forall of tyvar Set * ty
let gamma0_infer = [
    ("+", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("*", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("/", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("<", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    (">", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    ("<=", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
    (">=", Forall (Set.empty, TyArrow (TyInt, TyArrow (TyInt, TyBool))))
]


// Generalization
// 

// generalization promotes a type t to a type scheme o by quantifying type variables that represent
// polymorphic types through the universal quantifier Forall
let generalize env t =
    let diff = Set.difference (freevars_ty t) (freevars_scheme_env env)
    Forall(diff, t)

// Instantiation
// 

// converting type scheme into a type by refreshing its polymorphic type variables
let instantiate (Forall (tvs, t)) : ty =
    let new_vars:subst = Set.fold (fun acc ty_name -> (ty_name, new_fresh_name ()) :: acc ) List.empty tvs
    apply_subst t new_vars


// type inference
//

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []
    
    | Var (var_name) -> 
        let (value_var : scheme) = lookup_scheme env var_name
        let (var_ty: ty) = instantiate value_var

        var_ty, List.empty

    | UnOp (op, e) ->
        typeinfer_expr env (App (Var op, e))

    | BinOp (e1, op, e2) ->
        typeinfer_expr env (App (App (Var op, e1), e2))

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool

        let t2, s3 = typeinfer_expr env e2
        match e3o with        
        | None ->
            let s4 = unify t2 TyUnit

            let s = s4 $ s3 $ s2 $ s1
            apply_subst t2 s, s

        | Some e3 ->
            let t3, s4 = typeinfer_expr env e3
            let s5 = unify t2 t3

            let s = s5 $ s4 $ s3 $ s2 $ s1
            apply_subst t2 s, s

    | App (e1, e2) ->
        // questo secondo il foglio,
        // secondo wikipedia però dovrei utilizzare ciò che c'è tra //
        // https://wikimedia.org/api/rest_v1/media/math/render/svg/431b94815103ac9dc77d0e92739456c3c2c90803
        let t1, s1 = typeinfer_expr env e1

        let t2, s2 = typeinfer_expr (apply_subst_to_env env s1) e2

        let alpha = new_fresh_name ()

        // let s3 = unify (apply_subst t1 s2) (TyArrow (t2, alpha))
        let s3 = unify t1 (TyArrow (t2, alpha))

        let t = apply_subst alpha s3

        // let s4 = s3 $ s2 $ s1
        let s4 = s3 $ s2

        t, s4

    | Lambda (var_name, tyo, e) ->
        // inizio lez. 17
        // per poli lez. 20
        let alpha = new_fresh_name ()
        let new_scheme = Forall(Set.empty, alpha) 

        let (t2: ty, s1:subst) = typeinfer_expr ((var_name, new_scheme) :: env) e

        let t1: ty = apply_subst alpha s1

        match tyo with
        | None -> TyArrow(t1, t2), s1
        | Some t_n ->
            // Rendo i tipi compatibili trovando una sostituzione
            let s = unify t_n t1
            // Applico a t1 e t2
            let t1 = apply_subst t1 s
            let t2 = apply_subst t2 s
            // Restituisce il tipo della funzione e la sostituzione risultante
            TyArrow(t1, t2), s

    | Let (var_name, tyo, e1, e2) ->
        // lez. 19
        let t1, s1 = typeinfer_expr env e1

        let env = apply_subst_to_env env s1

        let scheme1 = generalize env t1

        // lez. 15
        let new_env : scheme env = (var_name, scheme1) :: env

        let t2, s2 = typeinfer_expr new_env e2

        match tyo with
        | None -> t2, s2 $ s1
        | Some t ->
            let s4 = compose_subst (unify t1 t) s1
            apply_subst t2 s4, s4

    | LetRec (var_name, tyo, e1, e2) -> // TODO
           TyUnit, []
            
    | Tuple (t: expr list) -> // TODO
        TyUnit, []

        //let t_new = List.fold (fun (expr) -> (typeinfer_expr env expr)) t

        //TyTuple t_new, []
    
    | _ -> type_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e



// type checker
//

let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x -> lookup env x

    | Let (x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Let (x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1
        if t <> t1 then type_error "type %O differs from type %O in let-binding" t1 t
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Lambda (x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow (t, te)

    | Lambda (x, None, e) ->
        type_error "unannotated lambdas are not supported by the type checker"

    | App (e1, e2) ->
        let t2 = typecheck_expr env e2
        match typecheck_expr env e1 with
        | TyArrow (ta, tb) -> 
            if ta <> t2 then type_error "argument has type %O while function parameter has type %O in application" t2 ta
            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    | IfThenElse (e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "bool expected in if guard, but got %O" t1
        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3
        if t2 <> t3 then type_error "then and else branches have different types: %O and %O" t2 t3
        t2
        
    | IfThenElse (e1, e2, None) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "bool expected in if guard, but got %O" t1
        let t2 = typecheck_expr env e2
        t2

    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyInt

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "operand of not-operator is not a bool: %O" t
        TyBool
        
    | BinOp (e1, "=", e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        if t1 <> t2 then type_error "left and right hands of equality operator are different: %O and %O" t1 t2
        TyBool

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyBool

    | BinOp (_, op, _) -> type_error "operation not supported (%s)" op
    | UnOp (op, _) -> type_error "operation not supported (%s)" op

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)

    | _ -> type_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e


(*

| IfThenElse (e1, e2, e3o) ->
(*
Versione prof
let t1, s1 = typeinfer_expr env e1
let s2 = unify t1 TyBool

let t2, s3 = typeinfer_expr env e2
let t3, s4 = typeinfer_expr env e3
let s5 = unify t2 t3

let s = s5 $ s4 $ s3 $ s2 $ s1
apply_subst t2 s, s
*)

let t1, s1 = typeinfer_expr env e1
let s2 = unify t1 TyBool

let t2, s3 = typeinfer_expr env e2
match e3o with        
| None ->
    let s4 = unify t2 TyUnit

    let s = s4 $ s3 $ s2 $ s1
    apply_subst t2 s, s

| Some e3 ->
    let t3, s4 = typeinfer_expr env e3
    let s5 = unify t2 t3

    let s = s5 $ s4 $ s3 $ s2 $ s1
    apply_subst t2 s, s

(*
let t1, s1 = typeinfer_expr env e1
let s2 = unify t1 TyBool

let s3 = s2 $ s1
let t2, s4 = typeinfer_expr (apply_subst_to_env env s3) e2

let s5 = s4 $ s3

match e3o with        
| None ->        
    let s6 = unify t2 TyUnit                    
    apply_subst t2 s5, s6

| Some e3 ->
    let t3, s6 = typeinfer_expr (apply_subst_to_env env s5) e3

    let s7 = s6 $ s5

    let s8 = unify (apply_subst t2 s7) (apply_subst t3 s7)

    let s9 = s8 $ s7

    apply_subst t2 s8, s9
*)

    (*| IfThenElse (e1, e2, None) ->
(*
Versione prof
let t1, s1 = typeinfer_expr env e1
let s2 = unify t1 TyBool

let t2, s3 = typeinfer_expr env e2
let s4 = unify t2 TyUnit

let s = s4 $ s3 $ s2 $ s1
apply_subst t2 s, s
*)

let t1, s1 = typeinfer_expr env e1
let s2 = unify t1 TyBool
        
let s3 = s2 $ s1
let t2, s4 = typeinfer_expr (apply_subst_to_env env s3) e2

let s5 = s4 $ s3

let s6 = unify t2 TyUnit

apply_subst t2 s5, s6*)

*)