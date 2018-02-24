open Position
open Error
open HopixAST

(** [error pos msg] reports runtime error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of hopix evaluates into a [value]. *)
type 'e gvalue =
  | VBool         of bool
  | VInt          of Int32.t
  | VChar         of char
  | VString       of string
  | VUnit
  | VAddress      of Memory.location
  | VTaggedValues of constructor * 'e gvalue list
  | VPrimitive    of string * ('e gvalue Memory.t -> 'e gvalue list -> 'e gvalue)
  | VFun          of pattern located list * expression located * 'e
  | VTypeDefin     of  'e gvalue list

type ('a, 'e) coercion = 'e gvalue -> 'a option
let value_as_int      = function VInt x -> Some x | _ -> None
let value_as_bool     = function VBool x -> Some x | _ -> None
let value_as_char     = function VChar c -> Some c | _ -> None

type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x

let primitive name ?(error = fun () -> assert false) coercion wrapper f =
  VPrimitive (name, fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

let print_value m v =
  let max_depth = 5 in

  let rec print_value d v =
    if d >= max_depth then "..." else
      match v with
        | VInt x ->
          Int32.to_string x
        | VBool true ->
          "true"
        | VBool false ->
          "false"
	| VChar c ->
	  "'" ^ Char.escaped c ^ "'"
	| VString s ->
	  "\"" ^ String.escaped s ^ "\""
	| VUnit ->
	  "()"
	| VAddress a ->
	  print_array_value d (Memory.dereference m a)
	| VTaggedValues (KId k, []) ->
	  k
	| VTaggedValues (KId k, vs) ->
	  k ^ "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
	| VFun _ ->
	    "<fun>"
	| VTypeDefin l ->
	    String.concat "|" (List.map (print_value (d + 1)) l)
        | VPrimitive (s, _) ->
          Printf.sprintf "<primitive: %s>" s
  and print_array_value d block =
    let r = Memory.read block in
    let n = Memory.size block in
    "[ " ^ String.concat ", " (
      List.(map (fun i -> print_value (d + 1) (r i)) (ExtStd.List.range 0 (n - 1))
      )) ^ " ]"
  in
  print_value 0 v

module Environment : sig
  (** Evaluation environments map identifiers to values. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x v] extends [env] with a binding from [x] to [v]. *)
  val bind    : t -> identifier -> t gvalue -> t

  (** [update pos x env v] modifies the binding of [x] in [env] so
      that [x ↦ v] ∈ [env]. *)
  val update  : Position.t -> identifier -> t -> t gvalue -> unit

  (** [lookup pos x env] returns [v] such that [x ↦ v] ∈ env. *)
  val lookup  : Position.t -> identifier -> t -> t gvalue

  (** [UnboundIdentifier (x, pos)] is raised when [update] or
      [lookup] assume that there is a binding for [x] in [env],
      where there is no such binding. *)
  exception UnboundIdentifier of identifier * Position.t

  (** [last env] returns the latest binding in [env] if it exists. *)
  val last    : t -> (identifier * t gvalue * t) option

  (** [print env] returns a human readable representation of [env]. *)
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e

end

type value = Environment.t gvalue

type formals = identifier list

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}

type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    VPrimitive (name, fun _ -> function
      | [VInt x; VInt y] -> out (op x y)
      | e ->Printf.printf " la list = %d" (List.length e);  assert false (* By typing. *)
    )
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v)) x l
  in
  (* Define arithmetic binary operators. *)
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Int32.(
    [ ("`+", add); ("`-", sub); ("`*", mul); ("`/", div) ]
  ) in
  (* Define arithmetic comparison operators. *)
  let cmparith name = intbin name (fun x -> VBool x) in
  let cmparithops =
    [ ("`=", ( = )); ("`<", ( < )); ("`>", ( > )); ("`>=", ( >= )); ("`<=", ( <= )) ]
  in
  let boolbin name out op =
    VPrimitive (name, fun m -> function
      | [VBool x; VBool y] -> out (op x y)
      | _ -> assert false (* By typing. *)
    )
  in
  let boolarith name = boolbin name (fun x -> VBool x) in
  let boolarithops =
    [ ("`||", ( || )); ("`&&", ( && )) ]
  in
  let generic_printer =
    VPrimitive ("print", fun m vs ->
      let repr = String.concat ", " (List.map (print_value m) vs) in
      output_string stdout repr;
      flush stdout;
      VUnit
    )
  in
  let print s =
    output_string stdout s;
    flush stdout;
    VUnit
  in
  let print_int =
    VPrimitive  ("print_int", fun m -> function
      | [ VInt x ] -> print (Int32.to_string x)
      | _ -> assert false (* By typing. *)
    )
  in
  let print_string =
    VPrimitive  ("print_string", fun m -> function
      | [ VString x ] -> print x
      | _ -> assert false (* By typing. *)
    )
  in
  let bind' x w env = Environment.bind env (Id x) w in
  Environment.empty
  |> bind_all binarith binarithops
  |> bind_all cmparith cmparithops
  |> bind_all boolarith boolarithops
  |> bind' "print"        generic_printer
  |> bind' "print_int"    print_int
  |> bind' "print_string" print_string
  |> bind' "true"         (VBool true)
  |> bind' "false"        (VBool false)

let initial_runtime () = {
  memory      = Memory.create (640 * 1024 (* should be enough. -- B.Gates *));
  environment = primitives;
}
    
exception NoPatternMatch
    
let rec evaluate runtime ast =
  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)

(* [definition pos runtime d] evaluates the new definition [d]
   into a new runtime [runtime']. In the specification, this
   is the judgment:

			E, M ⊢ dᵥ ⇒ E', M'

*)
and definition runtime d =
  match Position.value d with
  | DefineValue (x, e) ->
    let v = expression' runtime.environment runtime.memory e in
    { runtime with
      environment = bind_identifier runtime.environment x v
    }
  | DefineType (tp, tv, td) ->
      begin match tp.value with
      | TCon x -> let id  = (Id x) in let l = typedefintion td
      in let y = { tp with value= id } in
	{ runtime with
          environment = bind_identifier runtime.environment y   (VTypeDefin l)
        }
      end
	
	
  | DeclareExtern (id,ty) -> failwith "Not implemented"
  | DefineRecFuns( lst ) ->
      let l = List.map (fun (id, df) ->
	(id, df.value) ) lst in
      definerecfun runtime l

and typedefintion t =
  match t with
  | DefineSumType tl -> List.map (fun (x,y) -> VTaggedValues(x.value , [])) tl
  | Abstract -> []
	
and definerecfun run l =
  let new_run = defineAllfun run l
  in finalruntime new_run run l
    
and defineAllfun run l =
  match l with
  | []-> run
  | (x,e)::tl -> let new_run = know_fun run x e
  in definerecfun new_run tl

and know_fun run x e =
  match e with
  | FunctionDefinition(lty,lp,exp) ->
      try
	Environment.update x.position x.value run.environment (VFun(lp,exp,run.environment)) ;
	run
      with Environment.UnboundIdentifier (_,_) ->	
      {environment = bind_identifier run.environment x (VFun(lp,exp,run.environment))
							  ; memory = run.memory}
  | _ -> failwith "error functiondefintion"

and finalruntime run run_final = function
  | [] -> run_final
  | (x,e)::tl ->
      let new_run = know_fun run x e
      in finalruntime run new_run tl
	
and patternList lp le run =
  match lp,le with
  | [],[] -> run
  | p::pq,e::eq ->      
      let new_run = patterns (p.value) e run
      in patternList pq eq new_run
  | _,_ -> failwith "error function defintion patterns"

and expression' environment memory e =
  expression (position e) environment memory (value e)

(* [expression pos runtime e] evaluates into a value [v] if

                          E, M ⊢ e ⇓ v, M'

   and E = [runtime.environment], M = [runtime.memory].
*)
and expression position environment memory = function

  |Apply (e,ty,es) ->
      let vbs = expressions environment memory es in 
      begin match (expression' environment memory e) with
      | VPrimitive (_,f) ->
	   f memory vbs
      | VFun (lp,e,env) ->
	  let run = {environment = env ; memory = memory}
	  in let new_run = patternList lp vbs run
	  in expression' new_run.environment new_run.memory e
  
      | _ -> assert false 
      end
  | Fun (FunctionDefinition(tys,ps,e)) -> VFun (ps,e,environment)
  | Literal l -> literal (l.value)
  | Variable v -> Environment.lookup position (v.value) environment
  | Define (id, e1, e2) -> let x = expression' environment memory e1 in
    expression' (bind_identifier environment id x) memory e2
  | If (l_c_e,e) ->
      let rec eval_if l =
      begin match l with
      |(((c,e1)::q),e) ->
         let v = expression' environment memory c in
	 begin match value_as_bool v with
	 |None -> Printf.printf "Not valid if condition" ; assert false
	 |Some true -> expression' environment memory e1
	 |Some false -> eval_if (q,e)
         end
      |([],e) -> begin match e with |None -> VUnit |Some exp -> expression' environment memory exp end
      end
      in eval_if (l_c_e,e)
  | Tagged (c,l_ty,l_e) ->
      let l = List.map (fun x -> (expression' environment memory x)) l_e in
      VTaggedValues (c.value, l)
  | TypeAnnotation (e,_) -> expression' environment memory e
  | Ref e -> let v = expression' environment memory e in
    let adr = Memory.allocate memory 1 v in
    VAddress adr
  | Read e -> let v = expression' environment memory e in
    begin match v with
    | VAddress a -> Memory.read (Memory.dereference memory a) 0
    | _ -> failwith "error address"
    end
  | Write (e1,e2) -> let v1 = expression' environment memory e1 in
    begin match v1 with
    | VAddress a -> let v2 = expression' environment memory e2 in
      Memory.write  (Memory.dereference memory a) 0 v2; 
      VUnit
    | _ -> failwith "error address"
    end
  | While (e1,e2) -> 
  let rec eval_while (c,e) =
      let v = expression' environment memory c in
      begin match value_as_bool v with
      | None -> Printf.printf "Not valid While condition"; assert false
      (* mauvais typing ?? *)
      | Some true -> expression' environment memory e ; eval_while (c,e)
      | Some false -> VUnit
      end
  in  eval_while (e1,e2)
  | DefineRec (lst,e) ->
      let run = {environment = environment ; memory = memory}
      in let new_run = definerecfun run (List.map (fun (id,df) -> (id,df.value))  lst) 
      in expression' new_run.environment new_run.memory e
	    
  | Case (e,l) ->
    let lb = List.map (fun x -> value x) l in
    let runtime = {environment = environment ; memory = memory} in
    let v = expression' environment memory e in
    branches runtime v lb
  | _ -> failwith "Student! This is your job!"

and branches runtime e lb =
  match lb with
  | [] -> failwith "No patterns"
  | Branch (p,exp)::q ->
      try
       let run  =  patterns (p.value) e runtime in
	expression' run.environment run.memory exp
      with NoPatternMatch -> branches runtime e q

and patterns p e runtime  =
  match p with
   | PWildcard -> runtime
	
  | PVariable id -> { environment = bind_identifier runtime.environment id e   ; memory = runtime.memory}
    
  | PLiteral x ->
      begin match e with
      | VInt y when(LInt y = x.value) -> runtime
      | VChar y when(LChar y = x.value) -> runtime
      | VString y when(LString y = x.value) -> runtime
      | VBool y when(LBool y = x.value) -> runtime
      | _ -> raise NoPatternMatch
      end	
  | PTypeAnnotation (a,_) -> patterns a.value e runtime
	
  | PTaggedValue (cons,p_list) ->
      begin match e with
      | VTaggedValues (cons', gv_list) when( (cons.value) = cons' && List.length p_list = List.length gv_list) ->
	  let rec aux pl gvl run =
	    match pl, gvl with
	    | [],[] -> run
	    | p::qp , g::qg ->
		aux qp qg (patterns p.value g run)
	    | _ -> failwith "error pattern tagged value"
	  in aux p_list gv_list runtime
      | _ -> raise NoPatternMatch
      end
	
  | POr p_list ->
      let rec aux = function
	| [] -> raise NoPatternMatch
	| p::q ->
	    try
	      patterns p.value e runtime
	    with NoPatternMatch -> aux q
      in aux p_list
	
  | PAnd p_list ->
      let rec aux run = function
	| [] -> run
	| p::qp ->
	    try
	      aux (patterns p.value e run) qp
	    with NoPatternMatch -> raise NoPatternMatch
      in aux runtime p_list
	(* warning unused *)
  | _ -> raise NoPatternMatch
	

and expressions environment memory es =
  let rec aux vs memory = function
    | [] ->
      List.rev vs
    | e :: es ->
      let v = expression' environment memory e in
      aux (v :: vs) memory es
  in
  aux [] memory es


and bind_identifier environment x v =
  Environment.bind environment (Position.value x) v

and literal = function
  | LInt x -> VInt x
  | LBool x -> VBool x
  | LChar x -> VChar x
  | LString x -> VString x

and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

let print_observable runtime observation =
  Environment.print observation.new_memory observation.new_environment
