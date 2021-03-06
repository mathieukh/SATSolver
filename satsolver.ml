type litteral = {d:int;value:bool}
type litteral_annot = {litteral:litteral;dependencies:litteral list}
type clause = {litterals:litteral list;causes:litteral list}
type interpretation = litteral_annot list

exception CONFLICT of litteral list * clause list
exception UNSAT

let rec find e = function
    | [] -> false
    | h::t -> h = e || find e t

let rec help_append_list l1 l2 =
    match l1 with
    | [] -> l2
    | h::t -> if find h l2 then help_append_list t l2
              else help_append_list t (h::l2)

let append_list x y = help_append_list x (help_append_list y [])

let is_unitaire c =
  match c.litterals with _::[] -> true | _ -> false

let assume clauses =
  let (un,cl) = 
    List.partition
      (fun cl ->
	is_unitaire cl
      ) clauses in
  let un =
    List.rev_map
      (fun uc ->
	{litteral=(List.hd uc.litterals);dependencies=uc.causes}
      ) un in
  (un,cl)

let conflict_causes clauses =
  (List.find
    (fun cl ->
      cl.litterals = []
    ) clauses).causes

let get_litt clauses =
  let litt = List.hd (List.hd clauses).litterals in
  {litteral=litt;dependencies=[litt]}

let rec bcp clauses inter =
  let clauses = 
    List.fold_left
      (fun cls l ->
	let cls = List.filter
	  (fun c ->
	    not (List.exists
	      (fun a ->
		a.d = l.litteral.d && a.value = l.litteral.value
	      ) c.litterals)
	  ) cls in 
	List.rev_map
	  (fun cl ->
	    let litt = List.filter
	      (fun a ->
		a.d <> l.litteral.d || a.value = l.litteral.value
	      ) cl.litterals in
	    if(litt <> cl.litterals) then
	      {litterals=litt;causes=(append_list l.dependencies cl.causes)}
	    else
	      cl) cls
      ) clauses inter in
  let (un,clauses) = assume clauses in
  if(un = []) then
    ([],clauses)
  else
    let (i,c) = bcp clauses un in
    ((un@i),c)

let shift litteral conflict = 
  let rec shift_aux litt conflict acc =
    match conflict with
    | [] -> acc
    | h::t -> 
      if (List.exists (fun l -> l = litt.litteral) h.causes) then
	let causes = List.filter (fun l -> not(l = litt.litteral)) h.causes in
	let litts = {litt.litteral with value=(not litt.litteral.value)}::h.litterals in
	shift_aux litt t ({litterals=litts;causes=causes}::acc)
      else 
	shift_aux litt t (h::acc) in
  shift_aux litteral conflict []

let rec dpll clauses sh inter running =
  if(clauses = []) then
    append_list inter running
  else
    try
      raise (CONFLICT ((conflict_causes clauses),sh))
    with Not_found ->
      let (i,clauses) = bcp clauses running in
      let inter = i@inter in
      try
	let litt = get_litt clauses in
	try
	  dpll clauses sh (litt::inter) [litt]
	with CONFLICT (causes,sh) ->
	  let conflict_clauses = shift litt sh in 
	  if(List.exists (fun c -> c = litt.litteral) causes) then
	    let dep = List.filter (fun c -> not(c = litt.litteral)) causes in
	    let not_litt = {litteral={litt.litteral with value=(not(litt.litteral.value))};dependencies=dep} in
	    let new_conflict = {litterals=[not_litt.litteral];causes=dep} in
	    let conflict_clauses = append_list conflict_clauses [new_conflict] in
	    dpll clauses conflict_clauses (not_litt::inter) [not_litt]
	  else
	    raise (CONFLICT (causes, conflict_clauses))
      with Failure "hd" -> dpll clauses sh inter running

let remove_tautology clauses =
  List.filter
   (fun cl ->
      List.exists
       (fun l ->
           List.for_all
             (fun a ->
                l.d <> a.d || l = a
             ) cl.litterals
       ) cl.litterals
   ) clauses

let resolve fnc =
  let (un,cl) = assume fnc in
  let cl = remove_tautology cl in
  try
    dpll cl [] un un
  with CONFLICT _ -> raise UNSAT
