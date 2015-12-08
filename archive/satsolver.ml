type litteral = {d:int;value:bool}
type clause = litteral list
type fnc = clause list
type interpretation = litteral list

exception UNSAT

let is_unitaire clause = match clause with | _::[] -> true | _ -> false

let assume clauses =
  let (un,ot) = List.partition
    (fun c -> is_unitaire c) clauses in
  (List.flatten un, ot)

let conflict clauses = 
  List.exists
    (fun c ->
      match c with [] -> true | _ -> false
    ) clauses

let get_litt clauses =
 List.hd (List.hd clauses)

let rec bcp clauses inter =
  let clauses = 
    List.fold_left
      (fun cls i ->
	let cls = 
	  List.filter
	    (fun clause ->
	      not(
		List.exists
		  (fun atome ->
		    atome = i
		  ) clause)
	    ) cls in
	List.rev_map
	  (fun clause ->
	    List.filter
	      (fun atome ->
		(i.d <> atome.d)
	      ) clause
	  ) cls 
      ) clauses inter in
  let (un,clauses) = assume clauses in
  if(un <> []) then
    let (i,c) = bcp clauses un in
    ((un@i),c)
  else
    ([],clauses)
      
      
let rec dpll clauses inter running =
  if(clauses = []) then
    inter@running
  else if(conflict clauses) then
    raise UNSAT
  else
    let (i,clauses) = bcp clauses running in
    let inter = i@inter in
    try
      let litt = get_litt clauses in
      try
	dpll clauses (litt::inter) [litt]
      with UNSAT -> dpll clauses ({litt with value=(not(litt.value))}::inter) [{litt with value=(not(litt.value))}]
    with Failure "hd" -> dpll clauses inter running
      
let resolve fnc =
  let (un,cl) = assume fnc in
  dpll cl un un
