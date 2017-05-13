module Hello


type filename = string

(* canWrite is a function specifying whether or not a file f can be written *)
val canWrite : filename -> Tot bool
let canWrite f = 
  match f with 
    | "demo/tempfile" -> true
    | _ -> false

(* canRead is also a function ... *)
val canRead : filename -> Tot bool
let canRead f = 
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is this file *)

val read  : f:filename{canRead f}  -> ML string
let read f  = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

val write : f:filename{canWrite f} -> string -> ML unit
let write f s = FStar.IO.print_string ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")

let passwd  = "demo/password"
let readme  = "demo/README"
let tmp     = "demo/tempfile"

val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (* let v3 = read passwd in -- invalid read, fails type-checking *)
  write tmp "hello!"
  (* ; write passwd "junk" -- invalid write , fails type-checking *)

exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead


val checkedWrite : filename -> string -> ML unit

exception InvalidWrite
let checkedWrite f s =
  if canWrite f then write f s else raise InvalidWrite

let dynamicChecking () =
  let v1 = checkedRead tmp in
  let v2 = checkedRead readme in
  let v3 = checkedRead passwd in (* this raises exception *)
  checkedWrite tmp "hello!";
  checkedWrite passwd "junk" (* this raises exception *)

let nonZero (n:int) = n = 0

val div : int -> b:int{nonZero b} -> ML int
let div a b = a + b 

//let main = staticChecking () (*; dynamicChecking () *)

val new_counter: int -> ML (unit -> ML int)
let new_counter init =
  let c = ST.alloc init in
  fun () -> c := !c + 1; !c


//Statically checked assertions


let max a b = if a > b then a else b

let a = assert (max 0 1 = 1)

let b = assert (forall x y. 
		  max x y >= x 
		  && max x y >= y 
		  && (max x y = x || max x y = y))

let mul a b = a * b

type nat =x:int{x>=0}

val fib: nat -> nat
let rec fib x = 
  if x <= 1 then 1 
  else fib (x-1) + fib (x-2)


//lemmas
//GTot = ghost total function

//assert(forall x. fib x > 0)
val fib_is_possitive: x:nat -> Lemma(fib x>0)
//val fib_is_possitive: x:nat -> GTot(u:unit{fib x>0})
let rec fib_is_possitive x =
  match x with
  | 0 -> ()
  | _ -> fib_is_possitive (x-1)


val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibonacci_greater_than_arg n =
  match n with
  | 2 -> () 
  | _ -> admit() //f* can prove the lemma automatically
  //| _ -> fibonacci_greater_than_arg (n-1) //manual lemma proving


type list2 'a =
| Nil : list2 'a
| Cons : hd: 'a -> tl: list2 'a -> list2 'a

val append: list 'a -> list 'a -> Tot(list 'a)
let rec append l1 l2 = match l1 with
| [] -> l2
| hd::tl -> hd :: append tl l2

val length : list 'a -> nat
let rec length l = match l with
  | [] -> 0
  | _::tl -> 1 + length tl

val append_len : l1 : list 'a -> l2 : list 'a 
	       -> Lemma (requires True)
                       (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_len l1 l2 = match l1 with
| [] -> ()
| _::tl -> append_len tl l2

val mem: #t:Type{hasEq t} -> t -> list t -> Tot bool
let rec mem #t a l = match l with
| [] -> false
| hd::tl -> hd = a || mem a tl


val append_mem:  #t:Type{hasEq t} -> l1:list t -> l2:list t -> a:t
        -> Lemma (ensures (mem a (append l1 l2) <==>  mem a l1 || mem a l2))
let rec append_mem #t l1 l2 a =
  match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

//4.2. To type intrinsically, or to prove lemmas?

val reverse: list 'a -> Tot (list 'a)
let rec reverse l = match l with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]


type option 'a =
  | None : option 'a
  | Some : v:'a -> option 'a

(* The intrinsic style is more convenient in this case *)
val find : f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl


val nth: l: list 'a -> n: nat{length l > n} -> 'a
let rec nth l n = match l with
| hd::tl -> if n > 0 then nth tl (n - 1)
	  else hd

val take: l: list 'a -> n: nat{length l > n && n > 0} -> r:list 'a
let rec take l n = match l with
| hd::tl -> if n > 1 then hd :: take tl (n - 1)
	  else [hd]

val take_has_correct_length : l:list 'a -> n: nat{length l > n && n > 0} 
			      -> Lemma (ensures (length(take l n)) = n)
let rec take_has_correct_length l n = match l with
| hd::tl -> if n > 1 then take_has_correct_length tl (n-1)
	  else ()

