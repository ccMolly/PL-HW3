(* ========== Getting Started with ML ==========*)
(* 1 *)
fun reverse x = foldl (op::) nil x;

(* 2 *)
fun composelist x nil = x
	| composelist x (h::t) = composelist (h x) t;

(* 3 *)
exception Badform;
fun foldmod f nil = raise Badform
	| foldmod f (h::nil) = h
	| foldmod f (h::t) = (f h) (foldmod f t);

(* 4 *)
exception Mismatch;
fun zip (nil,nil) = nil
	| zip ((h::t),nil) = raise Mismatch
	| zip (nil,(m::n)) = raise Mismatch
	| zip ((h::t),(m::n)) = if (length t) = (length n) then [(h,m)] @ (zip (t,n))
	else raise Mismatch;

(* 5 *)
fun unzip x = case x of nil => (nil, nil)
    | (a,b)::t => let val (m, n) = unzip t
    in (a :: m, b :: n) end;

(* 6 *)
fun bind NONE _ f = NONE
	| bind _ NONE f = NONE
	| bind a b f = SOME (f (valOf a) (valOf b));

(* 7 *)
fun getitem a nil = NONE
	| getitem 1 (h::t) = SOME h
	| getitem a (h::t) = getitem (a-1) t;

(* 8 *)
fun getitem2 NONE _ = NONE
	| getitem2 _ nil = NONE
	| getitem2 (SOME 1) (h::t) = SOME h
	| getitem2 a (h::t) = getitem2 (SOME ((valOf a) - 1)) t;

(* ========== Multi-Level Priority Queue in ML ==========*)
signature MLQPARAM = sig
       type element;
       val max : int;
end;

functor MakeQ(MLQ:MLQPARAM):
	sig
		type 'a mlqueue
		val maxlevel : int
		val new: MLQ.element mlqueue
		val enqueue : MLQ.element mlqueue -> int -> int -> MLQ.element -> MLQ.element mlqueue
		val dequeue : MLQ.element mlqueue -> MLQ.element * MLQ.element mlqueue
		val move : (MLQ.element -> bool) -> MLQ.element mlqueue -> MLQ.element mlqueue
		val atlevel : MLQ.element mlqueue -> int -> (int * MLQ.element) list
		val lookup : (MLQ.element -> bool) -> MLQ.element mlqueue -> int * int
		val isempty : MLQ.element mlqueue -> bool
		val flatten : MLQ.element mlqueue -> MLQ.element list
    end
	=
	struct
		open MLQ

		exception Overflow
		exception Empty
		exception LevelNoExist
		exception NotFound

		datatype 'a mlqueue = Q of (int * int * 'a) list;
		val maxlevel = MLQ.max;
		val new = Q nil;

		fun enqueue (Q q) l p e = 
		let 
			fun enqueue0 [] (new as (l, p, e)) = if l < 0 then raise LevelNoExist else if l > maxlevel then raise LevelNoExist else [new]
				| enqueue0 (old as (l0, p0, e0) :: t) (new as (l, p, e)) =
				if l > maxlevel then raise LevelNoExist else
				if l0 >= l andalso p0 > p then new :: old else if  l0 = l andalso p0 = p then [(l0, p0, e0), new] @ t else
				(l0,p0,e0) :: (enqueue0 t (l, p, e))
		in
			Q (enqueue0 q (l, p, e))
		end

		fun dequeue (Q (nil)) = raise Empty
			| dequeue (Q ((l,p,e)::t)) = (e, (Q (t)))

		fun move pred (Q (nil)) = raise Empty
			| move pred (Q ((l,p,e)::t)) = 
			let
				fun iter(li, (trueList,falseList)) = 
					case li of
					[] => (List.rev trueList, List.rev falseList)
					| ((l0,p0,e0)::t0) => if pred e0 andalso l0<maxlevel
									then iter(t0, ((l0,p0,e0)::trueList,falseList))
									else iter(t0, (trueList,(l0,p0,e0)::falseList))

				fun move0 ([],(Q n)) = (Q n)
					| move0 ((l1,p1,e1)::t1,(Q n)) = move0 (t1, enqueue (Q n) (l1+1) p1 e1)
			in
				let
					val (a,b) = iter((l,p,e)::t,([],[]))
				in
					move0 (a, (Q b))
				end
			end

		fun atlevel (Q q) n =
			let 
				fun atlevel0 nil m = if m>maxlevel then raise LevelNoExist else nil
					| atlevel0 (old as (l0,p0,e0)::t0) m = if m>maxlevel then raise LevelNoExist else if l0 = m then (p0,e0)::(atlevel0 t0 m) else (atlevel0 t0 m);
					
			in
				atlevel0 q n
			end

		fun lookup pred (Q (nil)) = raise NotFound
			| lookup pred (Q ((l,p,e)::t)) = if (pred e) then (l,p) else lookup pred (Q (t))

		fun isempty (Q (nil)) = true
			| isempty (Q ((l,p,e)::t)) = false

		fun flatten (Q nil) = []
			| flatten (Q ((l,p,e)::t)) = e::(flatten (Q t))
		
	end;

structure Q = MakeQ(type element = int; val max = 2);
val q = Q.new;
val q = Q.enqueue q 1 1 2;
val q = Q.enqueue q 0 0 3;
val q = Q.enqueue q 2 0 5;
val q = Q.enqueue q 2 2 1;
val q = Q.enqueue q 1 0 4;
val q = Q.enqueue q 2 1 6;
val q = Q.enqueue q 3 1 6;
val q = Q.move (fn e => e>3) q;
val (e1,q) = Q.dequeue q;
val (e2,q) = Q.dequeue q;
Q.atlevel q 1;
Q.lookup (fn e => e<5) q;
