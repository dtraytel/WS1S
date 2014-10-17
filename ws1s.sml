(* Author: Dmitriy Traytel *)

(* Misc list functions *)
fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);
fun fold_rev _ [] y = y
  | fold_rev f (x :: xs) y = f x (fold_rev f xs y);
fun foldr1 _ [] = raise List.Empty
  | foldr1 f l =
      let fun itr [] = raise List.Empty
            | itr [x] = x
            | itr (x :: l) = f(x, itr l)
      in  itr l  end;
fun nth xs i = List.nth (xs, i);
fun member eq list x =
  let
    fun memb [] = false
      | memb (y :: ys) = eq (x, y) orelse memb ys;
  in memb list end;
fun insert eq x xs = if member eq xs x then xs else x :: xs;
fun remove eq x xs = if member eq xs x then List.filter (fn y => not (eq (x, y))) xs else xs;
fun union eq = fold (insert eq);
fun replicate (n: int) x =
  let fun rep (0, xs) = xs
        | rep (n, xs) = rep (n - 1, x :: xs)
  in
    if n < 0 then raise Subscript
    else rep (n, [])
  end;
fun map_product _ _ [] = []
  | map_product _ [] _ = []
  | map_product f (x :: xs) ys = map (f x) ys @ map_product f xs ys;
fun take (0: int) _ = []
  | take _ [] = []
  | take n (x :: xs) = x :: take (n - 1) xs;
fun drop (0: int) xs = xs
  | drop _ [] = []
  | drop n (_ :: xs) = drop (n - 1) xs;
infix 4 upto
fun ((i: int) upto j) =
  if i > j then [] else i :: (i + 1 upto j);

(* The decision procedure *)
structure WS1S = struct

datatype kind = FO | SO;

type atom = (bool list * bool list);

datatype ws1s =
  B of bool    |
  Q of int     |
  Less of int * int | LessF of int * int | LessT of int * int |
  In of int * int   | InT of int * int   |
  Eps of ws1s |
  Or of ws1s * ws1s | Not of ws1s        |
  Ex of kind * ws1s;

fun less_kind FO SO = true
  | less_kind _ _ = false;

fun less (B b1) (B b2) = not b1 andalso b2
  | less (B _) _ = true
  | less _ (B _) = false
  | less (Q i1) (Q i2) = i1 < i2
  | less (Q _) _ = true
  | less _ (Q _) = false
  | less (Less (i1, j1)) (Less (i2, j2)) = i1 < i2 orelse (i1 = i2 andalso j1 < j2) 
  | less (Less _) _ = true
  | less _ (Less _) = false
  | less (LessF (i1, j1)) (LessF (i2, j2)) = i1 < i2 orelse (i1 = i2 andalso j1 < j2) 
  | less (LessF _) _ = true
  | less _ (LessF _) = false
  | less (LessT (i1, j1)) (LessT (i2, j2)) = i1 < i2 orelse (i1 = i2 andalso j1 < j2) 
  | less (LessT _) _ = true
  | less _ (LessT _) = false
  | less (In (i1, j1)) (In (i2, j2)) = i1 < i2 orelse (i1 = i2 andalso j1 < j2) 
  | less (In _) _ = true
  | less _ (In _) = false
  | less (InT (i1, j1)) (InT (i2, j2)) = i1 < i2 orelse (i1 = i2 andalso j1 < j2) 
  | less (InT _) _ = true
  | less _ (InT _) = false
  | less (Eps f) (Eps g) = less f g
  | less (Eps _) _ = true
  | less _ (Eps _) = false
  | less (Or (f1, g1)) (Or (f2, g2)) = less f1 f2 orelse (f1 = f2 andalso less g1 g2) 
  | less (Or _) _ = true
  | less _ (Or _) = false
  | less (Not f) (Not g) = less f g
  | less (Not _) _ = true
  | less _ (Not _) = false
  | less (Ex (k1, f1)) (Ex (k2, f2)) = less_kind k1 k2 orelse (k1 = k2 andalso less f1 f2);

fun suc FO (m, n) = (m + 1, n)
  | suc SO (m, n) = (m, n + 1);

fun extend FO b (bs1, bs2) = (b :: bs1, bs2)
  | extend SO b (bs1, bs2) = (bs1, b :: bs2);

fun find FO l (Q i) = i = l
  | find FO l (Less (i, j)) = i = l orelse j = l
  | find FO l (LessF (i, j)) = i = l orelse j = l
  | find FO l (LessT (i, j)) = i = l orelse j = l
  | find FO l (In (i, _)) = i = l
  | find SO l (In (_, j)) = j = l
  | find FO l (InT (i, _)) = i = l
  | find SO l (InT (_, j)) = j = l
  | find k l (Eps f) = find k l f
  | find k l (Not f) = find k l f
  | find k l (Or (f, g)) = (find k l f orelse find k l g)
  | find k l (Ex (k', f)) = find k (if k = k' then l + 1 else l) f
  | find _ _ _ = false;

fun fov (Q i) = [i]
  | fov (Less (i, j)) = [i, j]
  | fov (LessF (i, j)) = [i, j]
  | fov (LessT (i, j)) = [i, j]
  | fov (In (i, _)) = [i]
  | fov (InT (i, _)) = [i]
  | fov (Eps f) = fov f
  | fov (Not f) = fov f
  | fov (Or (f, g)) = union (op =) (fov f) (fov g)
  | fov (Ex (FO, f)) = map (fn x => x - 1) (remove (op =) 0 (fov f))
  | fov (Ex (SO, f)) = fov f
  | fov _ = [];

fun dec l i = (if i > l then i - 1 else i);

fun decr FO l (Q i) = Q (dec l i) 
  | decr FO l (Less (i, j)) = Less (dec l i, dec l j)
  | decr FO l (LessF (i, j)) = LessF (dec l i, dec l j)
  | decr FO l (LessT (i, j)) = LessT (dec l i, dec l j)
  | decr FO l (In (i, j)) = In (dec l i, j)
  | decr SO l (In (i, j)) = In (i, dec l j)
  | decr FO l (InT (i, j)) = InT (dec l i, j)
  | decr SO l (InT (i, j)) = InT (i, dec l j)
  | decr k l (Eps f) = Eps (decr k l f)
  | decr k l (Not f) = Not (decr k l f)
  | decr k l (Or (f, g)) = Or (decr k l f, decr k l g)
  | decr k l (Ex (k', f)) = Ex (k', decr k (if k = k' then l + 1 else l) f)
  | decr _ _ f = f;

fun nOr (B b1) (B b2) = B (b1 orelse b2)
  | nOr (B b) g = (if b then B true else g)
  | nOr f (B b) = (if b then B true else f)
  | nOr (Or (f1, f2)) g = nOr f1 (nOr f2 g)
  | nOr f (Or (g1, g2)) =
      (if f = g1 then Or (g1, g2)
      else if less f g1 then Or (f, Or (g1, g2))
      else Or (g1, nOr f g2))
  | nOr f g =
      (if f = g then f
      else if less f g then Or (f, g)
      else Or (g, f));

fun nNot (Not f) = f
  | nNot (B b) = B (not b)
  | nNot f = Not f;

fun inc l i = (if l <= i then i + 1 else i);

fun incr FO l (Q i) = Q (inc l i) 
  | incr FO l (Less (i, j)) = Less (inc l i, inc l j)
  | incr FO l (LessF (i, j)) = LessF (inc l i, inc l j)
  | incr FO l (LessT (i, j)) = LessT (inc l i, inc l j)
  | incr FO l (In (i, j)) = In (inc l i, j)
  | incr SO l (In (i, j)) = In (i, inc l j)
  | incr FO l (InT (i, j)) = InT (inc l i, j)
  | incr SO l (InT (i, j)) = InT (i, inc l j)
  | incr k l (Not f) = Not (incr k l f)
  | incr k l (Or (f, g)) = Or (incr k l f, incr k l g)
  | incr k l (Ex (k', f)) = Ex (k', incr k (if k = k' then l + 1 else l) f)
  | incr _ _ f = f;

fun nEx k (Or (f, g)) = nOr (nEx k f) (nEx k g)
  | nEx k f = (if find k 0 f then Ex (k, f) else decr k 0 f);

fun norm (Or (f, g)) = nOr (norm f) (norm g)
  | norm (Not f) = nNot (norm f)
  | norm (Eps f) = Eps (norm f)
  | norm (Ex (k, f)) = nEx k (norm f)
  | norm f = f;

fun deriv (bs1, _) (Q i) = if nth bs1 i then B true else Q i
  | deriv (bs1, _) (Less (i, j)) =
      (case (nth bs1 i, nth bs1 j) of
        (false, false) => Less (i, j)
      | (true, false) => Q j
      | _ => B false)
  | deriv (bs1, _) (LessF (i, j)) =
      (case (nth bs1 i, nth bs1 j) of
        (false, false) => LessF (i, j)
      | (true, false) => B true
      | _ => B false)
  | deriv (bs1, _) (LessT (i, j)) =
      (case (nth bs1 i, nth bs1 j) of
        (false, false) => LessT (i, j)
      | (true, false) => B true
      | _ => B false)
  | deriv (bs1, bs2) (In (i, j)) =
      (case (nth bs1 i, nth bs2 j) of
        (false, _) => In (i, j)
      | (true, true) => B true
      | _ => B false)
  | deriv (bs1, bs2) (InT (i, j)) =
      (case (nth bs1 i, nth bs2 j) of
        (false, _) => InT (i, j)
      | (true, true) => B true
      | _ => B false)
  | deriv x (Or (f, g)) = nOr (deriv x f) (deriv x g)
  | deriv x (Eps f) = deriv x f
  | deriv x (Not f) = nNot (deriv x f)
  | deriv x (Ex (k, f)) = nEx k (nOr (deriv (extend k true x) f) (deriv (extend k false x) f))
  | deriv _ b = b;

fun derivs [] f = f
  | derivs (x :: xs) f = derivs xs (deriv x f);

fun nullable (B b) = b
  | nullable (Q _) = false
  | nullable (Less _) = false
  | nullable (LessF _) = false
  | nullable (LessT _) = true
  | nullable (In _) = false
  | nullable (InT _) = true
  | nullable (Or (f, g)) = nullable f orelse nullable g
  | nullable (Not f) = not (nullable f)
  | nullable (Eps _) = true
  | nullable (Ex (_, f)) = nullable f

fun rderiv (bs1, _) (Q i) = if nth bs1 i then B true else Q i
  | rderiv (bs1, _) (Less (i, j)) =
      (case nth bs1 j of
        false => Less (i, j)
      | true => LessF (i, j))
  | rderiv (bs1, _) (LessF (i, j)) =
      (case (nth bs1 i, nth bs1 j) of
        (true, false) => LessT (i, j)
      | _ => LessF (i, j))
  | rderiv (bs1, _) (LessT (i, j)) =
      (case nth bs1 j of
        false => LessT (i, j)
      | true => LessF (i, j))
  | rderiv (bs1, bs2) (In (i, j)) =
      (case (nth bs1 i, nth bs2 j) of
        (true, true) => InT (i, j)
      | _ => In (i, j))
  | rderiv (bs1, bs2) (InT (i, j)) =
      (case (nth bs1 i, nth bs2 j) of
        (true, false) => In (i, j)
      | _ => InT (i, j))
  | rderiv x (Or (f, g)) = nOr (rderiv x f) (rderiv x g)
  | rderiv x (Eps f) = rderiv x f
  | rderiv x (Not f) = nNot (rderiv x f)
  | rderiv x (Ex (k, f)) = nEx k (nOr (rderiv (extend k true x) f) (rderiv (extend k false x) f))
  | rderiv _ b = b;

fun futurize (m, n) f =
  let
    fun go f xs =
      if member (op =) xs f then foldr1 (fn (f, g) => nOr f g) xs
      else go (rderiv (replicate m false, replicate n false) f) (f :: xs);
  in go f [] end;

fun finalize mn (Ex (k, f)) = futurize mn (nEx k (finalize (suc k mn) f))
  | finalize mn (Or (f, g)) = nOr (finalize mn f) (finalize mn g)
  | finalize mn (Eps f) = Eps (finalize mn f)
  | finalize mn (Not f) = nNot (finalize mn f)
  | finalize _ f = f;

fun final mn f = nullable (finalize mn f);

fun nAnd f g = nNot (nOr (nNot f) (nNot g));
fun nAll k f = nNot (nEx k (nNot f));
fun And (f, g) = Not (Or (Not f, Not g));
fun All (k, f) = Not (Ex (k, Not f));

fun restrict f =
  let
    fun restr (Or (f, g)) = nOr (restr f) (restr g)
      | restr (Not f) = nNot (restr f)
      | restr (Eps f) = Eps (restr f)
      | restr (Ex (FO, f)) = nEx FO (nAnd (restr f) (Q 0))
      | restr (Ex (SO, f)) = nEx SO (restr f)
      | restr f = f;
  in fold (fn i => fn f => nAnd f (Q i)) (fov f) (restr f) end;

fun bitvectors 0 = [[]]
  | bitvectors n =
    let
      val bv = bitvectors (n - 1);
    in
      List.concat (map (fn xs => [true :: xs, false :: xs]) bv)
    end;

fun bisim alphs init delta obs s t =
  let
    val s0 = init s;
    val t0 = init t;
    fun closure [] _ = true
      | closure ((s, t) :: ws) P =
          if obs s = obs t then
            let
              fun add_new a (ws, P) =
                let val st = (delta a s, delta a t)
                in if member (op =) P st orelse (op =) st then (ws, P) else (st :: ws, st :: P) end;
              val (ws', P') = fold add_new alphs (ws, P);
            in closure ws' P' end
          else false;
  in closure [(s0, t0)] [(s0, t0)] end;

fun mk_alph (m, n) = map_product (fn a => fn b => (a, b)) (bitvectors m) (bitvectors n)

fun eqv_m2l mn = bisim (mk_alph mn) restrict deriv nullable;
fun eqv mn = bisim (mk_alph mn) restrict deriv (final mn);

val valid_m2l = eqv_m2l (0, 0) (B true) o Eps;
val invalid_m2l = eqv_m2l (0, 0) (Eps (B false)) o Eps;
val valid = eqv (0, 0) (B true);
val invalid = eqv (0, 0) (B false);

end;

(* Some tests *)
local
  open WS1S;
in

val tt =
    [ All (FO, Ex (FO, Less (1, 0)))
    , Ex (FO, Ex (FO, Less (1, 0)))
    , Ex (FO, Ex (FO, And (Less (1, 0), Less (1, 0))))
    , Ex (FO, Ex (FO, And (Less (0, 1), Less (0, 1))))
    , All (FO, Ex (FO, And (Less (1, 0), Less (1, 0))))
    , Ex (FO, Ex (FO, Not (Or (Not (Less (1, 0)), Not (Less (1, 0))))))
    , Ex (FO, Ex (FO, Ex (FO, And (Less (0, 1), Or (Less (1, 2), Less (2, 0))))))
    , All (FO, Ex (FO, Or (Less (0, 1), Less (1, 0))))]

val xx =
    [ Ex (FO, Less (0, 0))
    , All (FO, Less (0, 0))
    , Ex (FO, Ex (FO, Less (0, 1)))
    , Ex (FO, All (FO, Less (0, 1)))
    , All (FO, Ex (FO, Less (0, 1)))
    , All (FO, All (FO, Less (0, 1)))
    , Ex (FO, Ex (FO, Less (1, 0)))
    , Ex (FO, All (FO, Less (1, 0)))
    , All (FO, Ex (FO, Less (1, 0)))
    , All (FO, All (FO, Less (1, 0)))]

val yy =
    [ Ex (SO, Ex (FO, In (0, 0)))
    , Ex (SO, All (FO, In (0, 0)))
    , All (SO, Ex (FO, In (0, 0)))
    , All (SO, All (FO, In (0, 0)))
    , Ex (FO, Ex (SO, In (0, 0)))
    , Ex (FO, All (SO, In (0, 0)))
    , All (FO, Ex (SO, In (0, 0)))
    , All (FO, All (SO, In (0, 0)))]

val ft =
    [ All (FO, Ex (FO, Less (0, 1)))
    , Ex (FO, Less (0, 0))
    , Ex (FO, Ex (FO, And (Less (0, 1), Less (1, 0))))
    , Ex (FO, Ex (FO, Ex (FO, And (Less (0, 1), And (Less (1, 2), Less (2, 0))))))
    , Ex (FO, Ex (FO, Not (Or (Not (Less (0, 1)), Not (Less (1, 0))))))
    , All (FO, All (FO, Or (Less (0, 1), Less (1, 0))))
    , All (FO, All (FO, And (Less (0, 1), Less (1, 0))))]

fun test_true [] ts = List.all invalid ts 
  | test_true (x :: xs) ts =
      List.all invalid (take x ts) andalso valid (nth ts x) andalso
      test_true (map (fn i => i - x - 1) xs) (drop (x + 1) ts);

fun test () =
  List.all valid tt andalso
  List.all invalid ft andalso
  test_true [2,6,8] xx andalso
  test_true [0,4,6] yy;

fun Imp (f, g) = Or (Not f, g)

fun Globally P n = All (FO, Imp (Not (Less (n+1, 0)), P 0));
fun Future P n = Ex (FO, And (Not (Less (n+1, 0)), P 0));
fun IMP P1 P2 n = Imp (P1 n, P2 n);
fun PSI n = All (FO, (IMP
     (Globally (fold_rev (fn i => fn phi => IMP (fn m => In (m, i)) phi) (0 upto n - 1)
       (fn m => In (m, n))))
     (fold_rev (fn i => fn phi => IMP (Globally (fn m => In (m, i))) phi) (0 upto n - 1)
       (Globally (fn m => In (m, n))))) 0);

fun psi_test_m2l n = eqv_m2l (0, n + 1) (B true) (PSI n);
fun psi_test n = eqv (0, n + 1) (B true) (PSI n);

fun main () =
  if
    eqv_m2l (1, 0) (Ex (SO, In (0, 0))) (Not (Less (0, 0))) andalso
    eqv (1, 0) (Ex (SO, In (0, 0))) (Not (Less (0, 0))) andalso
    test () andalso
    List.all psi_test_m2l (0 upto 15) andalso
    List.all psi_test (0 upto 15) andalso
    invalid (Ex (SO, All (FO, In (0, 0)))) andalso
    valid_m2l (Ex (SO, All (FO, In (0, 0)))) andalso
    valid (All (FO, Ex (FO, Less (1, 0)))) andalso
    invalid_m2l (All (FO, Ex (FO, Less (1, 0))))
  then print "ok\n"
  else print "error\n"

end;
