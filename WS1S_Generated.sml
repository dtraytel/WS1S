structure WS1S_Generated : sig
  type ws1s
  type order
  type ('a, 'b) aformula
  type 'a set
  type idx
  val check_eqv :
    idx -> (ws1s, order) aformula -> (ws1s, order) aformula -> bool
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype ws1s = Q of nat | Less of nat * nat | LessF of nat * nat |
  LessT of nat * nat | In of nat * nat | InT of nat * nat;

fun equal_ws1sa (In (x51, x52)) (InT (x61, x62)) = false
  | equal_ws1sa (InT (x61, x62)) (In (x51, x52)) = false
  | equal_ws1sa (LessT (x41, x42)) (InT (x61, x62)) = false
  | equal_ws1sa (InT (x61, x62)) (LessT (x41, x42)) = false
  | equal_ws1sa (LessT (x41, x42)) (In (x51, x52)) = false
  | equal_ws1sa (In (x51, x52)) (LessT (x41, x42)) = false
  | equal_ws1sa (LessF (x31, x32)) (InT (x61, x62)) = false
  | equal_ws1sa (InT (x61, x62)) (LessF (x31, x32)) = false
  | equal_ws1sa (LessF (x31, x32)) (In (x51, x52)) = false
  | equal_ws1sa (In (x51, x52)) (LessF (x31, x32)) = false
  | equal_ws1sa (LessF (x31, x32)) (LessT (x41, x42)) = false
  | equal_ws1sa (LessT (x41, x42)) (LessF (x31, x32)) = false
  | equal_ws1sa (Less (x21, x22)) (InT (x61, x62)) = false
  | equal_ws1sa (InT (x61, x62)) (Less (x21, x22)) = false
  | equal_ws1sa (Less (x21, x22)) (In (x51, x52)) = false
  | equal_ws1sa (In (x51, x52)) (Less (x21, x22)) = false
  | equal_ws1sa (Less (x21, x22)) (LessT (x41, x42)) = false
  | equal_ws1sa (LessT (x41, x42)) (Less (x21, x22)) = false
  | equal_ws1sa (Less (x21, x22)) (LessF (x31, x32)) = false
  | equal_ws1sa (LessF (x31, x32)) (Less (x21, x22)) = false
  | equal_ws1sa (Q x1) (InT (x61, x62)) = false
  | equal_ws1sa (InT (x61, x62)) (Q x1) = false
  | equal_ws1sa (Q x1) (In (x51, x52)) = false
  | equal_ws1sa (In (x51, x52)) (Q x1) = false
  | equal_ws1sa (Q x1) (LessT (x41, x42)) = false
  | equal_ws1sa (LessT (x41, x42)) (Q x1) = false
  | equal_ws1sa (Q x1) (LessF (x31, x32)) = false
  | equal_ws1sa (LessF (x31, x32)) (Q x1) = false
  | equal_ws1sa (Q x1) (Less (x21, x22)) = false
  | equal_ws1sa (Less (x21, x22)) (Q x1) = false
  | equal_ws1sa (InT (x61, x62)) (InT (y61, y62)) =
    equal_nata x61 y61 andalso equal_nata x62 y62
  | equal_ws1sa (In (x51, x52)) (In (y51, y52)) =
    equal_nata x51 y51 andalso equal_nata x52 y52
  | equal_ws1sa (LessT (x41, x42)) (LessT (y41, y42)) =
    equal_nata x41 y41 andalso equal_nata x42 y42
  | equal_ws1sa (LessF (x31, x32)) (LessF (y31, y32)) =
    equal_nata x31 y31 andalso equal_nata x32 y32
  | equal_ws1sa (Less (x21, x22)) (Less (y21, y22)) =
    equal_nata x21 y21 andalso equal_nata x22 y22
  | equal_ws1sa (Q x1) (Q y1) = equal_nata x1 y1;

val equal_ws1s = {equal = equal_ws1sa} : ws1s equal;

fun rec_ws1s f1 f2 f3 f4 f5 f6 (Q x1) = f1 x1
  | rec_ws1s f1 f2 f3 f4 f5 f6 (Less (x21, x22)) = f2 x21 x22
  | rec_ws1s f1 f2 f3 f4 f5 f6 (LessF (x31, x32)) = f3 x31 x32
  | rec_ws1s f1 f2 f3 f4 f5 f6 (LessT (x41, x42)) = f4 x41 x42
  | rec_ws1s f1 f2 f3 f4 f5 f6 (In (x51, x52)) = f5 x51 x52
  | rec_ws1s f1 f2 f3 f4 f5 f6 (InT (x61, x62)) = f6 x61 x62;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun less_eq_ws1s x =
  (fn xa => fn y =>
    rec_ws1s
      (fn x_0 => fn a =>
        (case a of Q aa => less_nat x_0 aa | Less (_, _) => true
          | LessF (_, _) => true | LessT (_, _) => true | In (_, _) => true
          | InT (_, _) => true))
      (fn x_0 => fn x_1 => fn a =>
        (case a of Q _ => false
          | Less (y_0, y_1) =>
            less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
          | LessF (_, _) => true | LessT (_, _) => true | In (_, _) => true
          | InT (_, _) => true))
      (fn x_0 => fn x_1 => fn a =>
        (case a of Q _ => false | Less (_, _) => false
          | LessF (y_0, y_1) =>
            less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
          | LessT (_, _) => true | In (_, _) => true | InT (_, _) => true))
      (fn x_0 => fn x_1 => fn a =>
        (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
          | LessT (y_0, y_1) =>
            less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
          | In (_, _) => true | InT (_, _) => true))
      (fn x_0 => fn x_1 => fn a =>
        (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
          | LessT (_, _) => false
          | In (y_0, y_1) =>
            less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
          | InT (_, _) => true))
      (fn x_0 => fn x_1 => fn a =>
        (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
          | LessT (_, _) => false | In (_, _) => false
          | InT (y_0, y_1) =>
            less_nat x_0 y_0 orelse
              equal_nata x_0 y_0 andalso less_nat x_1 y_1))
      xa y orelse
      equal_ws1sa xa y)
    x;

fun less_ws1s x =
  rec_ws1s
    (fn x_0 => fn a =>
      (case a of Q aa => less_nat x_0 aa | Less (_, _) => true
        | LessF (_, _) => true | LessT (_, _) => true | In (_, _) => true
        | InT (_, _) => true))
    (fn x_0 => fn x_1 => fn a =>
      (case a of Q _ => false
        | Less (y_0, y_1) =>
          less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
        | LessF (_, _) => true | LessT (_, _) => true | In (_, _) => true
        | InT (_, _) => true))
    (fn x_0 => fn x_1 => fn a =>
      (case a of Q _ => false | Less (_, _) => false
        | LessF (y_0, y_1) =>
          less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
        | LessT (_, _) => true | In (_, _) => true | InT (_, _) => true))
    (fn x_0 => fn x_1 => fn a =>
      (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
        | LessT (y_0, y_1) =>
          less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
        | In (_, _) => true | InT (_, _) => true))
    (fn x_0 => fn x_1 => fn a =>
      (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
        | LessT (_, _) => false
        | In (y_0, y_1) =>
          less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1
        | InT (_, _) => true))
    (fn x_0 => fn x_1 => fn a =>
      (case a of Q _ => false | Less (_, _) => false | LessF (_, _) => false
        | LessT (_, _) => false | In (_, _) => false
        | InT (y_0, y_1) =>
          less_nat x_0 y_0 orelse equal_nata x_0 y_0 andalso less_nat x_1 y_1))
    x;

type 'a ord = {less_eq : 'a -> 'a -> bool, lessa : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val lessa = #lessa : 'a ord -> 'a -> 'a -> bool;

val ord_ws1s = {less_eq = less_eq_ws1s, lessa = less_ws1s} : ws1s ord;

datatype order = FO | SO;

fun equal_ordera FO SO = false
  | equal_ordera SO FO = false
  | equal_ordera SO SO = true
  | equal_ordera FO FO = true;

val equal_order = {equal = equal_ordera} : order equal;

fun rec_order f1 f2 FO = f1
  | rec_order f1 f2 SO = f2;

fun less_eq_order x =
  (fn xa => fn y =>
    rec_order (fn a => (case a of FO => false | SO => true))
      (fn a => (case a of FO => false | SO => false)) xa y orelse
      equal_ordera xa y)
    x;

fun less_order x =
  rec_order (fn a => (case a of FO => false | SO => true))
    (fn a => (case a of FO => false | SO => false)) x;

val ord_order = {less_eq = less_eq_order, lessa = less_order} : order ord;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    lessa = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

datatype ('a, 'b) aformula = FBool of bool | FBase of 'a |
  FNot of ('a, 'b) aformula | FOr of ('a, 'b) aformula * ('a, 'b) aformula |
  FAnd of ('a, 'b) aformula * ('a, 'b) aformula | FEx of 'b * ('a, 'b) aformula
  | FAll of 'b * ('a, 'b) aformula;

fun equal_aformulaa A_ B_ (FEx (x61, x62)) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FNot x3) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FNot x3) = false
  | equal_aformulaa A_ B_ (FNot x3) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FNot x3) = false
  | equal_aformulaa A_ B_ (FNot x3) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FNot x3) = false
  | equal_aformulaa A_ B_ (FNot x3) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FNot x3) = false
  | equal_aformulaa A_ B_ (FBase x2) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBase x2) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBase x2) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBase x2) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBase x2) (FNot x3) = false
  | equal_aformulaa A_ B_ (FNot x3) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBool x1) (FAll (x71, x72)) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FBool x1) = false
  | equal_aformulaa A_ B_ (FBool x1) (FEx (x61, x62)) = false
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FBool x1) = false
  | equal_aformulaa A_ B_ (FBool x1) (FAnd (x51, x52)) = false
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FBool x1) = false
  | equal_aformulaa A_ B_ (FBool x1) (FOr (x41, x42)) = false
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FBool x1) = false
  | equal_aformulaa A_ B_ (FBool x1) (FNot x3) = false
  | equal_aformulaa A_ B_ (FNot x3) (FBool x1) = false
  | equal_aformulaa A_ B_ (FBool x1) (FBase x2) = false
  | equal_aformulaa A_ B_ (FBase x2) (FBool x1) = false
  | equal_aformulaa A_ B_ (FAll (x71, x72)) (FAll (y71, y72)) =
    eq B_ x71 y71 andalso equal_aformulaa A_ B_ x72 y72
  | equal_aformulaa A_ B_ (FEx (x61, x62)) (FEx (y61, y62)) =
    eq B_ x61 y61 andalso equal_aformulaa A_ B_ x62 y62
  | equal_aformulaa A_ B_ (FAnd (x51, x52)) (FAnd (y51, y52)) =
    equal_aformulaa A_ B_ x51 y51 andalso equal_aformulaa A_ B_ x52 y52
  | equal_aformulaa A_ B_ (FOr (x41, x42)) (FOr (y41, y42)) =
    equal_aformulaa A_ B_ x41 y41 andalso equal_aformulaa A_ B_ x42 y42
  | equal_aformulaa A_ B_ (FNot x3) (FNot y3) = equal_aformulaa A_ B_ x3 y3
  | equal_aformulaa A_ B_ (FBase x2) (FBase y2) = eq A_ x2 y2
  | equal_aformulaa A_ B_ (FBool x1) (FBool y1) = equal_bool x1 y1;

fun equal_aformula A_ B_ = {equal = equal_aformulaa A_ B_} :
  ('a, 'b) aformula equal;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype idx = Abs_idx of (nat * nat);

fun id x = (fn xa => xa) x;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer 0 (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat 0;

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nat then [] else x :: take (minus_nat n one_nat) xs);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun union A_ = fold (inserta A_);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun map fi [] = []
  | map fi (x21a :: x22) = fi x21a :: map fi x22;

fun n_lists n xs =
  (if equal_nata n zero_nat then [[]]
    else maps (fn ys => map (fn y => y :: ys) xs)
           (n_lists (minus_nat n one_nat) xs));

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun remove1 A_ x [] = []
  | remove1 A_ x (y :: xs) = (if eq A_ x y then xs else y :: remove1 A_ x xs);

fun replicate n x =
  (if equal_nata n zero_nat then []
    else x :: replicate (minus_nat n one_nat) x);

fun fV0 (Q m) = [(FO, m)]
  | fV0 (Less (m1, m2)) =
    inserta (equal_prod equal_order equal_nat) (FO, m1) [(FO, m2)]
  | fV0 (LessF (m1, m2)) =
    inserta (equal_prod equal_order equal_nat) (FO, m1) [(FO, m2)]
  | fV0 (LessT (m1, m2)) =
    inserta (equal_prod equal_order equal_nat) (FO, m1) [(FO, m2)]
  | fV0 (In (ma, m)) = [(FO, ma), (SO, m)]
  | fV0 (InT (ma, m)) = [(FO, ma), (SO, m)];

fun fv (FBool uu) = []
  | fv (FBase a) = fV0 a
  | fv (FNot phi) = fv phi
  | fv (FOr (phi, psi)) =
    union (equal_prod equal_order equal_nat) (fv phi) (fv psi)
  | fv (FAnd (phi, psi)) =
    union (equal_prod equal_order equal_nat) (fv phi) (fv psi)
  | fv (FEx (k, phi)) =
    map (fn (ka, x) =>
          (ka, (if equal_ordera k ka then minus_nat x one_nat else x)))
      (remove1 (equal_prod equal_order equal_nat) (k, zero_nat) (fv phi))
  | fv (FAll (k, phi)) =
    map (fn (ka, x) =>
          (ka, (if equal_ordera k ka then minus_nat x one_nat else x)))
      (remove1 (equal_prod equal_order equal_nat) (k, zero_nat) (fv phi));

fun suca xa (Abs_idx x) =
  Abs_idx
    let
      val (m, n) = x;
    in
      (case xa of FO => (suc m, n) | SO => (m, suc n))
    end;

fun nFAND [] = FBool true
  | nFAND [x] = x
  | nFAND (x :: v :: va) = FAnd (x, nFAND (v :: va));

fun snd (x1, x2) = x2;

fun nFOR [] = FBool false
  | nFOR [x] = x
  | nFOR (x :: v :: va) = FOr (x, nFOR (v :: va));

fun rderiv0 (bs1, bs2) (Q m) = (if nth bs1 m then FBool true else FBase (Q m))
  | rderiv0 (bs1, bs2) (Less (m1, m2)) =
    (case nth bs1 m2 of true => FBase (LessF (m1, m2))
      | false => FBase (Less (m1, m2)))
  | rderiv0 (bs1, bs2) (LessF (m1, m2)) =
    (case (nth bs1 m1, nth bs1 m2) of (true, true) => FBase (LessF (m1, m2))
      | (true, false) => FBase (LessT (m1, m2))
      | (false, b) => FBase (LessF (m1, m2)))
  | rderiv0 (bs1, bs2) (LessT (m1, m2)) =
    (case nth bs1 m2 of true => FBase (LessF (m1, m2))
      | false => FBase (LessT (m1, m2)))
  | rderiv0 (bs1, bs2) (In (ma, m)) =
    (case (nth bs1 ma, nth bs2 m) of (true, true) => FBase (InT (ma, m))
      | (true, false) => FBase (In (ma, m)) | (false, b) => FBase (In (ma, m)))
  | rderiv0 (bs1, bs2) (InT (ma, m)) =
    (case (nth bs1 ma, nth bs2 m) of (true, true) => FBase (InT (ma, m))
      | (true, false) => FBase (In (ma, m))
      | (false, b) => FBase (InT (ma, m)));

fun whilea idx phi b c s = (if b s then whilea idx phi b c (c s) else s);

fun extend ord b =
  (fn (bs1, bs2) =>
    (case ord of FO => (b :: bs1, bs2) | SO => (bs1, b :: bs2)));

fun deriv deriv0 x (FBool b) = FBool b
  | deriv deriv0 x (FBase a) = deriv0 x a
  | deriv deriv0 x (FNot phi) = FNot (deriv deriv0 x phi)
  | deriv deriv0 x (FOr (phi, psi)) =
    FOr (deriv deriv0 x phi, deriv deriv0 x psi)
  | deriv deriv0 x (FAnd (phi, psi)) =
    FAnd (deriv deriv0 x phi, deriv deriv0 x psi)
  | deriv deriv0 x (FEx (k, phi)) =
    FEx (k, FOr (deriv deriv0 (extend k true x) phi,
                  deriv deriv0 (extend k false x) phi))
  | deriv deriv0 x (FAll (k, phi)) =
    FAll (k, FAnd (deriv deriv0 (extend k true x) phi,
                    deriv deriv0 (extend k false x) phi));

fun zero (Abs_idx xa) =
  let
    val (m, n) = xa;
  in
    (replicate m false, replicate n false)
  end;

fun rec_aformula f1 f2 f3 f4 f5 f6 f7 (FBool x1) = f1 x1
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FBase x2) = f2 x2
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FNot x3) =
    f3 x3 (rec_aformula f1 f2 f3 f4 f5 f6 f7 x3)
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FOr (x41, x42)) =
    f4 x41 x42 (rec_aformula f1 f2 f3 f4 f5 f6 f7 x41)
      (rec_aformula f1 f2 f3 f4 f5 f6 f7 x42)
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FAnd (x51, x52)) =
    f5 x51 x52 (rec_aformula f1 f2 f3 f4 f5 f6 f7 x51)
      (rec_aformula f1 f2 f3 f4 f5 f6 f7 x52)
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FEx (x61, x62)) =
    f6 x61 x62 (rec_aformula f1 f2 f3 f4 f5 f6 f7 x62)
  | rec_aformula f1 f2 f3 f4 f5 f6 f7 (FAll (x71, x72)) =
    f7 x71 x72 (rec_aformula f1 f2 f3 f4 f5 f6 f7 x72);

fun less_bool true b = false
  | less_bool false b = b;

fun less_aformula (A1_, A2_) (B1_, B2_) =
  rec_aformula
    (fn x_0 => fn a =>
      (case a of FBool aa => less_bool x_0 aa | FBase _ => true | FNot _ => true
        | FOr (_, _) => true | FAnd (_, _) => true | FEx (_, _) => true
        | FAll (_, _) => true))
    (fn x_0 => fn a =>
      (case a of FBool _ => false | FBase aa => lessa A2_ x_0 aa
        | FNot _ => true | FOr (_, _) => true | FAnd (_, _) => true
        | FEx (_, _) => true | FAll (_, _) => true))
    (fn _ => fn res_0 => fn a =>
      (case a of FBool _ => false | FBase _ => false | FNot aa => res_0 aa
        | FOr (_, _) => true | FAnd (_, _) => true | FEx (_, _) => true
        | FAll (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of FBool _ => false | FBase _ => false | FNot _ => false
        | FOr (y_0, y_1) =>
          res_0 y_0 orelse equal_aformulaa A1_ B1_ x_0 y_0 andalso res_1 y_1
        | FAnd (_, _) => true | FEx (_, _) => true | FAll (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn res_1 => fn a =>
      (case a of FBool _ => false | FBase _ => false | FNot _ => false
        | FOr (_, _) => false
        | FAnd (y_0, y_1) =>
          res_0 y_0 orelse equal_aformulaa A1_ B1_ x_0 y_0 andalso res_1 y_1
        | FEx (_, _) => true | FAll (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn a =>
      (case a of FBool _ => false | FBase _ => false | FNot _ => false
        | FOr (_, _) => false | FAnd (_, _) => false
        | FEx (y_0, y_1) =>
          lessa B2_ x_0 y_0 orelse eq B1_ x_0 y_0 andalso res_0 y_1
        | FAll (_, _) => true))
    (fn x_0 => fn _ => fn res_0 => fn a =>
      (case a of FBool _ => false | FBase _ => false | FNot _ => false
        | FOr (_, _) => false | FAnd (_, _) => false | FEx (_, _) => false
        | FAll (y_0, y_1) =>
          lessa B2_ x_0 y_0 orelse eq B1_ x_0 y_0 andalso res_0 y_1));

fun nFAnd (FBool b1) (FBool b2) = FBool (b1 andalso b2)
  | nFAnd (FBool b) (FBase v) = (if b then FBase v else FBool false)
  | nFAnd (FBool b) (FNot v) = (if b then FNot v else FBool false)
  | nFAnd (FBool b) (FOr (v, va)) = (if b then FOr (v, va) else FBool false)
  | nFAnd (FBool b) (FAnd (v, va)) = (if b then FAnd (v, va) else FBool false)
  | nFAnd (FBool b) (FEx (v, va)) = (if b then FEx (v, va) else FBool false)
  | nFAnd (FBool b) (FAll (v, va)) = (if b then FAll (v, va) else FBool false)
  | nFAnd (FBase v) (FBool b) = (if b then FBase v else FBool false)
  | nFAnd (FNot v) (FBool b) = (if b then FNot v else FBool false)
  | nFAnd (FOr (v, va)) (FBool b) = (if b then FOr (v, va) else FBool false)
  | nFAnd (FAnd (v, va)) (FBool b) = (if b then FAnd (v, va) else FBool false)
  | nFAnd (FEx (v, va)) (FBool b) = (if b then FEx (v, va) else FBool false)
  | nFAnd (FAll (v, va)) (FBool b) = (if b then FAll (v, va) else FBool false)
  | nFAnd (FAnd (phi_1, phi_2)) (FBase v) = nFAnd phi_1 (nFAnd phi_2 (FBase v))
  | nFAnd (FAnd (phi_1, phi_2)) (FNot v) = nFAnd phi_1 (nFAnd phi_2 (FNot v))
  | nFAnd (FAnd (phi_1, phi_2)) (FOr (v, va)) =
    nFAnd phi_1 (nFAnd phi_2 (FOr (v, va)))
  | nFAnd (FAnd (phi_1, phi_2)) (FAnd (v, va)) =
    nFAnd phi_1 (nFAnd phi_2 (FAnd (v, va)))
  | nFAnd (FAnd (phi_1, phi_2)) (FEx (v, va)) =
    nFAnd phi_1 (nFAnd phi_2 (FEx (v, va)))
  | nFAnd (FAnd (phi_1, phi_2)) (FAll (v, va)) =
    nFAnd phi_1 (nFAnd phi_2 (FAll (v, va)))
  | nFAnd (FBase v) (FAnd (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) psi_1
      then FAnd (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) psi_1
             then FAnd (FBase v, FAnd (psi_1, psi_2))
             else FAnd (psi_1, nFAnd (FBase v) psi_2)))
  | nFAnd (FNot v) (FAnd (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) psi_1
      then FAnd (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) psi_1
             then FAnd (FNot v, FAnd (psi_1, psi_2))
             else FAnd (psi_1, nFAnd (FNot v) psi_2)))
  | nFAnd (FOr (v, va)) (FAnd (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) psi_1
      then FAnd (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) psi_1
             then FAnd (FOr (v, va), FAnd (psi_1, psi_2))
             else FAnd (psi_1, nFAnd (FOr (v, va)) psi_2)))
  | nFAnd (FEx (v, va)) (FAnd (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) psi_1
      then FAnd (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) psi_1
             then FAnd (FEx (v, va), FAnd (psi_1, psi_2))
             else FAnd (psi_1, nFAnd (FEx (v, va)) psi_2)))
  | nFAnd (FAll (v, va)) (FAnd (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) psi_1
      then FAnd (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) psi_1
             then FAnd (FAll (v, va), FAnd (psi_1, psi_2))
             else FAnd (psi_1, nFAnd (FAll (v, va)) psi_2)))
  | nFAnd (FBase v) (FBase va) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FBase va) then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FBase va)
             then FAnd (FBase v, FBase va) else FAnd (FBase va, FBase v)))
  | nFAnd (FBase v) (FNot va) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FNot va) then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FNot va)
             then FAnd (FBase v, FNot va) else FAnd (FNot va, FBase v)))
  | nFAnd (FBase v) (FOr (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FOr (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FOr (va, vb))
             then FAnd (FBase v, FOr (va, vb))
             else FAnd (FOr (va, vb), FBase v)))
  | nFAnd (FBase v) (FEx (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FEx (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FEx (va, vb))
             then FAnd (FBase v, FEx (va, vb))
             else FAnd (FEx (va, vb), FBase v)))
  | nFAnd (FBase v) (FAll (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FAll (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FAll (va, vb))
             then FAnd (FBase v, FAll (va, vb))
             else FAnd (FAll (va, vb), FBase v)))
  | nFAnd (FNot v) (FBase va) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FBase va) then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FBase va)
             then FAnd (FNot v, FBase va) else FAnd (FBase va, FNot v)))
  | nFAnd (FNot v) (FNot va) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FNot va) then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FNot va)
             then FAnd (FNot v, FNot va) else FAnd (FNot va, FNot v)))
  | nFAnd (FNot v) (FOr (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FOr (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FOr (va, vb))
             then FAnd (FNot v, FOr (va, vb)) else FAnd (FOr (va, vb), FNot v)))
  | nFAnd (FNot v) (FEx (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FEx (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FEx (va, vb))
             then FAnd (FNot v, FEx (va, vb)) else FAnd (FEx (va, vb), FNot v)))
  | nFAnd (FNot v) (FAll (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FAll (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FAll (va, vb))
             then FAnd (FNot v, FAll (va, vb))
             else FAnd (FAll (va, vb), FNot v)))
  | nFAnd (FOr (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) (FBase vb)
      then FOr (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) (FBase vb)
             then FAnd (FOr (v, va), FBase vb)
             else FAnd (FBase vb, FOr (v, va))))
  | nFAnd (FOr (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) (FNot vb)
      then FOr (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) (FNot vb)
             then FAnd (FOr (v, va), FNot vb) else FAnd (FNot vb, FOr (v, va))))
  | nFAnd (FOr (v, va)) (FOr (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) (FOr (vb, vc))
      then FOr (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) (FOr (vb, vc))
             then FAnd (FOr (v, va), FOr (vb, vc))
             else FAnd (FOr (vb, vc), FOr (v, va))))
  | nFAnd (FOr (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) (FEx (vb, vc))
      then FOr (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) (FEx (vb, vc))
             then FAnd (FOr (v, va), FEx (vb, vc))
             else FAnd (FEx (vb, vc), FOr (v, va))))
  | nFAnd (FOr (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FOr (v, va)) (FAll (vb, vc))
      then FOr (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FOr (v, va)) (FAll (vb, vc))
             then FAnd (FOr (v, va), FAll (vb, vc))
             else FAnd (FAll (vb, vc), FOr (v, va))))
  | nFAnd (FEx (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FBase vb)
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FBase vb)
             then FAnd (FEx (v, va), FBase vb)
             else FAnd (FBase vb, FEx (v, va))))
  | nFAnd (FEx (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FNot vb)
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FNot vb)
             then FAnd (FEx (v, va), FNot vb) else FAnd (FNot vb, FEx (v, va))))
  | nFAnd (FEx (v, va)) (FOr (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FOr (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FOr (vb, vc))
             then FAnd (FEx (v, va), FOr (vb, vc))
             else FAnd (FOr (vb, vc), FEx (v, va))))
  | nFAnd (FEx (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FEx (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FEx (vb, vc))
             then FAnd (FEx (v, va), FEx (vb, vc))
             else FAnd (FEx (vb, vc), FEx (v, va))))
  | nFAnd (FEx (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FAll (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FAll (vb, vc))
             then FAnd (FEx (v, va), FAll (vb, vc))
             else FAnd (FAll (vb, vc), FEx (v, va))))
  | nFAnd (FAll (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FBase vb)
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FBase vb)
             then FAnd (FAll (v, va), FBase vb)
             else FAnd (FBase vb, FAll (v, va))))
  | nFAnd (FAll (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FNot vb)
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FNot vb)
             then FAnd (FAll (v, va), FNot vb)
             else FAnd (FNot vb, FAll (v, va))))
  | nFAnd (FAll (v, va)) (FOr (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FOr (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FOr (vb, vc))
             then FAnd (FAll (v, va), FOr (vb, vc))
             else FAnd (FOr (vb, vc), FAll (v, va))))
  | nFAnd (FAll (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FEx (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FEx (vb, vc))
             then FAnd (FAll (v, va), FEx (vb, vc))
             else FAnd (FEx (vb, vc), FAll (v, va))))
  | nFAnd (FAll (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FAll (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FAll (vb, vc))
             then FAnd (FAll (v, va), FAll (vb, vc))
             else FAnd (FAll (vb, vc), FAll (v, va))));

fun nFOr (FBool b1) (FBool b2) = FBool (b1 orelse b2)
  | nFOr (FBool b) (FBase v) = (if b then FBool true else FBase v)
  | nFOr (FBool b) (FNot v) = (if b then FBool true else FNot v)
  | nFOr (FBool b) (FOr (v, va)) = (if b then FBool true else FOr (v, va))
  | nFOr (FBool b) (FAnd (v, va)) = (if b then FBool true else FAnd (v, va))
  | nFOr (FBool b) (FEx (v, va)) = (if b then FBool true else FEx (v, va))
  | nFOr (FBool b) (FAll (v, va)) = (if b then FBool true else FAll (v, va))
  | nFOr (FBase v) (FBool b) = (if b then FBool true else FBase v)
  | nFOr (FNot v) (FBool b) = (if b then FBool true else FNot v)
  | nFOr (FOr (v, va)) (FBool b) = (if b then FBool true else FOr (v, va))
  | nFOr (FAnd (v, va)) (FBool b) = (if b then FBool true else FAnd (v, va))
  | nFOr (FEx (v, va)) (FBool b) = (if b then FBool true else FEx (v, va))
  | nFOr (FAll (v, va)) (FBool b) = (if b then FBool true else FAll (v, va))
  | nFOr (FOr (phi_1, phi_2)) (FBase v) = nFOr phi_1 (nFOr phi_2 (FBase v))
  | nFOr (FOr (phi_1, phi_2)) (FNot v) = nFOr phi_1 (nFOr phi_2 (FNot v))
  | nFOr (FOr (phi_1, phi_2)) (FOr (v, va)) =
    nFOr phi_1 (nFOr phi_2 (FOr (v, va)))
  | nFOr (FOr (phi_1, phi_2)) (FAnd (v, va)) =
    nFOr phi_1 (nFOr phi_2 (FAnd (v, va)))
  | nFOr (FOr (phi_1, phi_2)) (FEx (v, va)) =
    nFOr phi_1 (nFOr phi_2 (FEx (v, va)))
  | nFOr (FOr (phi_1, phi_2)) (FAll (v, va)) =
    nFOr phi_1 (nFOr phi_2 (FAll (v, va)))
  | nFOr (FBase v) (FOr (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) psi_1
      then FOr (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) psi_1
             then FOr (FBase v, FOr (psi_1, psi_2))
             else FOr (psi_1, nFOr (FBase v) psi_2)))
  | nFOr (FNot v) (FOr (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) psi_1
      then FOr (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) psi_1
             then FOr (FNot v, FOr (psi_1, psi_2))
             else FOr (psi_1, nFOr (FNot v) psi_2)))
  | nFOr (FAnd (v, va)) (FOr (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) psi_1
      then FOr (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) psi_1
             then FOr (FAnd (v, va), FOr (psi_1, psi_2))
             else FOr (psi_1, nFOr (FAnd (v, va)) psi_2)))
  | nFOr (FEx (v, va)) (FOr (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) psi_1
      then FOr (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) psi_1
             then FOr (FEx (v, va), FOr (psi_1, psi_2))
             else FOr (psi_1, nFOr (FEx (v, va)) psi_2)))
  | nFOr (FAll (v, va)) (FOr (psi_1, psi_2)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) psi_1
      then FOr (psi_1, psi_2)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) psi_1
             then FOr (FAll (v, va), FOr (psi_1, psi_2))
             else FOr (psi_1, nFOr (FAll (v, va)) psi_2)))
  | nFOr (FBase v) (FBase va) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FBase va) then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FBase va)
             then FOr (FBase v, FBase va) else FOr (FBase va, FBase v)))
  | nFOr (FBase v) (FNot va) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FNot va) then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FNot va)
             then FOr (FBase v, FNot va) else FOr (FNot va, FBase v)))
  | nFOr (FBase v) (FAnd (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FAnd (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FAnd (va, vb))
             then FOr (FBase v, FAnd (va, vb))
             else FOr (FAnd (va, vb), FBase v)))
  | nFOr (FBase v) (FEx (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FEx (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FEx (va, vb))
             then FOr (FBase v, FEx (va, vb)) else FOr (FEx (va, vb), FBase v)))
  | nFOr (FBase v) (FAll (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FBase v) (FAll (va, vb))
      then FBase v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FBase v) (FAll (va, vb))
             then FOr (FBase v, FAll (va, vb))
             else FOr (FAll (va, vb), FBase v)))
  | nFOr (FNot v) (FBase va) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FBase va) then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FBase va)
             then FOr (FNot v, FBase va) else FOr (FBase va, FNot v)))
  | nFOr (FNot v) (FNot va) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FNot va) then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FNot va)
             then FOr (FNot v, FNot va) else FOr (FNot va, FNot v)))
  | nFOr (FNot v) (FAnd (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FAnd (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FAnd (va, vb))
             then FOr (FNot v, FAnd (va, vb)) else FOr (FAnd (va, vb), FNot v)))
  | nFOr (FNot v) (FEx (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FEx (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FEx (va, vb))
             then FOr (FNot v, FEx (va, vb)) else FOr (FEx (va, vb), FNot v)))
  | nFOr (FNot v) (FAll (va, vb)) =
    (if equal_aformulaa equal_ws1s equal_order (FNot v) (FAll (va, vb))
      then FNot v
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FNot v) (FAll (va, vb))
             then FOr (FNot v, FAll (va, vb)) else FOr (FAll (va, vb), FNot v)))
  | nFOr (FAnd (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) (FBase vb)
      then FAnd (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) (FBase vb)
             then FOr (FAnd (v, va), FBase vb)
             else FOr (FBase vb, FAnd (v, va))))
  | nFOr (FAnd (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) (FNot vb)
      then FAnd (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) (FNot vb)
             then FOr (FAnd (v, va), FNot vb) else FOr (FNot vb, FAnd (v, va))))
  | nFOr (FAnd (v, va)) (FAnd (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) (FAnd (vb, vc))
      then FAnd (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) (FAnd (vb, vc))
             then FOr (FAnd (v, va), FAnd (vb, vc))
             else FOr (FAnd (vb, vc), FAnd (v, va))))
  | nFOr (FAnd (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) (FEx (vb, vc))
      then FAnd (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) (FEx (vb, vc))
             then FOr (FAnd (v, va), FEx (vb, vc))
             else FOr (FEx (vb, vc), FAnd (v, va))))
  | nFOr (FAnd (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAnd (v, va)) (FAll (vb, vc))
      then FAnd (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAnd (v, va)) (FAll (vb, vc))
             then FOr (FAnd (v, va), FAll (vb, vc))
             else FOr (FAll (vb, vc), FAnd (v, va))))
  | nFOr (FEx (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FBase vb)
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FBase vb)
             then FOr (FEx (v, va), FBase vb) else FOr (FBase vb, FEx (v, va))))
  | nFOr (FEx (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FNot vb)
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FNot vb)
             then FOr (FEx (v, va), FNot vb) else FOr (FNot vb, FEx (v, va))))
  | nFOr (FEx (v, va)) (FAnd (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FAnd (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FAnd (vb, vc))
             then FOr (FEx (v, va), FAnd (vb, vc))
             else FOr (FAnd (vb, vc), FEx (v, va))))
  | nFOr (FEx (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FEx (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FEx (vb, vc))
             then FOr (FEx (v, va), FEx (vb, vc))
             else FOr (FEx (vb, vc), FEx (v, va))))
  | nFOr (FEx (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FEx (v, va)) (FAll (vb, vc))
      then FEx (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FEx (v, va)) (FAll (vb, vc))
             then FOr (FEx (v, va), FAll (vb, vc))
             else FOr (FAll (vb, vc), FEx (v, va))))
  | nFOr (FAll (v, va)) (FBase vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FBase vb)
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FBase vb)
             then FOr (FAll (v, va), FBase vb)
             else FOr (FBase vb, FAll (v, va))))
  | nFOr (FAll (v, va)) (FNot vb) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FNot vb)
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FNot vb)
             then FOr (FAll (v, va), FNot vb) else FOr (FNot vb, FAll (v, va))))
  | nFOr (FAll (v, va)) (FAnd (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FAnd (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FAnd (vb, vc))
             then FOr (FAll (v, va), FAnd (vb, vc))
             else FOr (FAnd (vb, vc), FAll (v, va))))
  | nFOr (FAll (v, va)) (FEx (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FEx (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FEx (vb, vc))
             then FOr (FAll (v, va), FEx (vb, vc))
             else FOr (FEx (vb, vc), FAll (v, va))))
  | nFOr (FAll (v, va)) (FAll (vb, vc)) =
    (if equal_aformulaa equal_ws1s equal_order (FAll (v, va)) (FAll (vb, vc))
      then FAll (v, va)
      else (if less_aformula (equal_ws1s, ord_ws1s) (equal_order, ord_order)
                 (FAll (v, va)) (FAll (vb, vc))
             then FOr (FAll (v, va), FAll (vb, vc))
             else FOr (FAll (vb, vc), FAll (v, va))));

fun nFNot (FNot phi) = phi
  | nFNot (FOr (phi, psi)) = nFAnd (nFNot phi) (nFNot psi)
  | nFNot (FAnd (phi, psi)) = nFOr (nFNot phi) (nFNot psi)
  | nFNot (FEx (b, phi)) = FAll (b, nFNot phi)
  | nFNot (FAll (b, phi)) = FEx (b, nFNot phi)
  | nFNot (FBool b) = FBool (not b)
  | nFNot (FBase v) = FNot (FBase v);

fun find0 FO i (Q m) = equal_nata i m
  | find0 FO i (Less (m1, m2)) = equal_nata i m1 orelse equal_nata i m2
  | find0 FO i (LessF (m1, m2)) = equal_nata i m1 orelse equal_nata i m2
  | find0 FO i (LessT (m1, m2)) = equal_nata i m1 orelse equal_nata i m2
  | find0 FO i (In (m, uu)) = equal_nata i m
  | find0 SO i (In (uv, m)) = equal_nata i m
  | find0 FO i (InT (m, uw)) = equal_nata i m
  | find0 SO i (InT (ux, m)) = equal_nata i m
  | find0 SO uz (Q v) = false
  | find0 SO uz (Less (v, vb)) = false
  | find0 SO uz (LessF (v, vb)) = false
  | find0 SO uz (LessT (v, vb)) = false;

fun find k l (FBool uu) = false
  | find k l (FBase a) = find0 k l a
  | find k l (FNot phi) = find k l phi
  | find k l (FOr (phi, psi)) = find k l phi orelse find k l psi
  | find k l (FAnd (phi, psi)) = find k l phi orelse find k l psi
  | find ka l (FEx (k, phi)) =
    find ka (if equal_ordera ka k then suc l else l) phi
  | find ka l (FAll (k, phi)) =
    find ka (if equal_ordera ka k then suc l else l) phi;

fun dec k m = (if less_nat k m then minus_nat m (suc zero_nat) else m);

fun decr0 ord k (Q m) = Q ((case ord of FO => dec k | SO => id) m)
  | decr0 ord k (Less (m1, m2)) =
    Less ((case ord of FO => dec k | SO => id) m1,
           (case ord of FO => dec k | SO => id) m2)
  | decr0 ord k (LessF (m1, m2)) =
    LessF ((case ord of FO => dec k | SO => id) m1,
            (case ord of FO => dec k | SO => id) m2)
  | decr0 ord k (LessT (m1, m2)) =
    LessT ((case ord of FO => dec k | SO => id) m1,
            (case ord of FO => dec k | SO => id) m2)
  | decr0 ord k (In (ma, m)) =
    In ((case ord of FO => dec k | SO => id) ma,
         (case ord of FO => id | SO => dec k) m)
  | decr0 ord k (InT (ma, m)) =
    InT ((case ord of FO => dec k | SO => id) ma,
          (case ord of FO => id | SO => dec k) m);

fun decr k l (FBool b) = FBool b
  | decr k l (FBase a) = FBase (decr0 k l a)
  | decr k l (FNot phi) = FNot (decr k l phi)
  | decr k l (FOr (phi, psi)) = FOr (decr k l phi, decr k l psi)
  | decr k l (FAnd (phi, psi)) = FAnd (decr k l phi, decr k l psi)
  | decr ka l (FEx (k, phi)) =
    FEx (k, decr ka (if equal_ordera ka k then suc l else l) phi)
  | decr ka l (FAll (k, phi)) =
    FAll (k, decr ka (if equal_ordera ka k then suc l else l) phi);

fun nFAll k (FAnd (phi, psi)) = nFAnd (nFAll k phi) (nFAll k psi)
  | nFAll k (FBool v) =
    (if find k zero_nat (FBool v) then FAll (k, FBool v)
      else decr k zero_nat (FBool v))
  | nFAll k (FBase v) =
    (if find k zero_nat (FBase v) then FAll (k, FBase v)
      else decr k zero_nat (FBase v))
  | nFAll k (FNot v) =
    (if find k zero_nat (FNot v) then FAll (k, FNot v)
      else decr k zero_nat (FNot v))
  | nFAll k (FOr (v, va)) =
    (if find k zero_nat (FOr (v, va)) then FAll (k, FOr (v, va))
      else decr k zero_nat (FOr (v, va)))
  | nFAll k (FEx (v, va)) =
    (if find k zero_nat (FEx (v, va)) then FAll (k, FEx (v, va))
      else decr k zero_nat (FEx (v, va)))
  | nFAll k (FAll (v, va)) =
    (if find k zero_nat (FAll (v, va)) then FAll (k, FAll (v, va))
      else decr k zero_nat (FAll (v, va)));

fun nFEx k (FOr (phi, psi)) = nFOr (nFEx k phi) (nFEx k psi)
  | nFEx k (FBool v) =
    (if find k zero_nat (FBool v) then FEx (k, FBool v)
      else decr k zero_nat (FBool v))
  | nFEx k (FBase v) =
    (if find k zero_nat (FBase v) then FEx (k, FBase v)
      else decr k zero_nat (FBase v))
  | nFEx k (FNot v) =
    (if find k zero_nat (FNot v) then FEx (k, FNot v)
      else decr k zero_nat (FNot v))
  | nFEx k (FAnd (v, va)) =
    (if find k zero_nat (FAnd (v, va)) then FEx (k, FAnd (v, va))
      else decr k zero_nat (FAnd (v, va)))
  | nFEx k (FEx (v, va)) =
    (if find k zero_nat (FEx (v, va)) then FEx (k, FEx (v, va))
      else decr k zero_nat (FEx (v, va)))
  | nFEx k (FAll (v, va)) =
    (if find k zero_nat (FAll (v, va)) then FEx (k, FAll (v, va))
      else decr k zero_nat (FAll (v, va)));

fun norm (FOr (phi, psi)) = nFOr (norm phi) (norm psi)
  | norm (FAnd (phi, psi)) = nFAnd (norm phi) (norm psi)
  | norm (FNot phi) = nFNot (norm phi)
  | norm (FEx (k, phi)) = nFEx k (norm phi)
  | norm (FAll (k, phi)) = nFAll k (norm phi)
  | norm (FBool v) = FBool v
  | norm (FBase v) = FBase v;

fun fut b idx psi =
  (if b then nFOR else nFAND)
    (snd (whilea idx psi
           (fn (phi, phia) =>
             not (membera (equal_aformula equal_ws1s equal_order) phia phi))
           (fn (phi, phia) =>
             (norm (deriv rderiv0 (zero idx) phi), phi :: phia))
           (psi, [])));

fun less xd xb (Abs_idx x) =
  let
    val (m, n) = x;
  in
    (case xd of FO => less_nat xb m | SO => less_nat xb n)
  end;

fun wf0 idx (Q m) = less FO m idx
  | wf0 idx (Less (m1, m2)) = less FO m1 idx andalso less FO m2 idx
  | wf0 idx (LessF (m1, m2)) = less FO m1 idx andalso less FO m2 idx
  | wf0 idx (LessT (m1, m2)) = less FO m1 idx andalso less FO m2 idx
  | wf0 idx (In (ma, m)) = less FO ma idx andalso less SO m idx
  | wf0 idx (InT (ma, m)) = less FO ma idx andalso less SO m idx;

fun restricta ord i = (case ord of FO => FBase (Q i) | SO => FBool true);

fun restr (FOr (phi, psi)) = FOr (restr phi, restr psi)
  | restr (FAnd (phi, psi)) = FAnd (restr phi, restr psi)
  | restr (FNot phi) = FNot (restr phi)
  | restr (FEx (k, phi)) = FEx (k, FAnd (restricta k zero_nat, restr phi))
  | restr (FAll (k, phi)) =
    FAll (k, FOr (FNot (restricta k zero_nat), restr phi))
  | restr (FBool v) = FBool v
  | restr (FBase v) = FBase v;

fun nullable0 (Q m) = false
  | nullable0 (Less (m1, m2)) = false
  | nullable0 (LessF (m1, m2)) = false
  | nullable0 (LessT (m1, m2)) = true
  | nullable0 (In (ma, m)) = false
  | nullable0 (InT (ma, m)) = true;

fun nullable (FBool b) = b
  | nullable (FBase a) = nullable0 a
  | nullable (FNot phi) = not (nullable phi)
  | nullable (FOr (phi, psi)) = nullable phi orelse nullable psi
  | nullable (FAnd (phi, psi)) = nullable phi andalso nullable psi
  | nullable (FEx (k, phi)) = nullable phi
  | nullable (FAll (k, phi)) = nullable phi;

fun finalize idx (FEx (k, phi)) =
  fut true idx (nFEx k (finalize (suca k idx) phi))
  | finalize idx (FAll (k, phi)) =
    fut false idx (nFAll k (finalize (suca k idx) phi))
  | finalize idx (FOr (phi, psi)) = FOr (finalize idx phi, finalize idx psi)
  | finalize idx (FAnd (phi, psi)) = FAnd (finalize idx phi, finalize idx psi)
  | finalize idx (FNot phi) = FNot (finalize idx phi)
  | finalize idx (FBool v) = FBool v
  | finalize idx (FBase v) = FBase v;

fun final idx = nullable o finalize idx;

fun lderiv0 (bs1, bs2) (Q m) = (if nth bs1 m then FBool true else FBase (Q m))
  | lderiv0 (bs1, bs2) (Less (m1, m2)) =
    (case (nth bs1 m1, nth bs1 m2) of (true, true) => FBool false
      | (true, false) => FBase (Q m2) | (false, true) => FBool false
      | (false, false) => FBase (Less (m1, m2)))
  | lderiv0 (bs1, bs2) (LessF (m1, m2)) =
    (case (nth bs1 m1, nth bs1 m2) of (true, true) => FBool false
      | (true, false) => FBool true | (false, true) => FBool false
      | (false, false) => FBase (LessF (m1, m2)))
  | lderiv0 (bs1, bs2) (LessT (m1, m2)) =
    (case (nth bs1 m1, nth bs1 m2) of (true, true) => FBool false
      | (true, false) => FBool true | (false, true) => FBool false
      | (false, false) => FBase (LessT (m1, m2)))
  | lderiv0 (bs1, bs2) (In (ma, m)) =
    (case (nth bs1 ma, nth bs2 m) of (true, true) => FBool true
      | (true, false) => FBool false | (false, x) => FBase (In (ma, m)))
  | lderiv0 (bs1, bs2) (InT (ma, m)) =
    (case (nth bs1 ma, nth bs2 m) of (true, true) => FBool true
      | (true, false) => FBool false | (false, x) => FBase (InT (ma, m)));

fun ws1s_wf n (FBool uu) = true
  | ws1s_wf n (FBase a) = wf0 n a
  | ws1s_wf n (FNot phi) = ws1s_wf n phi
  | ws1s_wf n (FOr (phi, psi)) = ws1s_wf n phi andalso ws1s_wf n psi
  | ws1s_wf n (FAnd (phi, psi)) = ws1s_wf n phi andalso ws1s_wf n psi
  | ws1s_wf n (FEx (k, phi)) = ws1s_wf (suca k n) phi
  | ws1s_wf n (FAll (k, phi)) = ws1s_wf (suca k n) phi;

fun restrict phi =
  foldr (fn (k, x) => (fn a => FAnd (restricta k x, a))) (fv phi) (restr phi);

fun sigma (Abs_idx xa) =
  let
    val (n, na) = xa;
  in
    map (fn bs => (take n bs, drop n bs))
      (n_lists (plus_nat n na) [true, false])
  end;

fun rtrancl_while_test p (ws, uu) = not (null ws) andalso p (hd ws);

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun rtrancl_while_step A_ f (ws, z) =
  let
    val x = hd ws;
    val new = remdups A_ (filter (fn y => not (member A_ y z)) (f x));
  in
    (new @ tl ws, sup_set A_ (Set new) z)
  end;

fun while_option b c s = (if b s then while_option b c (c s) else SOME s);

val bot_set : 'a set = Set [];

fun rtrancl_while A_ p f x =
  while_option (rtrancl_while_test p) (rtrancl_while_step A_ f)
    ([x], insert A_ x bot_set);

fun left_formula0 x = true;

fun ws1s_left_formula (FBool uu) = true
  | ws1s_left_formula (FBase a) = left_formula0 a
  | ws1s_left_formula (FNot phi) = ws1s_left_formula phi
  | ws1s_left_formula (FOr (phi, psi)) =
    ws1s_left_formula phi andalso ws1s_left_formula psi
  | ws1s_left_formula (FAnd (phi, psi)) =
    ws1s_left_formula phi andalso ws1s_left_formula psi
  | ws1s_left_formula (FEx (k, phi)) = ws1s_left_formula phi
  | ws1s_left_formula (FAll (k, phi)) = ws1s_left_formula phi;

fun check_eqv idx r s =
  ws1s_wf idx r andalso ws1s_left_formula r andalso
    (ws1s_wf idx s andalso ws1s_left_formula s andalso
      (case rtrancl_while
              (equal_prod (equal_aformula equal_ws1s equal_order)
                (equal_aformula equal_ws1s equal_order))
              (fn (p, q) => equal_bool (final idx p) (final idx q))
              (fn (p, q) =>
                map (fn a =>
                      (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q)))
                  (sigma idx))
              (norm (restrict r), norm (restrict s))
        of NONE => false | SOME ([], _) => true | SOME (_ :: _, _) => false));

end; (*struct WS1S_Generated*)
