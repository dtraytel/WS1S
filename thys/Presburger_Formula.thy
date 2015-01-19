theory Presburger_Formula
imports
  Abstract_Formula
  "~~/src/Tools/Permanent_Interpretation"
begin

type_synonym interp = "nat list"
type_synonym atom = "bool list"
type_synonym "value" = "nat"
datatype_new presb = Eq (tm: "int list") (const: int)
datatype_compat presb
derive linorder list
derive linorder presb
type_synonym formula = "(presb, unit) aformula"

definition assigns :: "nat \<Rightarrow> interp \<Rightarrow> unit \<Rightarrow> value" ("_\<^bsup>_\<^esup>_" [900, 999, 999] 999) where
  "assigns n I _ = I!n"

abbreviation nvars :: "interp \<Rightarrow> nat" ("#\<^sub>V _" [1000] 900) where
  "nvars \<equiv> length"

definition Length :: "interp \<Rightarrow> nat" where
  "Length I = (LEAST l. \<forall>n \<in> set I. n \<le> 2^l)"

definition Extend :: "unit \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> value \<Rightarrow> interp" where
  "Extend _ i I m = insert_nth i m I"

definition CONS :: "atom \<Rightarrow> interp \<Rightarrow> interp" where
  "CONS bs I = map (\<lambda>(b,n). 2*n + (if b then 1 else 0)) (zip bs I)"

definition SNOC :: "atom \<Rightarrow> interp \<Rightarrow> interp" where
  "SNOC bs I = map (\<lambda>(b,n). n + (if b then 2 ^ Length I else 0)) (zip bs I)"

fun enc_nat :: "nat \<Rightarrow> atom" where
  "enc_nat n = (if n=0 then [] else (n mod 2 \<noteq> 0) # enc_nat (n div 2))"

definition enc :: "interp \<Rightarrow> atom list" where
  "enc = map enc_nat"

definition extend :: "unit \<Rightarrow> bool \<Rightarrow> atom \<Rightarrow> atom" where
  "extend _ b bs \<equiv> b # bs"

abbreviation size_atom :: "atom \<Rightarrow> nat" where
  "size_atom \<equiv> length"

definition FV0 :: "unit \<Rightarrow> presb \<Rightarrow> nat set" where
  "FV0 _ fm = (case fm of Eq is i \<Rightarrow> {n. n < length is \<and> is!n \<noteq> 0})"

primrec wf0 :: "nat \<Rightarrow> presb \<Rightarrow> bool" where
  "wf0 idx (Eq is i) = (length is \<le> idx)"

fun find0 where
  "find0 (_::unit) n (Eq is i) = (is!n \<noteq> 0)"

primrec decr0 where
  "decr0 (_::unit) k (Eq is i) = Eq (take k is @ drop (Suc k) is) i"

definition eval_tm :: "interp \<Rightarrow> int list \<Rightarrow> int" where
  "eval_tm I is = listsum (map (\<lambda>(a,b). int a * b) (zip I is))"

primrec satisfies0 where
  "satisfies0 I (Eq is i) = (eval_tm I is = i)"

fun lderiv0 :: "bool list \<Rightarrow> presb \<Rightarrow> formula" where
  "lderiv0 bs (Eq is i) =
  (let v = i - eval_tm (map (\<lambda>b. if b then 1 else 0) bs) is
   in if v mod 2 = 0 then FBase (Eq is (v div 2)) else FBool False)"

(*
lemma "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = size_atom x\<rbrakk> \<Longrightarrow>
  Formula_Operations.satisfies Extend satisfies0 \<AA> (lderiv0 x a) =
  satisfies0 (CONS x \<AA>) a"
  apply (induct a)
  apply (auto simp add: CONS_def eval_tm_def Let_def zip_map1 o_def split_beta
    Formula_Operations.satisfies.simps listsum_addf int_mult
   listsum_mult_const listsum_const_mult algebra_simps split: if_splits)
*)

fun rderiv0 :: "bool list \<Rightarrow> presb \<Rightarrow> formula" where
  "rderiv0 bs (Eq is i) = 
  (let v = i - eval_tm (map (\<lambda>b. if b then 1 else 0) bs) is
   in if v mod 2 = 0 then FBase (Eq is (v div 2)) else FBool False)"

text "\<Sum> ni * ci + 2 ^ l * \<Sum> bi * ci = x"
value "lderiv0 [False, False] (Eq [2, - 3] 2)"

lemma "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = size_atom x\<rbrakk> \<Longrightarrow>
  Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (rderiv0 x a) =
  satisfies0 (SNOC x \<AA>) a"
  apply (induct a)
  apply (auto simp add: SNOC_def eval_tm_def Let_def Formula_Operations.satisfies_bounded.simps)
  oops

primrec nullable0 where
  "nullable0 (Eq is i) = (i = 0)"

definition \<sigma> :: "nat \<Rightarrow> atom list" where
  "\<sigma> n = List.n_lists n [True, False]"

section \<open>Interpretation\<close>

lemma "(LEAST n::nat. True) = 0"
by (metis One_nat_def less_one not_less_Least not_less_eq)

declare [[goals_limit = 100]]

abbreviation "zero n \<equiv> replicate n False"
abbreviation "SUC \<equiv> \<lambda>_::unit. Suc"
definition len :: "nat \<Rightarrow> nat" where
  "len m = (LEAST l. m \<le> 2^l)"
abbreviation "clear_lsb m \<equiv> m div 2"
abbreviation "upshift m \<equiv> m * 2"
abbreviation "set_bit n m \<equiv> m + (if m div 2^n mod 2 = 0 then 2^n else 0)"
abbreviation "cut_bits n m \<equiv> m mod 2^n"

permanent_interpretation Presb: Word_Formula
  where SUC = SUC and LESS = "\<lambda>_. op <" and Length = Length
  and assigns = assigns and nvars = nvars and Extend = Extend and CONS = CONS and SNOC = SNOC
  and extend = extend and size = size_atom and zero = zero and eval = "op ="
  and downshift = clear_lsb and upshift = upshift and add = set_bit and cut = cut_bits and len = len
  and FV0 = FV0 and find0 = find0 and wf0 = wf0 and decr0 = decr0 and satisfies0 = satisfies0
  and nullable0 = nullable0 and lderiv0 = lderiv0 and rderiv0 = rderiv0
  and TYPEVARS = undefined and enc = enc and alphabet = \<sigma>
  defining norm = "Formula_Operations.norm FV0 decr0"
  and nFOr = "Formula_Operations.nFOr :: formula \<Rightarrow> _"
  and nFAnd = "Formula_Operations.nFAnd :: formula \<Rightarrow> _"
  and nFNot = "Formula_Operations.nFNot :: formula \<Rightarrow> _"
  and nFEx = "Formula_Operations.nFEx FV0 decr0"
  and nFAll = "Formula_Operations.nFAll FV0 decr0"
  and decr = "Formula_Operations.decr decr0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and find = "Formula_Operations.find find0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and deriv = "\<lambda>d0 (a :: atom) (\<phi> :: formula). Formula_Operations.deriv extend d0 a \<phi>"
  and nullable = "\<lambda>\<phi> :: formula. Formula_Operations.nullable nullable0 \<phi>"
  and fut_default = "Formula.fut_default extend zero rderiv0"
  and fut = "Formula.fut extend zero FV0 decr0 rderiv0"
  and finalize = "Formula.finalize SUC extend zero FV0 decr0 rderiv0"
  and final = "Formula.final SUC extend zero FV0 decr0
     nullable0 rderiv0 :: nat \<Rightarrow> formula \<Rightarrow> _"
  and presb_wf = "Formula_Operations.wf SUC (wf0 :: nat \<Rightarrow> presb \<Rightarrow> _)"
  and check_eqv = "\<lambda>idx. DA.check_eqv (\<sigma> idx)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (presb_wf idx :: formula \<Rightarrow> bool)"
  and automaton = "DA.automaton
    (\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi> :: formula))"
apply default
apply (auto simp: Suc_le_eq \<sigma>_def set_n_lists len_def
  FV0_def dec_def[abs_def] min_def nth_append
  split: presb.splits if_splits)
sorry

(*Workaround for code generation*)
lemma [code]: "check_eqv idx r s = (presb_wf idx r \<and> presb_wf idx s \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = final idx q)
    (\<lambda>(p, q). map (\<lambda>a. (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q))) (\<sigma> idx)) (r, s) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def Presb.check_eqv_def ..

definition while where [code del, code_abbrev]: "while idx \<phi> = while_default (fut_default idx \<phi>)"
declare while_default_code[of "fut_default idx \<phi>" for idx \<phi>, folded while_def, code]

end
