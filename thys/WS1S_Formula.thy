(*<*)
theory WS1S_Formula
imports
  Abstract_Formula
  FSet_More
  "~~/src/Tools/Permanent_Interpretation"
begin

hide_const (open) cut
(*>*)

section \<open>Concrete Atomic WS1S Formulas\<close>

definition "eval P x = (x |\<in>| P)"
definition "downshift P = (\<lambda>x. x - Suc 0) |`| (P |-| {|0|})"
definition "upshift P = Suc |`| P"
definition "lift bs i P = (if bs ! i then finsert 0 (upshift P) else upshift P)"
definition "snoc n bs i P = (if bs ! i then finsert n P else P)"
definition "cut n P = ffilter (\<lambda>i. i < n) P"
definition "len P = (if P = {||} then 0 else Suc (fMax P))"

datatype_new order = FO | SO
datatype_compat order
derive linorder order

typedef idx = "UNIV :: (nat \<times> nat) set" by (rule UNIV_witness)

setup_lifting type_definition_idx

lift_definition ZERO :: "idx" is "(0, 0)" .
lift_definition SUC :: "order \<Rightarrow> idx \<Rightarrow> idx" is
  "\<lambda>ord (m, n). case ord of FO \<Rightarrow> (Suc m, n) | SO \<Rightarrow> (m, Suc n)" .
lift_definition LESS :: "order \<Rightarrow> nat \<Rightarrow> idx \<Rightarrow> bool" is
  "\<lambda>ord l (m, n). case ord of FO \<Rightarrow> l < m | SO \<Rightarrow> l < n" .
abbreviation "LEQ ord l idx \<equiv> LESS ord l (SUC ord idx)"

definition "MSB Is \<equiv>
  if \<forall>P \<in> set Is. P = {||} then 0 else Suc (Max (\<Union>P \<in> set Is. fset P))"

lemma MSB_Nil[simp]: "MSB [] = 0"
  unfolding MSB_def by simp

lemma MSB_Cons[simp]: "MSB (I # Is) = max (if I = {||} then 0 else Suc (fMax I)) (MSB Is)"
  unfolding MSB_def including fset.lifting
  by transfer (auto simp: Max_Un list_all_iff Sup_bot_conv(2)[symmetric] simp del: Sup_bot_conv(2))

lemma MSB_append[simp]: "MSB (I1 @ I2) = max (MSB I1) (MSB I2)"
  by (induct I1) auto

lemma MSB_insert_nth[simp]:
  "MSB (insert_nth n P Is) = max (if P = {||} then 0 else Suc (fMax P)) (MSB Is)"
  by (subst (2) append_take_drop_id[of n Is, symmetric])
    (simp only: insert_nth_take_drop MSB_append MSB_Cons MSB_Nil)

lemma MSB_greater:
  "\<lbrakk>i < length Is; p |\<in>| Is ! i\<rbrakk> \<Longrightarrow> p < MSB Is"
  unfolding MSB_def by (fastforce simp: Bex_def in_set_conv_nth less_Suc_eq_le intro: Max_ge)

lemma MSB_mono: "set I1 \<subseteq> set I2 \<Longrightarrow> MSB I1 \<le> MSB I2"
  unfolding MSB_def including fset.lifting
  by transfer (auto simp: list_all_iff intro!: Max_ge)

lemma MSB_map_index'_CONS[simp]:
  "MSB (map_index' i (lift bs) Is) =
  (if MSB Is = 0 \<and> (\<forall>i \<in> {i ..< i + length Is}. \<not> bs ! i) then 0 else Suc (MSB Is))"
  by (induct Is arbitrary: i)
   (auto split: if_splits simp: mono_fMax_commute[where f = Suc, symmetric] mono_def
    lift_def upshift_def,
    metis atLeastLessThan_iff le_antisym not_less_eq_eq)

lemma MSB_map_index'_SNOC[simp]:
  "MSB Is \<le> n \<Longrightarrow> MSB (map_index' i (snoc n bs) Is) =
  (if (\<forall>i \<in> {i ..< i + length Is}. \<not> bs ! i) then MSB Is else Suc n)"
  by (induct Is arbitrary: i)
    (auto split: if_splits simp: mono_fMax_commute[where f = Suc, symmetric] mono_def
    snoc_def, (metis atLeastLessThan_iff le_antisym not_less_eq_eq)+)

lemma MSB_replicate[simp]: "MSB (replicate n P) = (if P = {||} \<or> n = 0 then 0 else Suc (fMax P))"
  by (induct n) auto

typedef interp =
  "{(n :: nat, I1 :: nat fset list, I2  :: nat fset list) | n I1 I2. MSB (I1 @ I2) \<le> n}"
  by auto

setup_lifting type_definition_interp

lift_definition assigns :: "nat \<Rightarrow> interp \<Rightarrow> order \<Rightarrow> nat fset" ("_\<^bsup>_\<^esup>_" [900, 999, 999] 999)
  is "\<lambda>n (_, I1, I2) ord. case ord of FO \<Rightarrow> if n < length I1 then I1 ! n else {||}
    | SO \<Rightarrow> if n < length I2 then I2 ! n else {||}" .
lift_definition nvars :: "interp \<Rightarrow> idx" ("#\<^sub>V _" [1000] 900)
  is "\<lambda>(_, I1, I2). (length I1, length I2)" .
lift_definition Length :: "interp \<Rightarrow> nat"
  is "\<lambda>(n, _, _). n" .
lift_definition Extend :: "order \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> nat fset \<Rightarrow> interp"
  is "\<lambda>ord i (n, I1, I2) P. case ord of
      FO \<Rightarrow> (max n (if P = {||} then 0 else Suc (fMax P)), insert_nth i P I1, I2)
    | SO \<Rightarrow> (max n (if P = {||} then 0 else Suc (fMax P)), I1, insert_nth i P I2)"
  using MSB_mono by (auto simp del: insert_nth_take_drop split: order.splits)

lift_definition CONS :: "(bool list \<times> bool list) \<Rightarrow> interp \<Rightarrow> interp"
  is "\<lambda>(bs1, bs2) (n, I1, I2).
   (Suc n, map_index (lift bs1) I1, map_index (lift bs2) I2)"
  by auto

lift_definition SNOC :: "(bool list \<times> bool list) \<Rightarrow> interp \<Rightarrow> interp"
  is "\<lambda>(bs1, bs2) (n, I1, I2).
   (Suc n, map_index (snoc n bs1) I1, map_index (snoc n bs2) I2)"
  by (auto simp: Let_def)

abbreviation "enc_atom_bool I n \<equiv> map (\<lambda>P. n |\<in>| P) I"

abbreviation "enc_atom I1 I2 n \<equiv> (enc_atom_bool I1 n, enc_atom_bool I2 n)"

type_synonym atom = "bool list \<times> bool list"

lift_definition enc :: "interp \<Rightarrow> atom list"
  is "\<lambda>(n, I1, I2). let m = MSB (I1 @ I2) in
    map (enc_atom I1 I2) [0 ..< m] @
    replicate (n - m) (replicate (length I1) False, replicate (length I2) False)" .

lift_definition zero :: "idx \<Rightarrow> atom"
  is "\<lambda>(m, n). (replicate m False, replicate n False)" .

definition "extend ord b \<equiv>
  \<lambda>(bs1, bs2). case ord of FO \<Rightarrow> (b # bs1, bs2) | SO \<Rightarrow> (bs1, b # bs2)"
lift_definition size_atom :: "bool list \<times> bool list \<Rightarrow> idx"
  is "\<lambda>(bs1, bs2). (length bs1, length bs2)" .

type_synonym fo = nat
type_synonym so = nat

datatype_new ws1s =
  Q fo |
  Less fo fo | LessF fo fo | LessT fo fo |
  In fo so | InT fo so
datatype_compat ws1s
derive linorder option
derive linorder ws1s
type_synonym formula = "(ws1s, order) aformula"

primrec wf0 where
  "wf0 idx (Q m) = LESS FO m idx"
| "wf0 idx (Less m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (LessF m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (LessT m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (In m M) = (LESS FO m idx \<and> LESS SO M idx)"
| "wf0 idx (InT m M) = (LESS FO m idx \<and> LESS SO M idx)"

fun left_formula0 where
  "left_formula0 x = True"

fun FV0 where
  "FV0 (Q m) = [(FO, m)]"
| "FV0 (Less m1 m2) = List.insert (FO, m1) [(FO, m2)]"
| "FV0 (LessF m1 m2) = List.insert (FO, m1) [(FO, m2)]"
| "FV0 (LessT m1 m2) = List.insert (FO, m1) [(FO, m2)]"
| "FV0 (In m M) = [(FO, m), (SO, M)]"
| "FV0 (InT m M) = [(FO, m), (SO, M)]"

fun find0 where
  "find0 FO i (Q m) = (i = m)"
| "find0 FO i (Less m1 m2) = (i = m1 \<or> i = m2)"
| "find0 FO i (LessF m1 m2) = (i = m1 \<or> i = m2)"
| "find0 FO i (LessT m1 m2) = (i = m1 \<or> i = m2)"
| "find0 FO i (In m _) = (i = m)"
| "find0 SO i (In _ M) = (i = M)"
| "find0 FO i (InT m _) = (i = m)"
| "find0 SO i (InT _ M) = (i = M)"
| "find0 _ _ _ = False"

primrec decr0 where
  "decr0 ord k (Q m) = Q (case_order (dec k) id ord m)"
| "decr0 ord k (Less m1 m2) = Less (case_order (dec k) id ord m1) (case_order (dec k) id ord m2)"
| "decr0 ord k (LessF m1 m2) = LessF (case_order (dec k) id ord m1) (case_order (dec k) id ord m2)"
| "decr0 ord k (LessT m1 m2) = LessT (case_order (dec k) id ord m1) (case_order (dec k) id ord m2)"
| "decr0 ord k (In m M) = In (case_order (dec k) id ord m) (case_order id (dec k) ord M)"
| "decr0 ord k (InT m M) = InT (case_order (dec k) id ord m) (case_order id (dec k) ord M)"

primrec satisfies0 where
  "satisfies0 \<AA> (Q m) = (m\<^bsup>\<AA>\<^esup>FO \<noteq> {||})"
| "satisfies0 \<AA> (Less m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in if P1 = {||} \<or> P2 = {||} then False else fMin P1 < fMin P2)"
| "satisfies0 \<AA> (LessF m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in
      if P1 = {||} then False else if P2 = {||} then True else fMin P1 < fMin P2)"
| "satisfies0 \<AA> (LessT m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in
      if P2 = {||} then True else if P1 = {||} then False else fMin P1 < fMin P2)"
| "satisfies0 \<AA> (In m M) =
   (let P = m\<^bsup>\<AA>\<^esup>FO in if P = {||} then False else fMin P |\<in>| M\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (InT m M) =
   (let P = m\<^bsup>\<AA>\<^esup>FO in if P = {||} then True else fMin P |\<in>| M\<^bsup>\<AA>\<^esup>SO)"

fun lderiv0 where
  "lderiv0 (bs1, bs2) (Q m) = (if bs1 ! m then FBool True else FBase (Q m))"
| "lderiv0 (bs1, bs2) (Less m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (Less m1 m2)
  | (True, False) \<Rightarrow> FBase (Q m2)
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (LessF m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (LessF m1 m2)
  | (True, False) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (LessT m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (LessT m1 m2)
  | (True, False) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (In m M) = (case (bs1 ! m, bs2 ! M) of
    (False, _) \<Rightarrow> FBase (In m M)
  | (True, True) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (InT m M) = (case (bs1 ! m, bs2 ! M) of
    (False, _) \<Rightarrow> FBase (InT m M)
  | (True, True) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"

fun rderiv0 where
  "rderiv0 (bs1, bs2) (Q m) = (if bs1 ! m then FBool True else FBase (Q m))"
| "rderiv0 (bs1, bs2) (Less m1 m2) = (case bs1 ! m2 of
    False \<Rightarrow> FBase (Less m1 m2)
  | True \<Rightarrow> FBase (LessF m1 m2))"
| "rderiv0 (bs1, bs2) (LessF m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (True, False) \<Rightarrow> FBase (LessT m1 m2)
  | _ \<Rightarrow> FBase (LessF m1 m2))"
| "rderiv0 (bs1, bs2) (LessT m1 m2) = (case bs1 ! m2 of
    False \<Rightarrow> FBase (LessT m1 m2)
  | True \<Rightarrow> FBase (LessF m1 m2))"
| "rderiv0 (bs1, bs2) (In m M) = (case (bs1 ! m, bs2 ! M) of
    (True, True) \<Rightarrow> FBase (InT m M)
  | _ \<Rightarrow> FBase (In m M))"
| "rderiv0 (bs1, bs2) (InT m M) = (case (bs1 ! m, bs2 ! M) of
    (True, False) \<Rightarrow> FBase (In m M)
  | _ \<Rightarrow> FBase (InT m M))"

fun nullable0 where
  "nullable0 (Q m) = False"
| "nullable0 (Less m1 m2) = False"
| "nullable0 (LessF m1 m2) = False"
| "nullable0 (LessT m1 m2) = True"
| "nullable0 (In m M) = False"
| "nullable0 (InT m M) = True"

lift_definition \<sigma> :: "idx \<Rightarrow> atom list"
  is "(\<lambda>(n, N). map (\<lambda>bs. (take n bs, drop n bs)) (List.n_lists (n + N) [True, False]))" .

section {* Interpretation *}

lemma fMin_fimage_Suc[simp]: "x |\<in>| A \<Longrightarrow> fMin (Suc |`| A) = Suc (fMin A)"
  by (rule fMin_eqI) (auto intro: fMin_in)

lemma fMin_eq_0[simp]: "0 |\<in>| A \<Longrightarrow> fMin A = (0 :: nat)"
  by (rule fMin_eqI) auto

lemma insert_nth_Cons[simp]:
  "insert_nth i x (y # xs) = (case i of 0 \<Rightarrow> x # y # xs | Suc i \<Rightarrow> y # insert_nth i x xs)"
  by (cases i) simp_all

lemma insert_nth_commute[simp]:
  assumes "j \<le> i" "i \<le> length xs"
  shows "insert_nth j y (insert_nth i x xs) = insert_nth (Suc i) x (insert_nth j y xs)"
  using assms by (induct xs arbitrary: i j) (auto simp del: insert_nth_take_drop split: nat.splits)

lemma SUC_SUC[simp]: "SUC ord (SUC ord' idx) = SUC ord' (SUC ord idx)"
  by transfer (auto split: order.splits)

lemma LESS_SUC[simp]:
  "LESS ord 0 (SUC ord idx)"
  "LESS ord (Suc l) (SUC ord idx) = LESS ord l idx"
  "ord \<noteq> ord' \<Longrightarrow> LESS ord l (SUC ord' idx) = LESS ord l idx"
  "LESS ord l idx \<Longrightarrow> LESS ord l (SUC ord' idx)"
  by (transfer, force split: order.splits)+

lemma nvars_Extend[simp]:
  "#\<^sub>V (Extend ord i \<AA> P) = SUC ord (#\<^sub>V \<AA>)"
  by (transfer, force split: order.splits)

lemma Length_Extend[simp]:
  "Length (Extend k i \<AA> P) = max (Length \<AA>) (if P = {||} then 0 else Suc (fMax P))"
  unfolding max_def by (split if_splits, transfer) (force split: order.splits)

lemma assigns_Extend[simp]:
  "LEQ ord i (#\<^sub>V \<AA>) \<Longrightarrow>m\<^bsup>Extend ord i \<AA> P\<^esup>ord = (if m = i then P else dec i m\<^bsup>\<AA>\<^esup>ord)"
  "ord \<noteq> ord' \<Longrightarrow> m\<^bsup>Extend ord i \<AA> P\<^esup>ord' = m\<^bsup>\<AA>\<^esup>ord'"
  by (transfer, force simp: dec_def min_def nth_append split: order.splits)+

lemma Extend_commute_safe[simp]:
  "\<lbrakk>j \<le> i; LEQ ord i (#\<^sub>V \<AA>)\<rbrakk> \<Longrightarrow>
    Extend ord j (Extend ord i \<AA> P1) P2 = Extend ord (Suc i) (Extend ord j \<AA> P2) P1"
  by (transfer,
    force simp del: insert_nth_take_drop simp: replicate_add[symmetric] split: order.splits)

lemma Extend_commute_unsafe:
  "ord \<noteq> ord' \<Longrightarrow> Extend ord j (Extend ord' i \<AA> P1) P2 = Extend ord' i (Extend ord j \<AA> P2) P1"
  by (transfer, force simp: replicate_add[symmetric] split: order.splits)

lemma Length_CONS[simp]:
  "Length (CONS x \<AA>) = Suc (Length \<AA>)"
  by (transfer, force split: order.splits)

lemma Length_SNOC[simp]:
  "Length (SNOC x \<AA>) = Suc (Length \<AA>)"
  by (transfer, force simp: Let_def split: order.splits)

lemma nvars_CONS[simp]:
  "#\<^sub>V (CONS x \<AA>) = #\<^sub>V \<AA>"
  by (transfer, force)

lemma nvars_SNOC[simp]:
  "#\<^sub>V (SNOC x \<AA>) = #\<^sub>V \<AA>"
  by (transfer, force simp: Let_def)

lemma assigns_CONS[simp]:
  assumes "#\<^sub>V \<AA> = size_atom bs1_bs2"
  shows "LESS ord x (#\<^sub>V \<AA>) \<Longrightarrow> x\<^bsup>CONS bs1_bs2 \<AA>\<^esup>ord =
    (if split case_order bs1_bs2 ord ! x then finsert 0 (upshift (x\<^bsup>\<AA>\<^esup>ord)) else upshift (x\<^bsup>\<AA>\<^esup>ord))"
  by (insert assms, transfer) (auto simp: lift_def split: order.splits)

lemma assigns_SNOC[simp]:
  assumes "#\<^sub>V \<AA> = size_atom bs1_bs2"
  shows "LESS ord x (#\<^sub>V \<AA>) \<Longrightarrow> x\<^bsup>SNOC bs1_bs2 \<AA>\<^esup>ord =
    (if split case_order bs1_bs2 ord ! x then finsert (Length \<AA>) (x\<^bsup>\<AA>\<^esup>ord) else x\<^bsup>\<AA>\<^esup>ord)"
  by (insert assms, transfer) (force simp: snoc_def Let_def split: order.splits)

lemma map_index'_eq_conv[simp]:
  "map_index' i f xs = map_index' j g xs = (\<forall>k < length xs. f (i + k) (xs ! k) = g (j + k) (xs ! k))"
proof (induct xs arbitrary: i j)
  case Cons from Cons(1)[of "Suc i" "Suc j"] show ?case by (auto simp: nth_Cons split: nat.splits)
qed simp

lemma fMax_Diff_0[simp]: "Suc m |\<in>| P \<Longrightarrow> fMax (P |-| {|0|}) = fMax P"
  by (rule fMax_eqI) (auto intro: fMax_in dest: fMax_ge)

lemma Suc_fMax_pred_fimage[simp]:
  assumes "Suc p |\<in>| P" "0 |\<notin>| P"
  shows "Suc (fMax ((\<lambda>x. x - Suc 0) |`| P)) = fMax P"
  using assms by (subst mono_fMax_commute[of Suc, unfolded mono_def, simplified]) (auto simp: o_def)

lemma Extend_CONS[simp]: "#\<^sub>V \<AA> = size_atom x \<Longrightarrow> Extend ord 0 (CONS x \<AA>) P =
  CONS (extend ord (eval P 0) x) (Extend ord 0 \<AA> (downshift P))"
  by transfer (auto simp: extend_def o_def gr0_conv_Suc
    mono_fMax_commute[of Suc, symmetric, unfolded mono_def, simplified]
    lift_def upshift_def downshift_def eval_def
    dest!: fsubset_fsingletonD split: order.splits)

lemma size_atom_extend[simp]:
  "size_atom (extend ord b x) = SUC ord (size_atom x)"
  unfolding extend_def by transfer (simp split: prod.splits order.splits)

lemma size_atom_zero[simp]:
  "size_atom (zero idx) = idx"
  unfolding extend_def by transfer (simp split: prod.splits order.splits)

lemma interp_eqI:
  "\<lbrakk>Length \<AA> = Length \<BB>; #\<^sub>V \<AA> = #\<^sub>V \<BB>; \<And>m k. LESS k m (#\<^sub>V \<AA>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k\<rbrakk> \<Longrightarrow> \<AA> = \<BB>"
  by transfer (force split: order.splits intro!: nth_equalityI)

lemma Extend_SNOC_cut[unfolded eval_def cut_def Length_SNOC, simp]:
  "\<lbrakk>len P \<le> Length (SNOC x \<AA>); #\<^sub>V \<AA> = size_atom x\<rbrakk> \<Longrightarrow>
  Extend ord 0 (SNOC x \<AA>) P =
    SNOC (extend ord (if eval P (Length \<AA>) then True else False) x) (Extend ord 0 \<AA> (cut (Length \<AA>) P))"
  by transfer (fastforce simp: extend_def len_def cut_def ffilter_eq_fempty_iff snoc_def eval_def
    split: if_splits order.splits dest: fMax_ge fMax_boundedD intro: fMax_in)

lemma nth_replicate_simp: "replicate m x ! i = (if i < m then x else [] ! (i - m))"
  by (induct m arbitrary: i) (auto simp: nth_Cons')

lemma MSB_eq_SucD: "MSB Is = Suc x \<Longrightarrow> \<exists>P\<in>set Is. x |\<in>| P"
  using Max_in[of "\<Union>x\<in>set Is. fset x"]
  unfolding MSB_def by (force simp: fmember_def split: if_splits)

lemma last_enc_atom_MSB:
  fixes I1 I2
  defines "xs \<equiv> map (enc_atom I1 I2) [0..<MSB (I1 @ I2)]"
  assumes "m = length I1" "n = length I2" "xs \<noteq> []"
  shows "last xs \<noteq> (replicate m False, replicate n False)"
proof (rule ccontr, unfold not_not)
  assume "last xs = (replicate m False, replicate n False)"
  moreover from `xs \<noteq> []` obtain i where i: "MSB (I1 @ I2) = Suc i"
    unfolding xs_def by (auto simp: gr0_conv_Suc)
  ultimately have "enc_atom I1 I2 i = (replicate m False, replicate n False)"
    unfolding xs_def by auto
  with i show False
   by (auto simp: list_eq_iff_nth_eq max_def in_set_conv_nth dest!: MSB_eq_SucD split: if_splits)
qed

lemma append_replicate_inj:
  assumes "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> x" and "ys \<noteq> [] \<Longrightarrow> last ys \<noteq> x"
  shows "xs @ replicate m x = ys @ replicate n x \<longleftrightarrow> (xs = ys \<and> m = n)"
proof safe
  from assms have assms': "xs \<noteq> [] \<Longrightarrow> rev xs ! 0 \<noteq> x" "ys \<noteq> [] \<Longrightarrow> rev ys ! 0 \<noteq> x"
    by (auto simp: hd_rev hd_conv_nth[symmetric])
  assume *: "xs @ replicate m x = ys @ replicate n x"
  then have "rev (xs @ replicate m x) = rev (ys @ replicate n x)" ..
  then have "replicate m x @ rev xs = replicate n x @ rev ys" by simp
  then have "take (max m n) (replicate m x @ rev xs) = take (max m n) (replicate n x @ rev ys)" by simp
  then have "replicate m x @ take (max m n - m) (rev xs) =
    replicate n x @ take (max m n - n) (rev ys)" by (auto simp: min_def max_def split: if_splits)
  then have "(replicate m x @ take (max m n - m) (rev xs)) ! min m n =
    (replicate n x @ take (max m n - n) (rev ys)) ! min m n" by simp
  with arg_cong[OF *, of length, simplified] assms' show "m = n"
    by (cases "xs = []" "ys = []" rule: bool.exhaust[case_product bool.exhaust])
      (auto simp: min_def nth_append split: if_splits)
  with * show "xs = ys" by auto
qed

lemma enc_inj[simp]: "#\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow> enc \<AA> = enc \<BB> \<Longrightarrow> \<AA> = \<BB>"
  using MSB_greater
  by transfer (elim exE conjE, hypsubst, unfold prod.case Pair_eq Let_def, elim conjE, simp only:,
    subst (asm) append_replicate_inj,
    erule (2) last_enc_atom_MSB[OF sym sym], erule last_enc_atom_MSB[OF refl refl],
    auto simp: list_eq_iff_nth_eq, (metis less_max_iff_disj)+)

lemma length_enc[simp]: "length (enc \<AA>) = Length \<AA>"
  by transfer (auto simp: Let_def)

lemma in_set_encD[simp]:
  "x \<in> set (enc \<AA>) \<Longrightarrow> #\<^sub>V \<AA> = size_atom x"
  by transfer (auto simp: Let_def split: if_splits)

lemma fin_lift[simp]: "m |\<in>| lift bs i (I ! i) \<longleftrightarrow> (case m of 0 \<Rightarrow> bs ! i | Suc m \<Rightarrow> m |\<in>| I ! i)"
  unfolding lift_def upshift_def by (auto split: nat.splits)

lemma enc_CONS[simp]:
  assumes "#\<^sub>V \<AA> = size_atom x"
  shows "enc (CONS x \<AA>) = x # enc \<AA>"
  using assms by transfer (fastforce simp add: Let_def nth_append nth_Cons
    simp del: upt_conv_Nil diff_is_0_eq' atLeastLessThan_empty
    split: prod.splits nat.splits intro!: nth_equalityI)

lemma ex_Length_0[simp]:
  "\<exists>\<AA>. Length \<AA> = 0 \<and> #\<^sub>V \<AA> = idx"
  by transfer (auto intro!: exI[of _ "replicate m {||}" for m])

lemma is_empty_inj[simp]: "\<lbrakk>Length \<AA> = 0; Length \<BB> = 0; #\<^sub>V \<AA> = #\<^sub>V \<BB>\<rbrakk> \<Longrightarrow> \<AA> = \<BB>"
  by transfer (simp add: list_eq_iff_nth_eq split: prod.splits,
    metis MSB_greater fMax_in less_nat_zero_code)

lemma set_\<sigma>_length_atom[simp]: "(x \<in> set (\<sigma> idx)) \<longleftrightarrow> idx = size_atom x"
  by transfer (auto simp: set_n_lists enum_UNIV image_iff intro!: exI[of _ "I1 @ I2" for I1 I2])

lemma fMin_less_Length[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> fMin (m1\<^bsup>\<AA>\<^esup>k) < Length \<AA>"
  by transfer
    (force elim: order.strict_trans2[OF MSB_greater, rotated -1] intro: fMin_in split: order.splits)

lemma min_Length_fMin[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> min (Length \<AA>) (fMin (m1\<^bsup>\<AA>\<^esup>k)) = fMin (m1\<^bsup>\<AA>\<^esup>k)"
  using fMin_less_Length[of x m1 \<AA> k] unfolding fMin_def by auto

lemma assigns_less_Length[simp]: "x |\<in>| m1\<^bsup>\<AA>\<^esup>k \<Longrightarrow> x < Length \<AA>"
  by transfer (force dest: MSB_greater split: order.splits if_splits)

lemma Length_notin_assigns[simp]: "Length \<AA> |\<notin>| m\<^bsup>\<AA>\<^esup>k"
  by (metis assigns_less_Length less_not_refl)

lemma nth_zero[simp]: "LESS ord m (#\<^sub>V \<AA>) \<Longrightarrow> \<not> split case_order (zero (#\<^sub>V \<AA>)) ord ! m"
  by transfer (auto split: order.splits)

lemma in_fimage_Suc[simp]: "x |\<in>| Suc |`| A \<longleftrightarrow> (\<exists>y. y |\<in>| A \<and> x = Suc y)"
  by blast

lemma fimage_Suc_inj[simp]: "Suc |`| A = Suc |`| B \<longleftrightarrow> A = B"
  by blast

lemma MSB_eq0_D: "MSB I = 0 \<Longrightarrow> x < length I \<Longrightarrow> I ! x = {||}"
  unfolding MSB_def by (auto split: if_splits)

lemma Suc_in_fimage_Suc: "Suc x |\<in>| Suc |`| X \<longleftrightarrow> x |\<in>| X"
  by auto

lemma Suc_in_fimage_Suc_o_Suc[simp]: "Suc x |\<in>| (Suc \<circ> Suc) |`| X \<longleftrightarrow> x |\<in>| Suc |`| X"
  by auto

lemma finsert_same_eq_iff[simp]: "finsert k X = finsert k Y \<longleftrightarrow> X |-| {|k|} = Y |-| {|k|}"
  by auto


lemma fimage_Suc_o_Suc_eq_fimage_Suc_iff[simp]:
  "((Suc \<circ> Suc) |`| X = Suc |`| Y) \<longleftrightarrow> (Suc |`| X = Y)"
  by (metis fimage_Suc_inj fset.map_comp)

lemma fMax_image_Suc[simp]: "x |\<in>| P \<Longrightarrow> fMax (Suc |`| P) = Suc (fMax P)"
  by (rule fMax_eqI) (metis Suc_le_mono fMax_ge fimageE, metis fimageI fempty_iff fMax_in)

lemma len_downshift_helper:
  "x |\<in>| P \<Longrightarrow> Suc (fMax ((\<lambda>x. x - Suc 0) |`| (P |-| {|0|}))) \<noteq> fMax P \<Longrightarrow> xa |\<in>| P \<Longrightarrow> xa = 0"
proof -
  assume a1: "xa |\<in>| P"
  assume a2: "Suc (fMax ((\<lambda>x. x - Suc 0) |`| (P |-| {|0|}))) \<noteq> fMax P"
  have "xa |\<in>| {|0|} \<longrightarrow> xa = 0" by fastforce
  moreover
  { assume "xa |\<notin>| {|0|}"
    hence "0 |\<notin>| P |-| {|0|} \<and> xa |\<notin>| {|0|}" by blast
    then obtain esk1\<^sub>1 :: "nat \<Rightarrow> nat" where "xa = 0" using a1 a2 by (metis Suc_fMax_pred_fimage fMax_Diff_0 fminus_iff not0_implies_Suc) }
  ultimately show "xa = 0" by blast
qed

declare [[goals_limit = 50]]

definition "restrict ord P = (case ord of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True)"
definition "Restrict ord i = (case ord of FO \<Rightarrow> FBase (Q i) | SO \<Rightarrow> FBool True)"

permanent_interpretation WS1S: Word_Formula SUC LESS assigns nvars Extend CONS SNOC Length
  extend size_atom zero eval downshift upshift finsert cut len restrict Restrict
  left_formula0 FV0 find0 wf0 decr0 satisfies0 nullable0 lderiv0 rderiv0 undefined enc \<sigma> ZERO
  defining norm = "Formula_Operations.norm find0 decr0"
  and nFOr = "Formula_Operations.nFOr :: formula \<Rightarrow> _"
  and nFAnd = "Formula_Operations.nFAnd :: formula \<Rightarrow> _"
  and nFNot = "Formula_Operations.nFNot :: formula \<Rightarrow> _"
  and nFEx = "Formula_Operations.nFEx find0 decr0"
  and nFAll = "Formula_Operations.nFAll find0 decr0"
  and decr = "Formula_Operations.decr decr0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and find = "Formula_Operations.find find0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and FV = "Formula_Operations.FV FV0"
  and RESTR = "Formula_Operations.RESTR Restrict"
  and RESTRICT = "Formula_Operations.RESTRICT Restrict FV0"
  and deriv = "\<lambda>d0 (a :: atom) (\<phi> :: formula). Formula_Operations.deriv extend d0 a \<phi>"
  and nullable = "\<lambda>\<phi> :: formula. Formula_Operations.nullable nullable0 \<phi>"
  and fut_default = "Formula.fut_default extend zero rderiv0"
  and fut = "Formula.fut extend zero find0 decr0 rderiv0"
  and finalize = "Formula.finalize SUC extend zero find0 decr0 rderiv0"
  and final = "Formula.final SUC extend zero find0 decr0
     nullable0 rderiv0 :: idx \<Rightarrow> formula \<Rightarrow> _"
  and ws1s_wf = "Formula_Operations.wf SUC (wf0 :: idx \<Rightarrow> ws1s \<Rightarrow> _)"
  and ws1s_left_formula = "Formula_Operations.left_formula left_formula0 :: formula \<Rightarrow> _"
  and check_eqv = "\<lambda>idx. DA.check_eqv (\<sigma> idx)
    (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_left_formula \<phi>)"
  and bounded_check_eqv = "\<lambda>idx. DA.check_eqv (\<sigma> idx)
    (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_left_formula \<phi>)"
  and automaton = "DA.automaton
    (\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi> :: formula))"
proof
  fix k idx and a :: ws1s and l assume "wf0 (SUC k idx) a" "LESS k l (SUC k idx)" "\<not> find0 k l a"
  then show "wf0 idx (decr0 k l a)"
    by (induct a) (unfold wf0.simps decr0.simps find0.simps,
     (transfer, force simp: dec_def split: if_splits order.splits)+)
next
  fix k and a :: ws1s and l assume "left_formula0 a"
  then show "left_formula0 (decr0 k l a)" by (induct a) simp_all
next
  fix i k and a :: ws1s and \<AA> :: interp and P assume "\<not> find0 k i a" "LESS k i (SUC k (#\<^sub>V \<AA>))"
  then show "satisfies0 (Extend k i \<AA> P) a = satisfies0 \<AA> (decr0 k i a)"
    by (induct a) (auto split: if_splits order.splits)
next
  fix idx and a :: ws1s and x assume "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (lderiv0 x a)"
    by (induct rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def split: bool.splits order.splits)
next
  fix a :: ws1s and x assume "left_formula0 a"
  then show "Formula_Operations.left_formula left_formula0 (lderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.left_formula.simps split: bool.splits)
next
  fix idx and a :: ws1s and x assume "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (rderiv0 x a)"
    by (induct rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def split: bool.splits order.splits)
next
  fix \<AA> :: interp and a :: ws1s
  assume "Length \<AA> = 0"
  then show "nullable0 a = satisfies0 \<AA> a"
    by (induct a, unfold wf0.simps nullable0.simps satisfies0.simps Let_def)
      (transfer, (auto 0 2 dest: MSB_greater split: prod.splits if_splits) [])+
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies Extend Length satisfies0 \<AA> (lderiv0 x a) = satisfies0 (CONS x \<AA>) a"
   proof (induct a)
   qed (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (lderiv0 x a) = satisfies0 (CONS x \<AA>) a"
   proof (induct a)
   qed (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0
         \<AA> (rderiv0 x a) = satisfies0 (SNOC x \<AA>) a"
   proof (induct a)
     case Less then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)
   next
     case LessT then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)
   next
     case LessF then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)
   next
     case In then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)+
   next
     case InT then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)+
   qed (auto split: prod.splits)
next
   fix a :: ws1s and \<AA> \<BB> :: interp
   assume "wf0 (#\<^sub>V \<BB>) a" "#\<^sub>V \<AA> = #\<^sub>V \<BB>" "(\<And>m k. LESS k m (#\<^sub>V \<BB>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k)"
     "left_formula0 a"
   then show "satisfies0 \<AA> a \<longleftrightarrow> satisfies0 \<BB> a" by (induct a) simp_all
next
   fix a :: ws1s
   let ?d = "Formula_Operations.deriv extend lderiv0"
   def \<Phi> \<equiv> "\<lambda>a. (case a of
       Q i \<Rightarrow> {FBase (Q i), FBool True}
     | Less i j \<Rightarrow> {FBase (Less i j), FBase (Q j), FBool True, FBool False}
     | LessT i j \<Rightarrow> {FBase (LessT i j), FBool True, FBool False}
     | LessF i j \<Rightarrow> {FBase (LessF i j), FBool True, FBool False}
     | In i I \<Rightarrow> {FBase (In i I), FBool True, FBool False}
     | InT i I \<Rightarrow> {FBase (InT i I), FBool True, FBool False}) :: (ws1s, order) aformula set"
   { fix xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     have "\<forall>a. fold ?d xs (FBase a) \<in> \<Phi> a"
      by (induct xs) (auto split: ws1s.splits bool.splits if_splits, metis+)
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def by (auto split: ws1s.splits)
   ultimately show "finite {fold ?d xs (FBase a) | xs. True}"
     by (blast intro: finite_subset)
next
   fix a :: ws1s
   let ?d = "Formula_Operations.deriv extend rderiv0"
   def \<Phi> \<equiv> "\<lambda>a. (case a of
       Q i \<Rightarrow> {FBase (Q i), FBool True}
     | Less i j \<Rightarrow> {FBase (Less i j), FBase (LessF i j), FBase (LessT i j)}
     | LessT i j \<Rightarrow> {FBase (LessT i j), FBase (LessF i j)}
     | LessF i j \<Rightarrow> {FBase (LessF i j), FBase (LessT i j)}
     | In i I \<Rightarrow> {FBase (In i I), FBase (InT i I)}
     | InT i I \<Rightarrow> {FBase (InT i I), FBase (In i I)}) :: (ws1s, order) aformula set"
   { fix x xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     have "\<forall>a. fold ?d xs (FBase a) \<in> \<Phi> a"
      by (induct xs) (auto split: ws1s.splits bool.splits if_splits, metis+)
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def by (auto split: ws1s.splits)
   ultimately show "finite {fold ?d xs (FBase a) | xs. True}"
     by (blast intro: finite_subset)
next
  fix k l and a :: ws1s
  show "find0 k l a \<longleftrightarrow> (k, l) \<in> set (FV0 a)" by (induct a rule: find0.induct) auto
next
  fix a :: ws1s
  show "distinct (FV0 a)" by (induct a) auto
next
  fix idx a k v
  assume "wf0 idx a" "(k, v) \<in> set (FV0 a)"
  then show "LESS k v idx" by (induct a) auto
next
  fix idx k i
  assume "LESS k i idx"
  then show "Formula_Operations.wf SUC wf0 idx (Restrict k i)"
     unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.wf.simps)
next
  fix k i
  show "Formula_Operations.left_formula left_formula0 (Restrict k i)"
    unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.left_formula.simps)
next
  fix i \<AA> k P
  assume "i\<^bsup>\<AA>\<^esup>k = P"
  then show "restrict k P \<longleftrightarrow>
    Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>_ _ _. True) \<AA> (Restrict k i)"
    unfolding restrict_def Restrict_def
    by (cases k) (auto simp: Formula_Operations.satisfies_gen.simps)
next
  fix i \<AA> k P
  assume "i\<^bsup>\<AA>\<^esup>k = P"
  then show "restrict k P \<longleftrightarrow>
    Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>_ P n. len P \<le> n) \<AA> (Restrict k i)"
    unfolding restrict_def Restrict_def
    by (cases k) (auto simp: Formula_Operations.satisfies_gen.simps)
qed (auto simp: Extend_commute_unsafe downshift_def upshift_def fimage_iff Suc_le_eq len_def
  eval_def cut_def len_downshift_helper
  dest: fMax_ge fMax_ffilter_less fMax_boundedD fsubset_fsingletonD
  split: order.splits if_splits)

(*Workaround for code generation*)
lemma [code]: "check_eqv idx r s =
  ((ws1s_wf idx r \<and> ws1s_left_formula r) \<and> (ws1s_wf idx s \<and> ws1s_left_formula s) \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = final idx q)
    (\<lambda>(p, q). map (\<lambda>a. (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q))) (\<sigma> idx))
    (norm (RESTRICT r), norm (RESTRICT s)) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def WS1S.check_eqv_def ..

definition while where [code del, code_abbrev]: "while idx \<phi> = while_default (fut_default idx \<phi>)"
declare while_default_code[of "fut_default idx \<phi>" for idx \<phi>, folded while_def, code]

export_code check_eqv in SML module_name WS1S_Generated (*file "WS1S_Generated"*)

lemma check_eqv_sound: 
  "\<lbrakk>#\<^sub>V \<AA> = idx; check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S.sat \<AA> \<phi> \<longleftrightarrow> WS1S.sat \<AA> \<psi>)"
  unfolding check_eqv_def by (rule WS1S.check_eqv_soundness)

lemma bounded_check_eqv_sound:
  "\<lbrakk>#\<^sub>V \<AA> = idx; bounded_check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S.sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> WS1S.sat\<^sub>b \<AA> \<psi>)"
  unfolding bounded_check_eqv_def by (rule WS1S.bounded_check_eqv_soundness)

end
