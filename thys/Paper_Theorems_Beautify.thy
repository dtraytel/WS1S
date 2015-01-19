(*<*)
theory Paper_Theorems_Beautify
imports WS1S_Formula
begin

hide_const (open) wf
hide_const (open) Not
no_notation Cons (infixr "#" 65)
no_notation Full ("\<Sigma>\<^sup>*")

type_synonym 'a lang = "'a language"
abbreviation in_language_syn (infix "\<in>" 66) where
  "w \<in> L \<equiv> in_language L w"
abbreviation \<dd>_syn ("(_)\<^sub>_") where
  "(L)\<^sub>a \<equiv> \<dd> L a"
abbreviation star ("_\<^sup>*") where "\<Sigma>\<^sup>* \<equiv> lists (set \<Sigma>)"
type_synonym letter = "bool list \<times> bool list"
type_synonym interp_size = idx
abbreviation "bisim wf \<Sigma> \<iota> \<delta> \<o> \<equiv> DA.check_eqv \<Sigma> \<iota> \<delta> \<o> (\<lambda>s. wf (\<iota> s))"
notation check_eqv ("eqv")
notation bounded_check_eqv ("eqv\<^sub><")
notation Length ("#_" [59] 60)
abbreviation "T \<equiv> FBool True"
abbreviation "F \<equiv> FBool False"
abbreviation "FOV \<phi> \<equiv> {i. (FO, i) \<in> set (FV \<phi>)}"
abbreviation FOassign1 ("_[_]\<^sub>1" [59, 60] 60) where "I[x]\<^sub>1 \<equiv> fset (x\<^bsup>I\<^esup>FO)"
abbreviation FOassign2 ("_[_]\<^sub>2" [59, 60] 60) where "I[x]\<^sub>2 \<equiv> fset (x\<^bsup>I\<^esup>SO)"
abbreviation Extend1as2 (infix "::\<^sub>1\<^sub>a\<^sub>s\<^sub>2" 67) where
  "P ::\<^sub>1\<^sub>a\<^sub>s\<^sub>2 I \<equiv> Extend FO 0 I (Abs_fset P)"
abbreviation Extend1 (infix "::\<^sub>1" 67) where
  "p ::\<^sub>1 I \<equiv> Extend FO 0 I {|p|}"
abbreviation Extend2 (infix "::\<^sub>2" 67) where
  "P ::\<^sub>2 I \<equiv> Extend SO 0 I (Abs_fset P)"
abbreviation Lt (infix "<" 66) where "i < j \<equiv> FBase (Less i j)"
abbreviation Mem (infix "\<in>" 66)  where "i \<in> I \<equiv> FBase (In i I)"
abbreviation Not ("\<not>_") where "Not \<equiv> FNot"
abbreviation Or (infix "\<or>" 66) where "Or \<equiv> FOr"
abbreviation Ex\<^sub>1 ("\<exists>\<^sub>1_") where "Ex\<^sub>1 \<equiv> FEx FO"
abbreviation Ex\<^sub>2 ("\<exists>\<^sub>2_") where "Ex\<^sub>2 \<equiv> FEx SO"
abbreviation Abs_idx_curry ("\<langle>_, _\<rangle>" [59, 60] 1000) where "Abs_idx_curry x y \<equiv> Abs_idx (x, y)"

lemma %invisible fset_empty_iff[simp]: "fset P = {} \<longleftrightarrow> P = {||}"
  by (metis bot_fset.rep_eq fset_inverse)

lemma %invisible satisfies0_singleton_fMin: "\<lbrakk>P \<noteq> {||}; LEQ FO i (#\<^sub>V I)\<rbrakk> \<Longrightarrow>
  satisfies0 (Extend FO i I P) a = satisfies0 (Extend FO i I {|fMin P|}) a"
  by (induct a) auto

lemma %invisible satisfies_gen_singleton_fMin:
  defines "sat \<equiv> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True)"
  shows "LEQ FO i (#\<^sub>V I) \<Longrightarrow> sat (Extend FO i I P) \<phi> =
    sat (Extend FO i I (if P = {||} then {||} else {|fMin P|})) \<phi>"
  apply (split if_splits)
  apply (intro conjI impI)
  apply simp
  apply (rotate_tac -1)
  apply (induct \<phi> arbitrary: i I)
  apply (auto simp add: satisfies0_singleton_fMin[symmetric] sat_def Extend_commute_unsafe split: order.splits)
proof -
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "\<And>i I. LEQ FO i (#\<^sub>V I) \<Longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I P) \<phi>' = Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I {|fMin P|}) \<phi>'"
  assume a2: "LEQ FO ia (#\<^sub>V Ia)"
  assume a3: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia P) Pa) \<phi>'"
  have f4: "\<forall>x\<^sub>0. LEQ FO ia (SUC x\<^sub>0 (#\<^sub>V Ia))" using a2 LESS_SUC(4) SUC_SUC by presburger
  have "\<forall>x\<^sub>0 x\<^sub>1. Extend FO 0 (Extend FO ia Ia x\<^sub>0) x\<^sub>1 = Extend FO (Suc ia) (Extend FO 0 Ia x\<^sub>1) x\<^sub>0" using a2 WS1S.Extend_commute_safe by blast
  thus "\<exists>Pa. Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia {|fMin P|}) Pa) \<phi>'" using a1 a2 a3 f4 by (metis (no_types) LESS_SUC(2) WS1S.Extend_commute_unsafe WS1S.nvars_Extend)
next
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "\<And>i I. LEQ FO i (#\<^sub>V I) \<Longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I P) \<phi>' = Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I {|fMin P|}) \<phi>'"
  assume a2: "LEQ FO ia (#\<^sub>V Ia)"
  assume a3: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia {|fMin P|}) Pa) \<phi>'"
  have f4: "\<forall>x\<^sub>0. LEQ FO ia (SUC x\<^sub>0 (#\<^sub>V Ia))" using a2 LESS_SUC(4) SUC_SUC by presburger
  have "\<forall>x\<^sub>0 x\<^sub>1. Extend FO 0 (Extend FO ia Ia x\<^sub>0) x\<^sub>1 = Extend FO (Suc ia) (Extend FO 0 Ia x\<^sub>1) x\<^sub>0" using a2 WS1S.Extend_commute_safe by blast
  thus "\<exists>Pa. Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia P) Pa) \<phi>'" using a1 a2 a3 f4 by (metis (no_types) LESS_SUC(2) WS1S.Extend_commute_unsafe WS1S.nvars_Extend)
next
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "\<And>i I. LEQ FO i (#\<^sub>V I) \<Longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I P) \<phi>' = Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I {|fMin P|}) \<phi>'"
  assume a2: "LEQ FO ia (#\<^sub>V Ia)"
  assume a3: "\<forall>Pa. Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia P) Pa) \<phi>'"
  have f4: "\<forall>x\<^sub>0. LEQ FO ia (SUC x\<^sub>0 (#\<^sub>V Ia))" using a2 LESS_SUC(4) SUC_SUC by presburger
  have "\<forall>x\<^sub>0 x\<^sub>1. Extend FO 0 (Extend FO ia Ia x\<^sub>0) x\<^sub>1 = Extend FO (Suc ia) (Extend FO 0 Ia x\<^sub>1) x\<^sub>0" using a2 WS1S.Extend_commute_safe by blast
  thus "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia {|fMin P|}) Pa) \<phi>'" using a1 a2 a3 f4 by (metis (no_types) LESS_SUC(2) WS1S.Extend_commute_unsafe WS1S.nvars_Extend)
next
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "\<And>i I. LEQ FO i (#\<^sub>V I) \<Longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I P) \<phi>' = Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend FO i I {|fMin P|}) \<phi>'"
  assume a2: "LEQ FO ia (#\<^sub>V Ia)"
  assume a3: "\<forall>Pa. Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia {|fMin P|}) Pa) \<phi>'"
  have "\<forall>x\<^sub>2 x\<^sub>0 x\<^sub>1. Extend FO x\<^sub>0 (Extend FO ia Ia x\<^sub>1) x\<^sub>2 = Extend FO (Suc ia) (Extend FO x\<^sub>0 Ia x\<^sub>2) x\<^sub>1 \<or> \<not> x\<^sub>0 \<le> ia" using a2 Extend_commute_safe by blast
  thus "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. True) (Extend x1a 0 (Extend FO ia Ia P) Pa) \<phi>'" using a1 a2 a3 by (metis (no_types) LESS_SUC(2) LESS_SUC(4) WS1S.Extend_commute_unsafe WS1S.nvars_Extend le0)
qed

lemma %invisible satisfies_gen_restrict_singleton_fMin:
  defines "sat \<equiv> Formula_Operations.satisfies_gen Extend Length satisfies0
    (\<lambda>k P n. case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True)"
  shows "\<lbrakk>P \<noteq> {||}; LEQ FO i (#\<^sub>V I)\<rbrakk> \<Longrightarrow> sat (Extend FO i I P) \<phi> = sat (Extend FO i I {|fMin P|}) \<phi>"
  by (induct \<phi> arbitrary: i I)
    (auto simp add: satisfies0_singleton_fMin[symmetric] sat_def WS1S.LEQ_SUC Extend_commute_unsafe split: order.splits)

lemma %invisible satisfies_gen_restrict_bounded_singleton_fMin:
  defines "sat \<equiv> Formula_Operations.satisfies_gen Extend Length satisfies0
    (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n)"
  shows "\<lbrakk>P \<noteq> {||}; len P \<le> Length I; LEQ FO i (#\<^sub>V I)\<rbrakk> \<Longrightarrow> sat (Extend FO i I P) \<phi> = sat (Extend FO i I {|fMin P|}) \<phi>"
  apply (induct \<phi> arbitrary: i I)
  apply (auto 0 0 simp add: satisfies0_singleton_fMin[symmetric] sat_def WS1S.LEQ_SUC Extend_commute_unsafe split: order.splits)
(*
  apply (smt2 equalsffemptyD fMax_ge fMin_le le_less_trans len_def less_Suc_eq_le max_def not_le)+
*)
  apply (metis (no_types, lifting) equalsffemptyD le_max_iff_disj len_def max.orderE)
  apply (metis (no_types, lifting) equalsffemptyD le_max_iff_disj len_def max.orderE)
  defer
  apply (metis (no_types, lifting) Suc_leI equalsffemptyD fMax_ge fMin_le leD le_less_trans len_def max_absorb1 not_less_eq)
  apply (metis (no_types, lifting) fMax_ge fMin_le finsert_absorb finsert_not_fempty len_def max.bounded_iff max.order_iff not_less_eq_eq)

proof -
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset" and xa :: nat
  assume a1: "len P \<le> #Ia"
  assume a2: "x |\<in>| P"
  assume a3: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a4: "\<forall>Pa. x1a = FO \<and> (len Pa \<le> max (#Ia) (Suc (fMax P)) \<longrightarrow> Pa = {||} \<or> \<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>') \<or> x1a = SO \<and> (len Pa \<le> max (#Ia) (Suc (fMax P)) \<longrightarrow> \<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>')"
  assume a5: "xa |\<in>| Pa"
  assume a6: "len Pa \<le> max (#Ia) (Suc (fMin P))"
  assume a7: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'"
  have "\<forall>x\<^sub>1. len Pa \<le> max (#Ia) x\<^sub>1" using a1 a2 a6 by (metis (no_types) WS1S.len_add fMin_le finsert_absorb le_max_iff_disj max.order_iff not_less_eq_eq)
  thus False using a3 a4 a5 a7 by blast
next
  fix \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset" and xa :: nat
  assume a1: "len P \<le> #Ia"
  assume a2: "x |\<in>| P"
  assume a3: "\<forall>Pa. Pa \<noteq> {||} \<and> len Pa \<le> max (#Ia) (Suc (fMax P)) \<longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a4: "len Pa \<le> max (#Ia) (Suc (fMin P))"
  assume a5: "\<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a6: "xa |\<in>| Pa"
  have "\<forall>x\<^sub>1. len Pa \<le> max (#Ia) x\<^sub>1" using a1 a2 a4 by (metis (no_types) WS1S.len_add fMin_le finsert_absorb le_max_iff_disj max.order_iff not_less_eq_eq)
  thus False using a3 a5 a6 by blast
next
  fix \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "len P \<le> #Ia"
  assume a2: "x |\<in>| P"
  assume a3: "\<forall>Pa. len Pa \<le> max (#Ia) (Suc (fMax P)) \<longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume "len Pa \<le> max (#Ia) (Suc (fMin P))"
  hence f4: "len Pa \<le> max (Suc (fMin P)) (#Ia)" by (simp add: max.commute)
  have f5: "\<forall>x\<^sub>0. \<not> len x\<^sub>0 \<le> max (Suc (fMax P)) (#Ia) \<or> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>uu uua uub. (case uu of FO \<Rightarrow> uua \<noteq> {||} | SO \<Rightarrow> True) \<and> len uua \<le> uub) (Extend FO ia (Extend SO 0 Ia x\<^sub>0) {|fMin P|}) \<phi>'" using a3 by (simp add: max.commute)
  have "max (Suc (fMin P)) (#Ia) = #Ia" using a1 a2 by (metis WS1S.len_add fMin_le finsert_absorb max.absorb_iff2 max.coboundedI2 max.commute not_less_eq_eq)
  thus "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'" using f4 f5 by (simp add: max.coboundedI2)
next
  fix \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset" and xa :: nat
  assume a1: "len P \<le> #Ia"
  assume a2: "x |\<in>| P"
  assume a3: "\<forall>Pa. Pa \<noteq> {||} \<and> len Pa \<le> max (#Ia) (Suc (fMin P)) \<longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a4: "len Pa \<le> max (#Ia) (Suc (fMax P))"
  assume a5: "\<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a6: "xa |\<in>| Pa"
  have f7: "\<forall>x\<^sub>0. \<not> len x\<^sub>0 \<le> max (Suc (fMin P)) (#Ia) \<or> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>uu uua uub. (case uu of FO \<Rightarrow> uua \<noteq> {||} | SO \<Rightarrow> True) \<and> len uua \<le> uub) (Extend FO (Suc ia) (Extend FO 0 Ia x\<^sub>0) {|fMin P|}) \<phi>' \<or> {||} = x\<^sub>0" using a3 unfolding max.commute by blast
  have "\<forall>x\<^sub>0. len Pa \<le> max x\<^sub>0 (#Ia)" using a1 a2 a4 by (metis (no_types) finsert_absorb finsert_not_fempty len_def max.absorb2 max.coboundedI1 max.commute)
  thus False using a5 a6 f7 by blast
next
  fix \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset"
  assume a1: "x |\<in>| P"
  assume a2: "len P \<le> #Ia"
  assume a3: "len Pa \<le> max (#Ia) (Suc (fMax P))"
  assume a4: "\<forall>Pa. len Pa \<le> max (#Ia) (Suc (fMin P)) \<longrightarrow> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'"
  have "len Pa \<le> max (#Ia) (Suc (fMin P))" using a1 a2 a3 by (metis (no_types) all_not_fin_conv dual_order.trans len_def max.cobounded2 max.commute max.order_iff)
  thus "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'" using a4 by blast
next
  fix x1a :: order and \<phi>' :: "(ws1s, order) aformula" and ia :: nat and Ia :: interp and x :: nat and Pa :: "nat fset" and xa :: nat
  assume a1: "len P \<le> #Ia"
  assume a2: "x |\<in>| P"
  assume a3: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>'"
  assume a4: "\<forall>Pa. x1a = FO \<and> (len Pa \<le> max (#Ia) (Suc (fMin P)) \<longrightarrow> Pa = {||} \<or> \<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO (Suc ia) (Extend FO 0 Ia Pa) {|fMin P|}) \<phi>') \<or> x1a = SO \<and> (len Pa \<le> max (#Ia) (Suc (fMin P)) \<longrightarrow> \<not> Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>')"
  assume a5: "xa |\<in>| Pa"
  assume a6: "len Pa \<le> max (#Ia) (Suc (fMax P))"
  assume a7: "Formula_Operations.satisfies_gen Extend Length satisfies0 (\<lambda>k P n. (case k of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True) \<and> len P \<le> n) (Extend FO ia (Extend SO 0 Ia Pa) {|fMin P|}) \<phi>'"
  have f8: "{||} \<noteq> Pa" using a5 by force
  have "len Pa \<le> #Ia" using a1 a2 a6 by (metis finsert_absorb finsert_not_fempty len_def max.absorb_iff2 max.commute)
  thus False using a3 a4 a7 f8 max.cobounded1 order_trans by blast
qed

abbreviation FO where "FO i \<equiv> FBase (Q i)"
notation WS1S.sat (infix "\<turnstile>" 66)
notation WS1S.sat\<^sub>b (infix "\<turnstile>\<^sub><" 66)

lemma %invisible ws1s_left_formula_triv[simp]: "ws1s_left_formula \<phi> = True"
  by (induct \<phi>) auto

lemma %invisible len_leq_iff: "len P \<le> n \<longleftrightarrow> (\<forall>p \<in> fset P. p < n)"
  unfolding len_def
  by (auto simp: Suc_le_eq fmember.rep_eq[symmetric] Ball_def intro: fMax_boundedD(1) fMax_in)

primrec satisfies :: "interp \<Rightarrow> formula \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "I \<Turnstile> (FBool b) = b"
| "I \<Turnstile> (FBase a) = satisfies0 I a"
| "I \<Turnstile> (FNot \<phi>) = (\<not> I \<Turnstile> \<phi>)"
| "I \<Turnstile> (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = (I \<Turnstile> \<phi>\<^sub>1 \<or> I \<Turnstile> \<phi>\<^sub>2)"
| "I \<Turnstile> (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = (I \<Turnstile> \<phi>\<^sub>1 \<and> I \<Turnstile> \<phi>\<^sub>2)"
| "I \<Turnstile> (FEx k \<phi>) = (case k of WS1S_Formula.FO \<Rightarrow> \<exists>p. p::\<^sub>1I \<Turnstile> \<phi> | SO \<Rightarrow> \<exists>P. finite P \<and> P::\<^sub>2I \<Turnstile> \<phi>)"
| "I \<Turnstile> (FAll k \<phi>) = (case k of WS1S_Formula.FO \<Rightarrow> \<forall>p. p::\<^sub>1I \<Turnstile> \<phi> | SO \<Rightarrow> \<forall>P. finite P \<longrightarrow> P::\<^sub>2I \<Turnstile> \<phi>)"

primrec satisfies_bounded :: "interp \<Rightarrow> formula \<Rightarrow> bool" (infix "\<Turnstile>\<^sub><" 50) where
  "I \<Turnstile>\<^sub>< (FBool b) = b"
| "I \<Turnstile>\<^sub>< (FBase a) = satisfies0 I a"
| "I \<Turnstile>\<^sub>< (FNot \<phi>) = (\<not> I \<Turnstile>\<^sub>< \<phi>)"
| "I \<Turnstile>\<^sub>< (FOr \<phi>\<^sub>1 \<phi>\<^sub>2) = (I \<Turnstile>\<^sub>< \<phi>\<^sub>1 \<or> I \<Turnstile>\<^sub>< \<phi>\<^sub>2)"
| "I \<Turnstile>\<^sub>< (FAnd \<phi>\<^sub>1 \<phi>\<^sub>2) = (I \<Turnstile>\<^sub>< \<phi>\<^sub>1 \<and> I \<Turnstile>\<^sub>< \<phi>\<^sub>2)"
| "I \<Turnstile>\<^sub>< (FEx k \<phi>) = (case k of WS1S_Formula.FO \<Rightarrow> \<exists>p<#I. p::\<^sub>1I \<Turnstile>\<^sub>< \<phi> | SO \<Rightarrow> \<exists>P. (\<forall>p \<in> P. p < #I) \<and> P::\<^sub>2I \<Turnstile>\<^sub>< \<phi>)"
| "I \<Turnstile>\<^sub>< (FAll k \<phi>) = (case k of WS1S_Formula.FO \<Rightarrow> \<forall>p<#I. p::\<^sub>1I \<Turnstile>\<^sub>< \<phi> | SO \<Rightarrow> \<forall>P. (\<forall>p \<in> P. p < #I) \<longrightarrow> P::\<^sub>2I \<Turnstile>\<^sub>< \<phi>)"

lemma %invisible sat_def:
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<turnstile> T \<longleftrightarrow> True"
  "I \<turnstile> F \<longleftrightarrow> False"
  "I \<turnstile> (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<turnstile> (x < y) \<longleftrightarrow>
     Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<turnstile> (x \<in> X) \<longleftrightarrow>
     Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<turnstile> (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<turnstile> \<phi>) \<and> (\<forall>x \<in> FOV (\<not> \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (\<phi> \<or> \<psi>) \<longleftrightarrow>
     (I \<turnstile> \<phi> \<or> I \<turnstile> \<psi>) \<and> (\<forall>x \<in> FOV (\<phi> \<or> \<psi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (FAnd \<phi> \<psi>) \<longleftrightarrow>
     (I \<turnstile> \<phi> \<and> I \<turnstile> \<psi>) \<and> (\<forall>x \<in> FOV (FAnd \<phi> \<psi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow>
     (\<exists>p. p::\<^sub>1I \<turnstile> \<phi>) \<and> (\<forall>x \<in> FOV (\<exists>\<^sub>1 \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow>
     (\<exists>P. finite P \<and> P::\<^sub>2I \<turnstile> \<phi>) \<and> (\<forall>x \<in> FOV (\<exists>\<^sub>2 \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (FAll WS1S_Formula.FO \<phi>) \<longleftrightarrow>
     (\<forall>p. p::\<^sub>1I \<turnstile> \<phi>) \<and> (\<forall>x \<in> FOV (FAll WS1S_Formula.FO \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile> (FAll SO \<phi>) \<longleftrightarrow>
     (\<forall>P. finite P \<longrightarrow> P::\<^sub>2I \<turnstile> \<phi>) \<and> (\<forall>x \<in> FOV (FAll SO \<phi>). I[x]\<^sub>1 \<noteq> {})"
  apply (auto simp: Formula_Operations.sat_def Formula_Operations.FV.simps
     FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits) [8]
     apply (simp_all add: Formula_Operations.sat_def Formula_Operations.FV.simps
       FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits)
     apply (auto 0 2) []
      apply (metis LESS_SUC(1) all_not_fin_conv satisfies_gen_restrict_singleton_fMin)
     apply (metis in_set_remove1 less_irrefl_nat prod.inject)  
    apply (auto 1 0) []
     apply (rule_tac x = "fset P" in exI)
     apply (simp add: fset_inverse)
     apply (metis in_set_remove1 order.distinct(1) prod.inject)
    apply (metis in_set_remove1 order.distinct(1) prod.inject)
   apply (auto 0 2) []
    apply (metis in_set_remove1 less_irrefl_nat prod.inject)
   apply (subst (asm) (2) satisfies_gen_restrict_singleton_fMin)
     apply (auto simp add: gr0_conv_Suc) [3]
  apply (auto 0 0) []
     apply (metis in_set_remove1 order.distinct(1) prod.inject)
    apply (metis in_set_remove1 order.distinct(1) prod.inject)
   apply (drule_tac x = "fset P" in spec)
   apply (simp add: fset_inverse)
  apply (metis finite_fset)
  done

lemma %invisible sat\<^sub>b_def:
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<turnstile>\<^sub>< T \<longleftrightarrow> True"
  "I \<turnstile>\<^sub>< F \<longleftrightarrow> False"
  "I \<turnstile>\<^sub>< (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<turnstile>\<^sub>< (x < y) \<longleftrightarrow>
     Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<turnstile>\<^sub>< (x \<in> X) \<longleftrightarrow>
     Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<turnstile>\<^sub>< (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<turnstile>\<^sub>< \<phi>) \<and> (\<forall>x \<in> FOV (\<not> \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (\<phi> \<or> \<psi>) \<longleftrightarrow>
     (I \<turnstile>\<^sub>< \<phi> \<or> I \<turnstile>\<^sub>< \<psi>) \<and> (\<forall>x \<in> FOV (\<phi> \<or> \<psi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (FAnd \<phi> \<psi>) \<longleftrightarrow>
     (I \<turnstile>\<^sub>< \<phi> \<and> I \<turnstile>\<^sub>< \<psi>) \<and> (\<forall>x \<in> FOV (FAnd \<phi> \<psi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow>
     (\<exists>p. p < #I \<and> p::\<^sub>1I \<turnstile>\<^sub>< \<phi>) \<and> (\<forall>x \<in> FOV (\<exists>\<^sub>1 \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow>
     (\<exists>P. (\<forall>p \<in> P. p < #I) \<and> P::\<^sub>2I \<turnstile>\<^sub>< \<phi>) \<and>
     (\<forall>x \<in> FOV (\<exists>\<^sub>2 \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (FAll WS1S_Formula.FO \<phi>) \<longleftrightarrow>
     (\<forall>p. p < #I \<longrightarrow> p::\<^sub>1I \<turnstile>\<^sub>< \<phi>) \<and> (\<forall>x \<in> FOV (FAll WS1S_Formula.FO \<phi>). I[x]\<^sub>1 \<noteq> {})"
  "I \<turnstile>\<^sub>< (FAll SO \<phi>) \<longleftrightarrow>
     (\<forall>P. (\<forall>p \<in> P. p < #I) \<longrightarrow> P::\<^sub>2I \<turnstile>\<^sub>< \<phi>) \<and> (\<forall>x \<in> FOV (FAll SO \<phi>). I[x]\<^sub>1 \<noteq> {})"
  apply (auto simp: Formula_Operations.sat\<^sub>b_def Formula_Operations.FV.simps
     FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits) [8]
     apply (simp_all add: Formula_Operations.sat\<^sub>b_def Formula_Operations.FV.simps
       FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits)
     apply (auto 0 2) []
      apply (rule_tac x = "fMin P" in exI)
      apply (rule conjI)
       apply (auto simp: len_def not_less split: if_splits) []
       apply (metis fMax_ge fMin_le not_less_eq_eq order.trans)
      apply (subst (asm) satisfies_gen_restrict_bounded_singleton_fMin)
         apply (auto simp add: fmember.rep_eq) [4]
      apply (metis Pair_inject gr0_implies_Suc in_set_remove1 nat.distinct(1))
     apply (rule_tac x = "{|p|}" in exI)
     apply (auto simp: len_def) []
    apply (auto 1 0) []
      apply (rule_tac x = "fset P" in exI)
      apply (auto simp: len_leq_iff fset_inverse) []
      apply (metis (hide_lams) in_set_remove1 order.distinct(1) prod.inject)
     apply (metis (hide_lams) in_set_remove1 order.distinct(1) prod.inject)
    apply (rule_tac x = "Abs_fset P" in exI)
    apply (auto simp: len_leq_iff bounded_nat_set_is_finite Abs_fset_inverse) []
   apply (auto 0 2) []
     apply (drule_tac x = "{|p|}" in spec)
     apply (auto simp: len_def) []
    apply (metis in_set_remove1 less_irrefl_nat prod.inject)
   apply (subst (asm) (2) satisfies_gen_restrict_bounded_singleton_fMin)
      apply (auto simp add: fmember.rep_eq) [4]
   apply (drule_tac x = "fMin P" in spec)
   apply (auto simp: len_def not_less split: if_splits) []
   apply (metis fMax_ge fMin_le not_less_eq_eq order.trans)
  apply (auto 0 0) []
      apply (drule_tac x = "Abs_fset P" in spec)
      apply (auto simp: len_leq_iff bounded_nat_set_is_finite Abs_fset_inverse) []
     apply (metis in_set_remove1 order.distinct(1) prod.inject)
    apply (metis in_set_remove1 order.distinct(1) prod.inject)
   apply (drule_tac x = "fset P" in spec)
   apply (auto simp: len_leq_iff fset_inverse) []
  apply blast
  done

lemma %invisible sat_alt:
  "I \<turnstile> \<phi> \<longleftrightarrow> (I \<Turnstile> \<phi> \<and> (\<forall>x \<in> FOV \<phi>. I[x]\<^sub>1 \<noteq> {}))"
  apply (induct \<phi> arbitrary: I)
  apply (auto simp add: Formula_Operations.sat_def Formula_Operations.FV.simps
     FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits) [2]
  apply (auto simp: sat_def) [3]
   apply (auto 1 0 simp add: sat_def split: order.splits) []
    apply (auto simp: dec_def gr0_conv_Suc) []
    apply (drule_tac x = m in spec)
    apply (auto simp: image_iff split: prod.splits) []
    apply (metis diff_Suc_Suc diff_zero in_set_remove1 nat.distinct(1) prod.inject)
   apply (rule_tac x = P in exI)
   apply auto []
   apply (drule_tac x = x in spec)
   apply (auto 0 2 simp: image_iff split: prod.splits) []
  apply (auto 1 0 simp add: sat_def split: order.splits) []
   apply (auto simp: dec_def gr0_conv_Suc) []
   apply (drule_tac x = m in spec)
   apply (auto simp: image_iff split: prod.splits) []
   apply (metis diff_Suc_Suc diff_zero in_set_remove1 nat.distinct(1) prod.inject)
  apply (drule_tac x = x in spec)
  apply (auto 0 3 simp: image_iff split: prod.splits) []
  done

lemma %invisible sat\<^sub>b_alt:
  "I \<turnstile>\<^sub>< \<phi> \<longleftrightarrow> (I \<Turnstile>\<^sub>< \<phi> \<and> (\<forall>x \<in> FOV \<phi>. I[x]\<^sub>1 \<noteq> {}))"
  apply (induct \<phi> arbitrary: I)
  apply (auto simp add: Formula_Operations.sat\<^sub>b_def Formula_Operations.FV.simps
     FV_def restrict_def dec_def Let_def fMin.rep_eq fmember.rep_eq split: order.splits prod.splits) [2]
  apply (auto simp: sat\<^sub>b_def) [3]
   apply (auto 1 0 simp add: sat\<^sub>b_def split: order.splits) []
    apply (rule_tac x = p in exI)
    apply (auto simp: dec_def gr0_conv_Suc) []
    apply (drule_tac x = m in spec)
    apply (auto simp: image_iff split: prod.splits) []
    apply (metis diff_Suc_Suc diff_zero in_set_remove1 nat.distinct(1) prod.inject)
   apply (rule_tac x = P in exI)
   apply auto []
   apply (drule_tac x = x in spec)
   apply (auto 0 2 simp: image_iff split: prod.splits) []
  apply (auto 1 0 simp add: sat\<^sub>b_def split: order.splits) []
   apply (auto simp: dec_def gr0_conv_Suc) []
   apply (rotate_tac 2)
   apply (drule_tac x = m in spec)
   apply (auto simp: image_iff split: prod.splits) []
   apply (metis diff_Suc_Suc diff_zero in_set_remove1 nat.distinct(1) prod.inject)
  apply (drule_tac x = x in spec)
  apply (auto 0 3 simp: image_iff split: prod.splits) []
  done

notation WS1S.satisfies (infix "\<TTurnstile>" 65)
notation WS1S.satisfies_bounded (infix "\<TTurnstile>\<^sub><" 65)
(*>*)

end
