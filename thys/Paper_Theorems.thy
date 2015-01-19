(*<*)
theory Paper_Theorems
imports Paper_Theorems_Beautify
begin
(*>*)

lemma
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<Turnstile> T \<longleftrightarrow> True"
  "I \<Turnstile> F \<longleftrightarrow> False"
  "I \<Turnstile> (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<Turnstile> (x < y) \<longleftrightarrow> Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<Turnstile> (x \<in> X) \<longleftrightarrow> Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<Turnstile> (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<Turnstile> \<phi>)"
  "I \<Turnstile> (\<phi> \<or> \<psi>) \<longleftrightarrow> (I \<Turnstile> \<phi> \<or> I \<Turnstile> \<psi>)"
  "I \<Turnstile> (FAnd \<phi> \<psi>) \<longleftrightarrow> (I \<Turnstile> \<phi> \<and> I \<Turnstile> \<psi>)"
  "I \<Turnstile> (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow> (\<exists>P. finite P \<and> P::\<^sub>1\<^sub>a\<^sub>s\<^sub>2I \<Turnstile> \<phi>)"
  "I \<Turnstile> (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow> (\<exists>P. finite P \<and> P::\<^sub>2I \<Turnstile> \<phi>)"
  by (auto 0 2 simp: Let_def fMin.rep_eq fmember.rep_eq
    fset_inverse intro: exI[of _ "fset P" for P])

lemma
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<Turnstile>\<^sub>< T \<longleftrightarrow> True"
  "I \<Turnstile>\<^sub>< F \<longleftrightarrow> False"
  "I \<Turnstile>\<^sub>< (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<Turnstile>\<^sub>< (x < y) \<longleftrightarrow> Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<Turnstile>\<^sub>< (x \<in> X) \<longleftrightarrow> Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<Turnstile>\<^sub>< (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<Turnstile>\<^sub>< \<phi>)"
  "I \<Turnstile>\<^sub>< (\<phi> \<or> \<psi>) \<longleftrightarrow> (I \<Turnstile>\<^sub>< \<phi> \<or> I \<Turnstile>\<^sub>< \<psi>)"
  "I \<Turnstile>\<^sub>< (FAnd \<phi> \<psi>) \<longleftrightarrow> (I \<Turnstile>\<^sub>< \<phi> \<and> I \<Turnstile>\<^sub>< \<psi>)"
  "I \<Turnstile>\<^sub>< (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow> (\<exists>P. (\<forall>p \<in> P. p <# I) \<and> P::\<^sub>1\<^sub>a\<^sub>s\<^sub>2I \<Turnstile>\<^sub>< \<phi>)"
  "I \<Turnstile>\<^sub>< (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow> (\<exists>P. (\<forall>p \<in> P. p <# I) \<and> P::\<^sub>2I \<Turnstile>\<^sub>< \<phi>)"
  by (auto 0 2 simp: Let_def fMin.rep_eq fmember.rep_eq
    len_leq_iff Abs_fset_inverse bounded_nat_set_is_finite fset_inverse
    elim: exI[of _ "Abs_fset P" for P, OF conjI, rotated])

lemma
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<TTurnstile> T \<longleftrightarrow> True"
  "I \<TTurnstile> F \<longleftrightarrow> False"
  "I \<TTurnstile> (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<TTurnstile> (x < y) \<longleftrightarrow> Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<TTurnstile> (x \<in> X) \<longleftrightarrow> Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<TTurnstile> (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<TTurnstile> \<phi>)"
  "I \<TTurnstile> (\<phi> \<or> \<psi>) \<longleftrightarrow> (I \<TTurnstile> \<phi> \<or> I \<TTurnstile> \<psi>)"
  "I \<TTurnstile> (FAnd \<phi> \<psi>) \<longleftrightarrow> (I \<TTurnstile> \<phi> \<and> I \<TTurnstile> \<psi>)"
  "I \<TTurnstile> (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow> (\<exists>p. p::\<^sub>1I \<TTurnstile> \<phi>)"
  "I \<TTurnstile> (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow> (\<exists>P. finite P \<and> P::\<^sub>2I \<TTurnstile> \<phi>)"
  by (auto simp add: Let_def fMin.rep_eq fmember.rep_eq)

lemma
  fixes I :: interp
  and x y X :: nat
  and \<phi> \<psi> :: formula
  shows
  "I \<TTurnstile>\<^sub>< T \<longleftrightarrow> True"
  "I \<TTurnstile>\<^sub>< F \<longleftrightarrow> False"
  "I \<TTurnstile>\<^sub>< (FO x) \<longleftrightarrow> I[x]\<^sub>1 \<noteq> {}"
  "I \<TTurnstile>\<^sub>< (x < y) \<longleftrightarrow> Min (I[x]\<^sub>1) < Min (I[y]\<^sub>1) \<and> I[x]\<^sub>1 \<noteq> {} \<and> I[y]\<^sub>1 \<noteq> {}"
  "I \<TTurnstile>\<^sub>< (x \<in> X) \<longleftrightarrow> Min (I[x]\<^sub>1) \<in> I[X]\<^sub>2 \<and> I[x]\<^sub>1 \<noteq> {} \<and> finite (I[X]\<^sub>2)"
  "I \<TTurnstile>\<^sub>< (\<not> \<phi>) \<longleftrightarrow> \<not> (I \<TTurnstile>\<^sub>< \<phi>)"
  "I \<TTurnstile>\<^sub>< (\<phi> \<or> \<psi>) \<longleftrightarrow> (I \<TTurnstile>\<^sub>< \<phi> \<or> I \<TTurnstile>\<^sub>< \<psi>)"
  "I \<TTurnstile>\<^sub>< (\<exists>\<^sub>1 \<phi>) \<longleftrightarrow> (\<exists>p <# I. p::\<^sub>1I \<TTurnstile>\<^sub>< \<phi>)"
  "I \<TTurnstile>\<^sub>< (\<exists>\<^sub>2 \<phi>) \<longleftrightarrow> (\<exists>P. (\<forall>p \<in> P. p <# I) \<and> P::\<^sub>2I \<TTurnstile>\<^sub>< \<phi>)"
  by (auto simp add: Let_def fMin.rep_eq fmember.rep_eq)
   

abbreviation bisimilar (infix "\<sim>" 65) where
  "L \<sim> K \<equiv> (\<exists>R. R L K \<and> (\<forall>L' K'. R L' K' \<longrightarrow>
     (([] \<in> L' \<longleftrightarrow> [] \<in> K') \<and> (\<forall>a. R (L')\<^sub>a (K')\<^sub>a))))"

theorem Theorem1:
  fixes L K :: "'a language"
  shows "L \<sim> K \<Longrightarrow> L = K"
  by (coinduction arbitrary: K L) auto

lemma Lemma2:
  fixes \<Sigma> :: "'a list"
  and L :: "'t \<Rightarrow> 'a language"
  and L' :: "'s \<Rightarrow> 'a language"
  and \<iota> :: "'s \<Rightarrow> 't"
  and \<delta> :: "'a \<Rightarrow> 't \<Rightarrow> 't"
  and \<o> :: "'t \<Rightarrow> bool"
  and wf :: "'t \<Rightarrow> bool"
  assumes "\<And>s w. wf s \<Longrightarrow> w \<in> L s \<Longrightarrow> w \<in> \<Sigma>\<^sup>*"
  and "\<And>t. L (\<iota> t) = L' t"
  and "\<And>s a. wf s \<Longrightarrow> a \<in> set \<Sigma> \<Longrightarrow> wf (\<delta> a s)"
  and "\<And>s a. wf s \<Longrightarrow> a \<in> set \<Sigma> \<Longrightarrow> L (\<delta> a s) = (L s)\<^sub>a"
  and "\<And>s. wf s \<Longrightarrow> \<o> s \<longleftrightarrow> [] \<in> L s"
  and "\<And>s. wf s \<Longrightarrow> finite {fold \<delta> w s |w. w \<in> \<Sigma>\<^sup>*}"
  and "wf (\<iota> s)" "wf (\<iota> s')"
  shows "bisim wf \<Sigma> \<iota> \<delta> \<o> s s' \<longleftrightarrow> L' s = L' s'"
proof -
  interpret D: DFA \<Sigma> \<iota> \<delta> \<o> wf "\<lambda>s. wf (\<iota> s)" L L'
    using assms by unfold_locales auto
  show "bisim wf \<Sigma> \<iota> \<delta> \<o> s s' \<longleftrightarrow> L' s = L' s'" by (auto intro: D.soundness D.completeness assms)
qed


(*<*)
notation final ("\<o>")
notation nullable ("\<o>\<^sub><")
notation ws1s_wf ("wf")
no_notation norm_ACI ("\<langle>_\<rangle>")
notation norm_ACI ("|_|\<^sub>A\<^sub>C\<^sub>I")
notation size_atom ("|_|")
abbreviation "\<delta> \<equiv> deriv lderiv0"
abbreviation "\<rho> \<equiv> deriv rderiv0"
hide_const (open) fut
abbreviation futurize where "futurize \<equiv> WS1S_Formula.fut True"
abbreviation finalize_syn ("\<lfloor>_\<rfloor>\<^bsub>_\<^esub>") where "\<lfloor>\<phi>\<rfloor>\<^bsub>n\<^esub> \<equiv> finalize n \<phi>"
(*>*)


lemma Theorem3:
  fixes \<phi> :: formula
  and I :: interp
  and a :: "bool list \<times> bool list"
  assumes "wf (#\<^sub>V I) \<phi>"
  and "#\<^sub>V I = |a|"
  shows "I \<Turnstile> \<delta> a \<phi> \<longleftrightarrow> CONS a I \<Turnstile> \<phi>"
  and "I \<Turnstile>\<^sub>< \<delta> a \<phi> \<longleftrightarrow> CONS a I \<Turnstile>\<^sub>< \<phi>"
  by (rule WS1S.satisfies_lderiv[OF assms], rule WS1S.satisfies_bounded_lderiv[OF assms])

lemma Theorem4:
  fixes \<phi> :: formula
  shows "finite { |fold \<delta> xs \<phi>|\<^sub>A\<^sub>C\<^sub>I | xs. True}"
  by (blast intro: WS1S.finite_fold_deriv)

lemma Example1:
  shows "|\<delta> ([False], []) (Ex\<^sub>2 (0 \<in> 0))|\<^sub>A\<^sub>C\<^sub>I = Ex\<^sub>2 (0  \<in> 0)"
  and "|\<delta> ([True], []) (Ex\<^sub>2 (0 \<in> 0))|\<^sub>A\<^sub>C\<^sub>I = Ex\<^sub>2 (F \<or> T)"
  and "|\<delta> ([False], []) (Ex\<^sub>2 (F \<or> T))|\<^sub>A\<^sub>C\<^sub>I = Ex\<^sub>2 (F \<or> T)"
  and "|\<delta> ([True], []) (Ex\<^sub>2 (F \<or> T))|\<^sub>A\<^sub>C\<^sub>I = Ex\<^sub>2 (F \<or> T)"
  by eval+

lemma Theorem5:
  fixes \<phi> :: formula
  shows "finite { |fold \<rho> xs \<phi>|\<^sub>A\<^sub>C\<^sub>I | xs. True}"
  by (blast intro: WS1S.finite_fold_deriv)

lemma Theorem6:
  fixes \<phi> :: formula
  and I :: interp
  and a :: "bool list \<times> bool list"
  assumes "wf (#\<^sub>V I) \<phi>"
  and "#\<^sub>V I = |a|"
  shows "I \<Turnstile>\<^sub>< \<rho> a \<phi> \<longleftrightarrow> SNOC a I \<Turnstile>\<^sub>< \<phi>"
  by (rule WS1S.satisfies_bounded_rderiv[OF assms])

lemma Theorem71:
  fixes \<phi> :: formula
  and I :: interp
  assumes "wf (#\<^sub>V I) \<phi>" 
  and "#I = 0"
  shows "\<o>\<^sub>< \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>< \<phi>"
  using assms by (auto simp: WS1S.nullable_satisfies_bounded)

lemma Theorem72:
  fixes \<phi> :: formula
  and I :: interp
  assumes "wf (#\<^sub>V I) \<phi>" 
  shows "I \<Turnstile>\<^sub>< futurize (#\<^sub>V I) \<phi> \<longleftrightarrow>
    (\<exists>k. (SNOC (zero (#\<^sub>V I)) ^^ k) I \<Turnstile>\<^sub>< \<phi>)"
  using assms by (auto simp: WS1S.satisfies_bounded_fut)

lemma Theorem73:
  fixes \<phi> :: formula
  and I :: interp
  assumes "wf (#\<^sub>V I) \<phi>" 
  shows "I \<Turnstile>\<^sub>< \<lfloor>\<phi>\<rfloor>\<^bsub>(#\<^sub>V I)\<^esub> \<longleftrightarrow> I \<Turnstile> \<phi>"
  using assms by (auto simp: WS1S.finalize_satisfies)

lemma Theorem74:
  fixes \<phi> :: formula
  and I :: interp
  assumes "wf (#\<^sub>V I) \<phi>" 
  and "#I = 0"
  shows "\<o> (#\<^sub>V I) \<phi> \<longleftrightarrow> I \<Turnstile> \<phi>"
  using assms by (auto simp: WS1S.final_satisfies)

(*<*)
notation WS1S.language ("L")
notation WS1S.language\<^sub>b ("L\<^sub><")
(*>*)


lemma language_def:
  "L n \<phi> = {enc I | I. I \<TTurnstile> \<phi> \<and> (\<forall>x\<in>FOV \<phi>. I[x]\<^sub>1 \<noteq> {}) \<and> #\<^sub>V I = n}"
  "L\<^sub>< n \<phi> = {enc I | I. I \<TTurnstile>\<^sub>< \<phi> \<and> (\<forall>x\<in>FOV \<phi>. I[x]\<^sub>1 \<noteq> {}) \<and> #\<^sub>V I = n}"
  unfolding WS1S.language_def WS1S.language\<^sub>b_def sat_alt sat\<^sub>b_alt by simp_all

lemma Theorem8:
  fixes \<phi> \<psi> :: formula
  and n :: interp_size
  shows "eqv n \<phi> \<psi> \<Longrightarrow> L n \<phi> = L n \<psi>"
  and "eqv\<^sub>< n \<phi> \<psi> \<Longrightarrow> L\<^sub>< n \<phi> = L\<^sub>< n \<psi>"
  unfolding check_eqv_def bounded_check_eqv_def
  by (drule WS1S.soundness, erule injD[OF bij_is_inj[OF to_language_bij]])
     (drule WS1S.bounded.soundness, erule injD[OF bij_is_inj[OF to_language_bij]])

lemma Example2:
  shows "eqv \<langle>1, 0\<rangle> (Ex\<^sub>2 (0 \<in> 0)) (FO 0)"
  by eval

(*<*)
end
(*>*)
