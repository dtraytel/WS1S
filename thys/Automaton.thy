(*  Author: Dmitriy Traytel *)

header "Equivalence Framework"

(*<*)
theory Automaton
imports
  "~~/src/HOL/Library/While_Combinator"
  "$AFP/Coinductive_Languages/Coinductive_Language"
begin
(*>*)

abbreviation "\<dd>s \<equiv> fold (\<lambda>a L. \<dd> L a)"

lemma in_language_\<dd>s: "in_language (\<dd>s w L) v \<longleftrightarrow> in_language L (w @ v)"
  by (induct w arbitrary: L) simp_all

lemma \<oo>_\<dd>s: "\<oo> (\<dd>s w L) \<longleftrightarrow> in_language L w"
  by (induct w arbitrary: L) auto

lemma in_language_to_language[simp]: "in_language (to_language L) w \<longleftrightarrow> w \<in> L"
  by (metis in_language_to_language mem_Collect_eq)

lemma rtrancl_fold_product:
shows "{((r, s), (f a r, f a s)) | a r s. a \<in> A}^* =
       {((r, s), (fold f w r, fold f w s)) | w r s. w \<in> lists A}" (is "?L = ?R")
proof-
  { fix r s r' s'
    have "((r, s), (r', s')) : ?L \<Longrightarrow> ((r, s), (r', s')) \<in> ?R"
    proof(induction rule: converse_rtrancl_induct2)
      case refl show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  } moreover
  { fix r s r' s'
    { fix w assume "w \<in> lists A"
      then have "((r, s), fold f w r, fold f w s) \<in> ?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (force elim!: rtrancl_into_rtrancl)
      qed
    }
    hence "((r, s), (r', s')) \<in> ?R \<Longrightarrow> ((r, s), (r', s')) \<in> ?L" by auto
  } ultimately show ?thesis by (auto 10 0)
qed

lemma rtrancl_fold_product1:
shows "{(r, s). \<exists>a \<in> A. s = f a r}^* = {(r, s). \<exists>a \<in> lists A. s = fold f a r}" (is "?L = ?R")
proof-
  { fix r s
    have "(r, s) \<in> ?L \<Longrightarrow> (r, s) \<in> ?R"
    proof(induction rule: converse_rtrancl_induct)
      case base show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  } moreover
  { fix r s
    { fix w assume "w \<in> lists A"
      then have "(r, fold f w r) \<in> ?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (force elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "(r, s) \<in> ?R \<Longrightarrow> (r, s) \<in> ?L" by auto
  } ultimately show ?thesis by (auto 10 0)
qed

lemma lang_eq_ext_Nil_fold_Deriv:
  fixes K L A
  assumes "\<And>w. in_language K w \<Longrightarrow> w \<in> lists A" "\<And>w. in_language L w \<Longrightarrow> w \<in> lists A"
  defines "\<BB> \<equiv> {(\<dd>s w K, \<dd>s w L) | w. w \<in> lists A}"
  shows "K = L \<longleftrightarrow> (\<forall>(K, L) \<in> \<BB>. \<oo> K \<longleftrightarrow> \<oo> L)"
proof
  assume "\<forall>(K, L)\<in>\<BB>. \<oo> K = \<oo> L"
  then show "K = L"
  unfolding \<BB>_def using assms(1,2)
  proof (coinduction arbitrary: K L)
    case (Lang K L)
    then have CIH: "\<And>K' L'. \<exists>w. K' = \<dd>s w K \<and> L' = \<dd>s w L \<and> w \<in> lists A \<Longrightarrow> \<oo> K' = \<oo> L'" and
      [dest, simp]: "\<And>w. in_language K w \<Longrightarrow> w \<in> lists A" "\<And>w. in_language L w \<Longrightarrow> w \<in> lists A" 
      by blast+
    show ?case unfolding ex_simps simp_thms
    proof (safe del: iffI)
      show "\<oo> K = \<oo> L" by (intro CIH[OF exI[where x = "[]"]]) simp
    next
      fix x w assume "\<forall>x\<in>set w. x \<in> A"
      then show "\<oo> (\<dd>s w (\<dd> K x)) = \<oo> (\<dd>s w (\<dd> L x))"
      proof (cases "x \<in> A")
        assume "x \<notin> A"
        then show ?thesis unfolding in_language_\<dd>s in_language.simps[symmetric] by fastforce
      qed (intro CIH[OF exI[where x = "x # w"]], auto)
    qed (auto simp add: in_language.simps[symmetric] simp del: in_language.simps)
  qed
qed (auto simp: \<BB>_def)

subsection \<open>Abstract Deterministic Automaton\<close>

locale DA =
fixes alphabet :: "'a list"
fixes init :: "'t \<Rightarrow> 's"
fixes delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes accept :: "'s \<Rightarrow> bool"
fixes wellformed :: "'s \<Rightarrow> bool"
fixes wf :: "'t \<Rightarrow> bool"
fixes Language :: "'s \<Rightarrow> 'a language"
fixes Lang :: "'t \<Rightarrow> 'a language"
assumes Language_init: "Language (init t) = Lang t"
assumes wellformed_init: "wf t \<Longrightarrow> wellformed (init t)"
assumes Language_alphabet: "\<lbrakk>wellformed s; in_language (Language s) w\<rbrakk> \<Longrightarrow> w \<in> lists (set alphabet)"
assumes wellformed_delta: "\<lbrakk>wellformed s; a \<in> set alphabet\<rbrakk> \<Longrightarrow> wellformed (delta a s)"
assumes Language_delta: "\<lbrakk>wellformed s; a \<in> set alphabet\<rbrakk> \<Longrightarrow> Language (delta a s) = \<dd> (Language s) a"
assumes accept_Language: "wellformed s \<Longrightarrow> accept s \<longleftrightarrow> \<oo> (Language s)"
begin

lemma wellformed_deltas: "\<lbrakk>wellformed s; w \<in> lists (set alphabet)\<rbrakk> \<Longrightarrow>
  wellformed (fold delta w s)"
  by (induction w arbitrary: s) (auto simp add: Language_delta wellformed_delta)

lemma Language_deltas: "\<lbrakk>wellformed s; w \<in> lists (set alphabet)\<rbrakk> \<Longrightarrow>
  Language (fold delta w s) = \<dd>s w (Language s)"
  by (induction w arbitrary: s) (auto simp add: Language_delta wellformed_delta)

abbreviation closure :: "'s * 's \<Rightarrow> (('s * 's) list * ('s * 's) set) option" where
  "closure \<equiv> rtrancl_while (\<lambda>(p, q). accept p = accept q)
    (\<lambda>(p, q). map (\<lambda>a. (delta a p, delta a q)) alphabet)"

theorem closure_sound_complete:
assumes wf: "wf r" "wf s"
and result: "closure (init r, init s) = Some (ws, R)" (is "closure (?r, ?s) = _")
shows "ws = [] \<longleftrightarrow> Lang r = Lang s"
proof -
  from wf have wellformed: "wellformed ?r" "wellformed ?s" using wellformed_init by blast+
  note Language_alphabets[simp] =
    Language_alphabet[OF wellformed(1)] Language_alphabet[OF wellformed(2)]
  note Language_deltass = Language_deltas[OF wellformed(1)] Language_deltas[OF wellformed(2)]

  have bisim: "(Language ?r = Language ?s) =
    (\<forall>a b. (\<exists>w. a = \<dd>s w (Language ?r) \<and> b = \<dd>s w (Language ?s) \<and> w \<in> lists (set alphabet)) \<longrightarrow>
    \<oo> a = \<oo> b)"
    by (subst lang_eq_ext_Nil_fold_Deriv) auto

  have leq: "(Language ?r = Language ?s) =
  (\<forall>(r', s') \<in> {((r, s), (delta a r, delta a s)) | a r s. a \<in> set alphabet}^* `` {(?r, ?s)}.
    accept r' = accept s')" using Language_deltass
      accept_Language[OF wellformed_deltas[OF wellformed(1)]]
      accept_Language[OF wellformed_deltas[OF wellformed(2)]]
      unfolding rtrancl_fold_product in_lists_conv_set bisim
      by (auto 10 0)
  have "{(x,y). y \<in> set ((\<lambda>(p,q). map (\<lambda>a. (delta a p, delta a q)) alphabet) x)} =
    {((r, s), (delta a r, delta a s)) | a r s. a \<in> set alphabet}" by auto
  with rtrancl_while_Some[OF result]
  have "(ws = []) = (Language ?r = Language ?s)" by (auto simp add: leq Ball_def split: if_splits)
  then show ?thesis unfolding Language_init .
qed

subsection \<open>The overall procedure\<close>

definition check_eqv :: "'t \<Rightarrow> 't \<Rightarrow> bool" where
"check_eqv r s = (wf r \<and> wf s \<and> (case closure (init r, init s) of Some([], _) \<Rightarrow> True | _ \<Rightarrow> False))"

lemma soundness: 
assumes "check_eqv r s" shows "Lang r = Lang s"
proof -
  obtain R where "wf r" "wf s" "closure (init r, init s) = Some([], R)"
    using assms by (auto simp: check_eqv_def Let_def split: option.splits list.splits)
  from closure_sound_complete[OF this] show "Lang r = Lang s" by simp
qed

(* completeness needs termination of closure, otherwise result could be None *)

text\<open>Auxiliary functions:\<close>
definition reachable :: "'a list \<Rightarrow> 's \<Rightarrow> 's set" where
  "reachable as s = snd (the (rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) s))"

definition automaton :: "'a list \<Rightarrow> 's \<Rightarrow> (('s * 'a) * 's) set" where
  "automaton as s =
    snd (the
    (let start = (([s], {s}), {});
         test = \<lambda>((ws, Z), A). ws \<noteq> [];
         step = \<lambda>((ws, Z), A).
           (let s = hd ws;
                new_edges = map (\<lambda>a. ((s, a), delta a s)) as;
                new = remdups (filter (\<lambda>ss. ss \<notin> Z) (map snd new_edges))
           in ((new @ tl ws, set new \<union> Z), set new_edges \<union> A))
    in while_option test step start))"

definition match :: "'s \<Rightarrow> 'a list \<Rightarrow> bool" where
  "match s w = accept (fold delta w s)"

lemma match_correct:
  assumes "wellformed s" "w \<in> lists (set alphabet)"
  shows "match s w \<longleftrightarrow> in_language (Language s) w"
  unfolding match_def accept_Language[OF wellformed_deltas[OF assms]] Language_deltas[OF assms] \<oo>_\<dd>s ..

end

subsection \<open>Abstract Deterministic Finite Automaton\<close>

locale DFA = DA +
assumes fin: "wellformed s \<Longrightarrow> finite {fold delta w s | w. w \<in> lists (set alphabet)}"
begin

lemma finite_rtrancl_delta_Image:
  "\<lbrakk>wellformed r; wellformed s\<rbrakk> \<Longrightarrow>
  finite ({((r, s), (delta a r, delta a s))| a r s. a \<in> set (alphabet)}^* `` {(r, s)})"
  unfolding rtrancl_fold_product Image_singleton
  by (auto intro: finite_subset[OF _ finite_cartesian_product[OF fin fin]])

lemma "termination":
  assumes "wellformed r" "wellformed s"
  shows "\<exists>st. closure (r, s) = Some st" (is "\<exists>_. closure  ?i = _")
proof (rule rtrancl_while_finite_Some)
  show "finite ({(x, st). st \<in> set ((\<lambda>(p,q). map (\<lambda>a. (delta a p, delta a q)) alphabet) x)}\<^sup>* `` {?i})"
    by (rule finite_subset[OF Image_mono[OF rtrancl_mono] finite_rtrancl_delta_Image[OF assms]]) auto
qed

lemma completeness: 
assumes "wf r" "wf s" "Lang r = Lang s" shows "check_eqv r s"
proof -
  obtain ws R where 1: "closure (init r, init s) = Some (ws, R)" using "termination"
    wellformed_init assms by fastforce
  with closure_sound_complete[OF _ _ this] assms
  show "check_eqv r s" by (simp add: check_eqv_def Language_alphabet)
qed

lemma finite_rtrancl_delta_Image1:
  "wellformed r \<Longrightarrow> finite ({(r, s). \<exists>a \<in> set alphabet. s = delta a r}^* `` {r})"
  unfolding rtrancl_fold_product1 by (auto intro: finite_subset[OF _ fin])

lemma
  assumes "wellformed r" "set as \<subseteq> set alphabet"
  shows reachable: "reachable as r = {fold delta w r | w. w \<in> lists (set as)}"
  and finite_reachable: "finite (reachable as r)"
proof -
  obtain wsZ where *: "rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) r = Some wsZ"
    using assms by (atomize_elim, intro rtrancl_while_finite_Some Image_mono rtrancl_mono
      finite_subset[OF _ finite_rtrancl_delta_Image1[of r]]) auto
  then show "reachable as r = {fold delta w r | w. w \<in> lists (set as)}"
    unfolding reachable_def by (cases wsZ)
      (auto dest!: rtrancl_while_Some split: if_splits simp: rtrancl_fold_product1 image_iff)
  then show "finite (reachable as r)" using assms by (force intro: finite_subset[OF _ fin])
qed
  
end

(*<*)
end
(*>*)
