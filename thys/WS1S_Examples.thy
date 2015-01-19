(*<*)
theory WS1S_Examples
imports WS1S_Formula
begin
(*>*)

section \<open>Examples\<close>

abbreviation (input) FImp where "FImp \<phi> \<psi> \<equiv> FOr (FNot \<phi>) \<psi>"
abbreviation FIff where "FIff \<phi> \<psi> \<equiv> FAnd (FImp \<phi> \<psi>) (FImp \<psi> \<phi>)"
abbreviation FBall where "FBall X \<phi> \<equiv> FAll FO (FImp (FBase (In 0 X)) \<phi>)"

abbreviation SUBSET where "SUBSET X Y \<equiv> FBall X (FBase (In 0 Y))"
abbreviation EQ where "EQ X Y \<equiv> FAnd (SUBSET X Y) (SUBSET Y X)"
abbreviation First where "First x \<equiv> FNot (FEx FO (FBase (Less 0 (x+1))))"
abbreviation Last where "Last x \<equiv> FNot (FEx FO (FBase (Less (x+1) 0)))"
abbreviation Succ where "Succ sucx x \<equiv> FAnd (FBase (Less x sucx)) (FNot (FEx FO (FAnd (FBase (Less (x+1) 0)) (FBase (Less 0 (sucx+1))))))"

definition "Thm idx \<phi> = check_eqv idx \<phi> (FBool True)"

export_code Thm in SML module_name Thm

abbreviation FTrue ("\<top>") where "FTrue \<equiv> FBool True"
abbreviation FFalse ("\<bottom>") where "FFalse \<equiv> FBool False"

notation FImp (infixr "-->" 25)
notation (output) FO ("1")
notation (output) SO ("2")
notation FEx ("\<exists>\<^sub>_ _" [10] 10)
notation FAll ("\<forall>\<^sub>_ _" [10] 10)
notation FNot ("\<not> _" [40] 40)
notation FOr (infixr "\<or>" 30)
notation FAnd (infixr "\<and>" 35)
abbreviation FLess ("x\<^sub>_ < x\<^sub>_" [65, 66] 65) where "FLess m1 m2 \<equiv> FBase (Less m1 m2)"
abbreviation FIn ("x\<^sub>_ \<in> X\<^bsub>_\<^esub>" [65, 66] 65) where "FIn m M \<equiv> FBase (In m M)"
abbreviation FQ ("[x\<^sub>_]" [66] 65) where "FQ m \<equiv> FBase (Q m)"

(*true in M2L, false in WS1S*)
definition "M2L = (FEx SO (FAll FO (FBase (In 0 0))) :: formula)"
(*false in M2L, true in WS1S*)
definition "\<Phi> = (FAll FO (FEx FO (FBase (Less 1 0))) :: formula)"

lemma "Thm (Abs_idx (0, 1)) (FNot M2L)"
  by eval

lemma "Thm (Abs_idx (0, 0)) \<Phi>"
  by eval

abbreviation Globally ("\<box>_" [40] 40) where "Globally P == %n. FAll FO (FImp (FNot (FBase (Less (n+1) 0))) (P 0))"
abbreviation Future ("\<diamondsuit>_" [40] 40) where "Future P == %n. FEx FO (FAnd (FNot (FBase (Less (n+1) 0))) (P 0))"
abbreviation IMP (infixr "\<rightarrow>" 50) where "IMP P1 P2 == %n. FImp (P1 n) (P2 n)"

definition \<Psi> :: "nat \<Rightarrow> formula" where
  "\<Psi> n = FAll FO (((\<box>(foldr (\<lambda>i \<phi>. (\<lambda>m. FBase (In m i)) \<rightarrow> \<phi>) [0..<n] (\<lambda>m. FBase (In m n)))) \<rightarrow>
     foldr (\<lambda>i \<phi>. (\<box>(\<lambda>m. FBase (In m i))) \<rightarrow> \<phi>) [0..<n] (\<box>(\<lambda>m. FBase (In m n)))) 0)"

lemma "Thm (Abs_idx (0, 1)) (\<Psi> 0)" by eval
lemma "Thm (Abs_idx (0, 2)) (\<Psi> 1)" by eval
lemma "Thm (Abs_idx (0, 3)) (\<Psi> 2)" by eval
lemma "Thm (Abs_idx (0, 4)) (\<Psi> 3)" by eval
lemma "Thm (Abs_idx (0, 5)) (\<Psi> 4)" by eval
lemma "Thm (Abs_idx (0, 6)) (\<Psi> 5)" by eval
lemma "Thm (Abs_idx (0, 11)) (\<Psi> 10)" by eval
lemma "Thm (Abs_idx (0, 16)) (\<Psi> 15)" by eval

(*<*)
(*
definition "Thm1 n = (\<lambda>(ws,X). (ws = [], int (card X), X)) (the (WS1S.closure (Abs_idx (0, n + 1)) (norm (\<Psi> n), FBool True)))"

value "Thm1 0"
value "Thm1 1"
value "Thm1 2"
value "Thm1 3"
value "Thm1 4"
value "Thm1 5"
value "Thm1 6"
value "Thm1 7"
value "Thm1 8"
value "Thm1 9"
value "Thm1 10"
value "Thm1 11"
value "Thm1 12"
value "Thm1 13"
value "Thm1 14"
value "Thm1 15"

definition "mod_two a b c d = FIff a (FIff b (FIff c d))"
definition "at_least_two a b c d = FIff d (FOr (FAnd a b) (FOr (FAnd b c) (FAnd a c)))"

definition "ADD S A B = FEx SO (FAnd (FAll FO (FImp (First 0) (FNot (FBase (In 0 0)))))
  (FAll FO (FAnd (mod_two (FBase (In 0 (A+1))) (FBase (In 0 (B+1))) (FBase (In 0 0)) (FBase (In 0 (S+1))))
       ((FImp (FEx FO (FAnd (Last 0) (FBase (Less 1 0)))))
            (at_least_two (FBase (In 0 (A+1))) (FBase (In 0 (B+1))) (FBase (In 0 0)) (FAll FO (FImp (Succ 0 1) (FBase (In 0 0)))))))))"

lemma Comm_Test: "check_eqv (Abs_idx (0, 3)) (ADD 0 1 2) (ADD 1 0 2)"
  by eval

abbreviation transition ("\"_\" -> \"_\" [label=\"_\"];")
  where "transition from to lab \<equiv> ((from, lab), to)"

value "WS1S.automaton (\<sigma> (Abs_idx (0, 0))) M2L"

*)

end
(*>*)
