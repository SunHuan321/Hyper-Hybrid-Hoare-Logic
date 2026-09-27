
theory Lander1
  imports ContinuousInvHHL ComplementlemmaHHL H3L_Oracle.HybridOracle
begin

text \<open>Numerical facts about the lander invariant are delegated to the
oracle layer (\<^theory_text>\<open>HybridOracle\<close>); \<open>landerinv_prop2\<close> below is an
alias so the downstream proofs are unchanged.\<close>

text \<open>Variables\<close>

definition Fc :: char where "Fc = CHR ''a''"
definition M :: char where "M = CHR ''b''"
definition T :: char where "T = CHR ''c''"
definition V :: char where "V = CHR ''d''"
definition W :: char where "W = CHR ''e''"

text \<open>Constants\<close>
text \<open>\<^term>\<open>Period\<close>, \<^term>\<open>W_upd\<close>, \<^term>\<open>landerinv\<close> come from
\<^theory_text>\<open>HybridOracle\<close>.\<close>

lemmas landerinv_prop2 = HybridOracle.oracle_Lander_discrete_step

lemma train_vars_distinct [simp]: "T \<noteq> V" "T \<noteq> W"
                                  "V \<noteq> T" "V \<noteq> W"
                                  "W \<noteq> T" "W \<noteq> V"
  unfolding T_def V_def W_def by auto

definition landerInv :: "state \<Rightarrow> real" where
  "landerInv s = landerinv (s T) (s V) (s W)"

text \<open>Processes\<close>

(*
  V ::= (\<lambda>_. -1.5);
  W ::= (\<lambda>_. 2835/759.5);
*)
definition P0 :: proc where
  "P0 =
    Rep (
      T ::= (\<lambda>_. 0);
      Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                           W := (\<lambda>s. (s W)^2 / 2500 ),
                           T := (\<lambda>_. 1)))) ((\<lambda>s. s T < Period));
      W ::= (\<lambda>s. W_upd (s V) (s W))
    )"

fun P0_inv :: "nat \<Rightarrow> tassn" where
  "P0_inv 0 = emp\<^sub>t"
| "P0_inv (Suc n) = (ode_inv_assn (\<lambda>s. landerInv s \<le> 0) @\<^sub>t P0_inv n)"

lemma P0_inv_Suc:
  "P0_inv n @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0) = 
   ode_inv_assn (\<lambda>s. landerInv s \<le> 0) @\<^sub>t P0_inv n"
  apply (induct n) by (auto simp add: join_assoc)

lemma ContODE:
 "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. landerInv s \<le> 0 \<and>
             (\<lambda>s. s T = 0 \<and> s T < Period) s \<and>
             supp s \<subseteq> {V, W, T} \<and> P tr}
     Cont (ODE ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732), W := (\<lambda>s. (s W)^2 / 2500 ), T := (\<lambda>_. 1)))) ((\<lambda>s. s T < Period))
    {\<lambda>s tr. s T = Period \<and>
            supp s \<subseteq> {V, W, T} \<and>
            landerInv s \<le> 0 \<and>
            (P @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0)) tr}"
  apply(rule Valid_post_and)
  subgoal
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_inv_b_s_le)
apply clarify
       apply(simp add:vec2state_def)
     apply (fast intro!: derivative_intros)
    apply(auto simp add:state2vec_def entails_def)
    done
  apply(rule Valid_post_and)
  subgoal
    apply(rule Valid_weaken_pre)
     prefer 2
     apply(rule Valid_ode_supp)
     apply (auto simp add:entails_def)
    done
  apply(rule Valid_weaken_pre)
   prefer 2
   apply (rule DC'[where init= "\<lambda> s. landerInv s \<le> 0 \<and> s T = 0" and c = "\<lambda> s. s T \<ge> 0"])
    apply(rule Valid_weaken_pre)
 prefer 2
     apply(rule Valid_inv_s_tr_ge)
      apply clarify
      apply(simp add:vec2state_def)
      apply (fast intro!: derivative_intros)
  subgoal
    by(auto simp add:state2vec_def)
    prefer 2
apply(rule Valid_weaken_pre)
 prefer 2
  apply(rule Valid_inv_barrier_s_tr_le)
apply clarify
       apply(simp add:vec2state_def landerInv_def landerinv_def)
    apply (fast intro!: derivative_intros)
   apply(auto simp add:state2vec_def entails_def landerInv_def landerinv_def)
  sorry


lemma P0_prop_st:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, W := w0, T := Period) \<and>
                  landerinv 0 v0 w0 \<le> 0 \<and> emp\<^sub>t tr}
     P0
   {\<lambda>s tr. \<exists>n v w. s = (\<lambda>_. 0)(V := v, W := w, T := Period) \<and>
                   landerinv 0 v w \<le> 0 \<and> P0_inv n tr}"
  unfolding P0_def
  apply (rule Valid_weaken_pre)
   prefer 2
  apply (rule Valid_rep)
  apply (rule Valid_ex_pre) apply (rule Valid_ex_pre)
  apply (rule Valid_ex_pre)
  subgoal for n v w
    apply (rule Valid_seq)
     apply (rule Valid_assign_sp_st)
    apply (rule Valid_seq)
     apply (rule Valid_weaken_pre)
      prefer 2 
    apply (rule ContODE[where P="P0_inv n"])
     apply auto
     apply (auto simp add: entails_def landerInv_def supp_def Period_def)[1]
    apply (rule Valid_weaken_pre[where P'=
          "\<lambda>s tr. \<exists>v w. s = ((\<lambda>_. 0)(V := v, W := w, T := Period)) \<and>
                        landerInv s \<le> 0 \<and>
                        (P0_inv n @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0)) tr"])
    subgoal
      apply (auto simp add: entails_def  supp_def)
      subgoal for s tr
        apply (rule exI[where x="s V"]) apply (rule exI[where x="s W"])
        apply (rule ext) by auto
      done
    apply (rule Valid_ex_pre)
    apply (rule Valid_ex_pre)
    subgoal for v w
    apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_assign_sp_st)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="Suc n"])
      apply (rule exI[where x=v]) apply (rule exI[where x="W_upd v w"])
      apply (auto simp add: P0_inv_Suc)
      by (auto simp add: landerInv_def landerinv_prop2)
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x=0]) apply (rule exI[where x=v0])
  apply (rule exI[where x=w0]) by auto


lemma P0_prop:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. s = (\<lambda>_. 0)(V := v0, W := w0, T := Period) \<and>
                  landerinv 0 v0 w0 \<le> 0 \<and> emp\<^sub>t tr}
     P0
   {\<lambda>s tr. \<exists>n v w. s = (\<lambda>_. 0)(V := v, W := w, T := Period) \<and>
                   landerinv 0 v w \<le> 0 \<and> P0_inv n tr}"
  unfolding P0_def
  apply (rule Valid_weaken_pre)
   prefer 2
  apply (rule Valid_rep)
  apply (rule Valid_ex_pre) apply (rule Valid_ex_pre)
  apply (rule Valid_ex_pre)
  subgoal for n v w
    apply (rule Valid_seq)
     apply (rule Valid_assign_sp)
    apply (rule Valid_seq)
     apply (rule Valid_weaken_pre)
      prefer 2 
    apply (rule ContODE[where P="P0_inv n"])
     apply auto
    subgoal
    proof-
      have "s T = 0 \<and> (\<exists>x. s(T := x) = (\<lambda>_. 0)(V := vv, W := ww, T := PP)) \<Longrightarrow> (s = (\<lambda>_. 0)(V := vv, W := ww, T := 0))" for s and vv and ww and PP
        by (metis fun_upd_triv fun_upd_upd)
      then show ?thesis
     apply (auto simp add: entails_def landerInv_def supp_def Period_def)
         apply (smt fun_upd_other fun_upd_same train_vars_distinct(1) train_vars_distinct(2) train_vars_distinct(4))
        by (smt fun_upd_apply)
    qed
    apply (rule Valid_weaken_pre[where P'=
          "\<lambda>s tr. \<exists>v w. s = ((\<lambda>_. 0)(V := v, W := w, T := Period)) \<and>
                        landerInv s \<le> 0 \<and>
                        (P0_inv n @\<^sub>t ode_inv_assn (\<lambda>s. landerInv s \<le> 0)) tr"])
    subgoal
      apply (auto simp add: entails_def  supp_def)
      subgoal for s tr
        apply (rule exI[where x="s V"]) apply (rule exI[where x="s W"])
        apply (rule ext) by auto
      done
    apply (rule Valid_ex_pre)
    apply (rule Valid_ex_pre)
    subgoal for v w
    apply (rule Valid_strengthen_post)
       prefer 2 apply (rule Valid_assign_sp)
      apply (auto simp add: entails_def)
      apply (rule exI[where x="Suc n"])
      apply (rule exI[where x=v]) apply (rule exI[where x="W_upd v w"])
      apply (auto simp add: P0_inv_Suc)
       apply (auto simp add: landerInv_def landerinv_prop2)
      by (smt fun_upd_apply fun_upd_triv fun_upd_twist fun_upd_upd train_vars_distinct(1) train_vars_distinct(2) train_vars_distinct(4))
    done
  apply (auto simp add: entails_def)
  apply (rule exI[where x=0]) apply (rule exI[where x=v0])
  apply (rule exI[where x=w0]) by auto
end
