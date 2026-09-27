theory PhaseG_Scale_Unbounded
  imports "H3L_GNI.PhaseG_Lander_Mass_Witness"
begin

section \<open>P1.4a/c: unbounded-guard scaling rules toward Lander0\<close>

text \<open>
Toward the paper's real (no fixed \<^term>\<open>Fmax\<close>) mass model: the
cycle guard without the thrust bound is \<^term>\<open>s T < Period \<and> 0 < s M\<close>;
positive mass is preserved by positive scaling, and the whole clock
guard is scale-invariant.  These are the local certificates that the
revision plan (\<^emph>\<open>H3L_NI syntax rule revision\<close> \<S>3 Cont-Scale) lists as
the ODE side conditions; the communication/parallel witness rules and
the global GNI-Intro remain future work.\<close>

definition unbounded_guard :: fform where
  "unbounded_guard s \<longleftrightarrow> s T < Period \<and> 0 < s M"

lemma unbounded_guard_scale:
  assumes pos: "0 < k" and g: "unbounded_guard s"
  shows "unbounded_guard (mass_scale k s)"
  using assms unfolding unbounded_guard_def by simp

lemma mass_scale_M_pos:
  assumes pos: "0 < k" and mpos: "0 < s M"
  shows "0 < mass_scale k s M"
  using assms by simp

text \<open>ODE-solution scaling with the unbounded guard, covering both
semantic branches of \<^const>\<open>Cont\<close>.\<close>

theorem mass_scale_cont_unbounded:
  assumes pos: "0 < k" and dp: "0 < d"
    and sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and p0: "p 0 = s(T := 0)"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (p t)"
    and clock_exit: "\<not> p d T < Period"
  shows "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
    ((mass_scale k s)(T := 0))
    [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
    (mass_scale k (p d))"
proof -
  have solk: "ODEsol (ODE lander_mass_clock_field) (\<lambda>t. mass_scale k (p t)) d"
    by (rule mass_scale_ODEsol[OF pos sol])
  have gk: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (mass_scale k (p t))"
    using inside by (simp add: unbounded_guard_scale[OF pos])
  have exk: "\<not> unbounded_guard (mass_scale k (p d))"
    unfolding unbounded_guard_def using clock_exit by simp
  have reset: "(mass_scale k s)(T := 0) = mass_scale k (p 0)"
    by (rule ext) (simp add: p0 mass_scale_def)
  show ?thesis
    by (rule ContB2[OF dp solk gk exk reset[THEN sym]])
qed


definition Abs0 :: proc where
  "Abs0 = T ::= (\<lambda>_. 0);
   Cont (ODE lander_mass_clock_field) unbounded_guard;
   W ::= (\<lambda>s. W_upd (s V) (s W));
   Fc ::= (\<lambda>s. s M * s W)"

lemma mass_post_steps0:
  "big_step
      (W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W))
      s [] (mass_post s)"
proof -
  let ?s1 = "s(W := W_upd (s V) (s W))"
  let ?s2 = "?s1(Fc := ?s1 M * ?s1 W)"
  have s2: "?s2 = mass_post s" unfolding mass_post_def by simp
  have a: "big_step (W ::= (\<lambda>s. W_upd (s V) (s W))) s [] ?s1"
    by (rule assignB)
  have b: "big_step (Fc ::= (\<lambda>s. s M * s W)) ?s1 [] ?s2"
    by (rule assignB)
  show ?thesis using seqB[OF a b] s2 by simp
qed

theorem mass_scale_abs0_one_cycle:
  assumes pos: "0 < k" and dp: "0 < d"
    and sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and p0: "p 0 = s(T := 0)"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (p t)"
    and clock_exit: "\<not> p d T < Period"
  shows "big_step (Abs0) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (mass_post (p d)))"
    and "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})) =
      lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) ({}, {}))"
    and "mass_scale k (mass_post (p d)) V = mass_post (p d) V"
    and "mass_scale k (mass_post (p d)) W = mass_post (p d) W"
proof -
  have reset: "(mass_scale k s)(T := 0) = mass_scale k (p 0)"
    by (rule ext) (simp add: p0 mass_scale_def)
  have a: "big_step (T ::= (\<lambda>_. 0)) (mass_scale k s) []
      ((mass_scale k s)(T := 0))" by (rule assignB)
  have b: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      ((mass_scale k s)(T := 0))
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (p d))"
    by (rule mass_scale_cont_unbounded[OF pos dp sol p0 inside clock_exit])
  have c: "big_step
      (W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W))
      (mass_scale k (p d)) [] (mass_post (mass_scale k (p d)))"
    by (rule mass_post_steps0)
  have bc: "big_step
      (Cont (ODE lander_mass_clock_field) unbounded_guard;
       W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W))
      ((mass_scale k s)(T := 0))
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_post (mass_scale k (p d)))"
    using seqB[OF b c] by simp
  have pre: "big_step (T ::= (\<lambda>_. 0);
      Cont (ODE lander_mass_clock_field) unbounded_guard;
      W ::= (\<lambda>s. W_upd (s V) (s W));
      Fc ::= (\<lambda>s. s M * s W))
      (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_post (mass_scale k (p d)))"
    using seqB[OF a bc] by simp
  show "big_step (Abs0) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (mass_post (p d)))"
    unfolding Abs0_def
    by (rule big_step_cong[OF pre refl mass_post_scale])
  show "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})) =
      lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) ({}, {}))"
    by (rule mass_scale_wait_obs)
  show "mass_scale k (mass_post (p d)) V = mass_post (p d) V"
    by (simp add: mass_post_scale)
  show "mass_scale k (mass_post (p d)) W = mass_post (p d) W"
    by (simp add: mass_post_scale)
qed

theorem scale_rep_by_step:
  assumes step:
    "\<And>s tr s'. big_step C s tr s' \<Longrightarrow>
      \<exists>tr'. big_step C (mass_scale k s) tr' (mass_scale k s')
        \<and> lander_obs_trace tr' = lander_obs_trace tr"
    and run: "big_step (Rep C) s tr s'"
  shows "\<exists>tr'. big_step (Rep C) (mass_scale k s) tr'
      (mass_scale k s') \<and> lander_obs_trace tr' = lander_obs_trace tr"
  using run
proof (induct "Rep C" s tr s' rule: big_step.induct)
  case (RepetitionB1 s)
  have z: "big_step (Rep C) (mass_scale k s) [] (mass_scale k s)"
    by (rule RepetitionB1)
  show ?case using z by (auto simp: lander_obs_trace_def)
next
  case (RepetitionB2 s tr1 s2 tr2 s3 tr)
  obtain tr1' where a: "big_step C (mass_scale k s) tr1'
      (mass_scale k s2)" and ao: "lander_obs_trace tr1' = lander_obs_trace tr1"
    using step RepetitionB2.hyps(1) by blast
  obtain tr2' where b: "big_step (Rep C) (mass_scale k s2) tr2'
      (mass_scale k s3)" and bo: "lander_obs_trace tr2' = lander_obs_trace tr2"
    using RepetitionB2 by blast
  have c: "big_step (Rep C) (mass_scale k s) (tr1' @ tr2')
      (mass_scale k s3)"
    by (rule big_step.RepetitionB2[OF a b refl])
  show ?case using c ao bo RepetitionB2.hyps(5)
    by (auto simp: lander_obs_trace_append)
qed

end
