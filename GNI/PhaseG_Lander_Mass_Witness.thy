theory PhaseG_Lander_Mass_Witness
  imports PhaseG_GNI_parallel_rich PhaseG_GNI_witness
begin

section \<open>Mass scaling as a continuous three-run witness\<close>

definition mass_scale :: "real \<Rightarrow> state \<Rightarrow> state" where
  "mass_scale k s = s(M := k * s M, Fc := k * s Fc)"

lemma mass_scale_M [simp]: "mass_scale k s M = k * s M"
  unfolding mass_scale_def by simp

lemma mass_scale_Fc [simp]: "mass_scale k s Fc = k * s Fc"
  unfolding mass_scale_def by simp

lemma mass_scale_other [simp]:
  "x \<noteq> M \<Longrightarrow> x \<noteq> Fc \<Longrightarrow> mass_scale k s x = s x"
  unfolding mass_scale_def by simp

lemma mass_scale_selected:
  "x = M \<or> x = Fc \<Longrightarrow> mass_scale k s x = k * s x"
  by auto

lemma has_vderiv_on_scale_const:
  fixes k :: real
  assumes der: "(f has_vderiv_on f') D"
  shows "((\<lambda>t. k * f t) has_vderiv_on (\<lambda>t. k * f' t)) D"
  apply (rule has_vderiv_on_eq_rhs)
   apply (rule has_vderiv_on_mult)
    apply (auto intro: derivative_intros)[1]
  using der by auto

lemma mass_scale_rate:
  assumes nz: "k \<noteq> 0"
  shows "lander_mass_clock_field x (mass_scale k s) =
    (if x = M \<or> x = Fc then k * lander_mass_clock_field x s
     else lander_mass_clock_field x s)"
proof (cases "x = M")
  case True
  then show ?thesis by simp
next
  case m: False
  show ?thesis
  proof (cases "x = Fc")
    case True
    with m show ?thesis by simp
  next
    case f: False
    show ?thesis
    proof (cases "x = V")
      case True
      with m f nz show ?thesis by simp
    next
      case v: False
      show ?thesis
      proof (cases "x = W")
        case True
        with m f v show ?thesis by simp
      next
        case w: False
        show ?thesis
        proof (cases "x = T")
          case True
          with m f v w show ?thesis by simp
        next
          case t: False
          with m f v w show ?thesis by simp
        qed
      qed
    qed
  qed
qed

theorem mass_scale_ODEsol:
  assumes pos: "0 < k" and sol: "ODEsol (ODE lander_mass_clock_field) p d"
  shows "ODEsol (ODE lander_mass_clock_field) (\<lambda>t. mass_scale k (p t)) d"
proof -
  have nz: "k \<noteq> 0" using pos by simp
  from ODEsol_component_ext[OF sol] obtain e where e: "0 < e"
    and comp: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (p t))) {-e..d+e}" by blast
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  show ?thesis
  proof (rule ODEsol_from_components[OF d0 e])
    fix x
    show "((\<lambda>t. mass_scale k (p t) x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (mass_scale k (p t)))) {-e..d+e}"
    proof (cases "x = M \<or> x = Fc")
      case True
      have der: "((\<lambda>t. k * p t x) has_vderiv_on
        (\<lambda>t. k * lander_mass_clock_field x (p t))) {-e..d+e}"
        by (rule has_vderiv_on_scale_const[OF comp[of x]])
      have feq: "(\<lambda>t. mass_scale k (p t) x) = (\<lambda>t. k * p t x)"
        by (rule ext) (rule mass_scale_selected[OF True])
      have req: "(\<lambda>t. lander_mass_clock_field x (mass_scale k (p t))) =
          (\<lambda>t. k * lander_mass_clock_field x (p t))"
        by (rule ext) (simp add: mass_scale_rate[OF nz] True)
      show ?thesis unfolding feq req by (rule der)
    next
      case False
      have xM: "x \<noteq> M" and xF: "x \<noteq> Fc" using False by auto
      have feq: "(\<lambda>t. mass_scale k (p t) x) = (\<lambda>t. p t x)"
        by (rule ext) (simp add: xM xF)
      have req: "(\<lambda>t. lander_mass_clock_field x (mass_scale k (p t))) =
          (\<lambda>t. lander_mass_clock_field x (p t))"
        by (rule ext) (simp add: mass_scale_rate[OF nz] False)
      show ?thesis unfolding feq req by (rule comp[of x])
    qed
  qed
qed

lemma mass_scale_low [simp]:
  "mass_scale k s V = s V" "mass_scale k s W = s W"
  by simp_all

lemma mass_scale_one [simp]: "mass_scale 1 s = s"
  by (rule ext) (simp add: mass_scale_def)

lemma mass_scale_wait_obs:
  "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) r) =
   lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) r)"
proof -
  have curve: "restrict (lander_low_gstate \<circ> (\<lambda>t. State (mass_scale k (p t)))) {0..d} =
      restrict (lander_low_gstate \<circ> (\<lambda>t. State (p t))) {0..d}"
    by (rule restrict_eq_on) simp
  show ?thesis unfolding WaitBlk_def
    by (simp only: lander_obs_block.simps restrict_comp_restrict curve)
qed

definition mass_cycle_guard :: "real \<Rightarrow> fform" where
  "mass_cycle_guard Fmax s \<longleftrightarrow>
    s T < Period \<and> lander_force_ok Fmax s"

lemma mass_scale_force_ok:
  assumes pos: "0 < k" and ok: "lander_force_ok Fmax s"
    and bound: "k * s Fc \<le> Fmax"
  shows "lander_force_ok Fmax (mass_scale k s)"
  using assms unfolding lander_force_ok_def
  by (auto intro: mult_pos_pos mult_nonneg_nonneg)

theorem mass_scale_cont_cycle:
  assumes pos: "0 < k" and dp: "0 < d"
    and sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> mass_cycle_guard Fmax (p t)"
    and margin: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> k * p t Fc \<le> Fmax"
    and clock_exit: "\<not> p d T < Period"
  shows "big_step (Cont (ODE lander_mass_clock_field) (mass_cycle_guard Fmax))
    (mass_scale k (p 0))
    [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
    (mass_scale k (p d))"
proof -
  have solk: "ODEsol (ODE lander_mass_clock_field) (\<lambda>t. mass_scale k (p t)) d"
    by (rule mass_scale_ODEsol[OF pos sol])
  have g: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow>
      mass_cycle_guard Fmax (mass_scale k (p t))"
  proof (intro allI impI)
    fix t assume t: "0 \<le> t \<and> t < d"
    have old: "mass_cycle_guard Fmax (p t)" using inside t by blast
    have b: "k * p t Fc \<le> Fmax" using margin t by blast
    have oldforce: "lander_force_ok Fmax (p t)"
      using old unfolding mass_cycle_guard_def by simp
    have newforce: "lander_force_ok Fmax (mass_scale k (p t))"
      by (rule mass_scale_force_ok[OF pos oldforce b])
    show "mass_cycle_guard Fmax (mass_scale k (p t))"
      using old newforce
      unfolding mass_cycle_guard_def by simp
  qed
  have ex: "\<not> mass_cycle_guard Fmax (mass_scale k (p d))"
    using clock_exit unfolding mass_cycle_guard_def by simp
  show ?thesis by (rule ContB2[OF dp solk g ex refl])
qed

definition mass_post :: "state \<Rightarrow> state" where
  "mass_post s = s(W := W_upd (s V) (s W),
                   Fc := s M * W_upd (s V) (s W))"

lemma mass_post_steps:
  assumes ok: "lander_force_ok Fmax (mass_post s)"
  shows "big_step
      (W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W);
       Assume (lander_force_ok Fmax))
      s [] (mass_post s)"
proof -
  let ?s1 = "s(W := W_upd (s V) (s W))"
  let ?s2 = "?s1(Fc := ?s1 M * ?s1 W)"
  have s2: "?s2 = mass_post s" unfolding mass_post_def by simp
  have a: "big_step (W ::= (\<lambda>s. W_upd (s V) (s W))) s [] ?s1"
    by (rule assignB)
  have b: "big_step (Fc ::= (\<lambda>s. s M * s W)) ?s1 [] ?s2"
    by (rule assignB)
  have c: "big_step (Assume (lander_force_ok Fmax)) ?s2 [] ?s2"
    by (rule AssumeB) (use ok s2 in simp)
  have bc: "big_step
      (Fc ::= (\<lambda>s. s M * s W); Assume (lander_force_ok Fmax))
      ?s1 [] ?s2"
    using seqB[OF b c] by simp
  show ?thesis using seqB[OF a bc] s2 by simp
qed

lemma mass_post_scale:
  "mass_post (mass_scale k s) = mass_scale k (mass_post s)"
proof (rule ext)
  fix x
  show "mass_post (mass_scale k s) x = mass_scale k (mass_post s) x"
    unfolding mass_post_def mass_scale_def
    by (auto simp: algebra_simps)
qed

theorem mass_scale_abs_one_cycle:
  assumes pos: "0 < k" and dp: "0 < d"
    and sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and p0: "p 0 = s(T := 0)"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> mass_cycle_guard Fmax (p t)"
    and margin: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> k * p t Fc \<le> Fmax"
    and clock_exit: "\<not> p d T < Period"
    and post_ok: "lander_force_ok Fmax (mass_post (mass_scale k (p d)))"
  shows "big_step (Abs_M Fmax) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_post (mass_scale k (p d)))"
    and "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})) =
      lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) ({}, {}))"
    and "mass_post (mass_scale k (p d)) V = mass_post (p d) V"
    and "mass_post (mass_scale k (p d)) W = mass_post (p d) W"
proof -
  have reset: "(mass_scale k s)(T := 0) = mass_scale k (p 0)"
    by (rule ext) (simp add: p0 mass_scale_def)
  have a: "big_step (T ::= (\<lambda>_. 0)) (mass_scale k s) [] (mass_scale k (p 0))"
  proof -
    have step: "big_step (T ::= (\<lambda>_. 0)) (mass_scale k s) []
        ((mass_scale k s)(T := 0))" by (rule assignB)
    show ?thesis using step reset by simp
  qed
  have b: "big_step (Cont (ODE lander_mass_clock_field)
      (\<lambda>s. s T < Period \<and> lander_force_ok Fmax s))
      (mass_scale k (p 0))
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (p d))"
    using mass_scale_cont_cycle[OF pos dp sol inside margin clock_exit]
    unfolding mass_cycle_guard_def .
  have c: "big_step
      (W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W);
       Assume (lander_force_ok Fmax))
      (mass_scale k (p d)) [] (mass_post (mass_scale k (p d)))"
    by (rule mass_post_steps[OF post_ok])
  have bc: "big_step
      (Cont (ODE lander_mass_clock_field)
        (\<lambda>s. s T < Period \<and> lander_force_ok Fmax s);
       W ::= (\<lambda>s. W_upd (s V) (s W));
       Fc ::= (\<lambda>s. s M * s W);
       Assume (lander_force_ok Fmax))
      (mass_scale k (p 0))
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_post (mass_scale k (p d)))"
    using seqB[OF b c] by simp
  show "big_step (Abs_M Fmax) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_post (mass_scale k (p d)))"
    unfolding Abs_M_def using seqB[OF a bc] by simp
  show "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})) =
      lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) ({}, {}))"
    by (rule mass_scale_wait_obs)
  show "mass_post (mass_scale k (p d)) V = mass_post (p d) V"
    by (simp add: mass_post_scale)
  show "mass_post (mass_scale k (p d)) W = mass_post (p d) W"
    by (simp add: mass_post_scale)
qed

theorem mass_scale_abs_pair:
  assumes pos: "0 < k" and dp: "0 < d"
    and sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and p0: "p 0 = s(T := 0)"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> mass_cycle_guard Fmax (p t)"
    and margin: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> k * p t Fc \<le> Fmax"
    and clock_exit: "\<not> p d T < Period"
    and orig_post: "lander_force_ok Fmax (mass_post (p d))"
    and scaled_post: "lander_force_ok Fmax (mass_post (mass_scale k (p d)))"
  shows "big_step (Abs_M Fmax) s
      [WaitBlk d (\<lambda>t. State (p t)) ({}, {})] (mass_post (p d))"
    and "big_step (Abs_M Fmax) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (mass_post (p d)))"
    and "lander_obs_trace
       [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
       = lander_obs_trace [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]"
proof -
  have onepos: "0 < (1::real)" by simp
  have m1: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> 1 * p t Fc \<le> Fmax"
    using inside unfolding mass_cycle_guard_def lander_force_ok_def by auto
  have post1: "lander_force_ok Fmax (mass_post (mass_scale 1 (p d)))"
    using orig_post by simp
  show "big_step (Abs_M Fmax) s
      [WaitBlk d (\<lambda>t. State (p t)) ({}, {})] (mass_post (p d))"
    using mass_scale_abs_one_cycle(1)[OF onepos dp sol p0 inside m1 clock_exit post1]
    by simp
  show "big_step (Abs_M Fmax) (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (mass_post (p d)))"
    using mass_scale_abs_one_cycle(1)[OF pos dp sol p0 inside margin clock_exit scaled_post]
    by (simp add: mass_post_scale)
  show "lander_obs_trace
       [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
       = lander_obs_trace [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]"
    by (simp add: lander_obs_trace_def mass_scale_wait_obs)
qed

text \<open>The loop lifting is conditional on a certificate for every reached
one-cycle execution.  The initial mass-family bound alone does not supply
this certificate after the controller updates its target acceleration.\<close>

theorem mass_scale_rep_by_step:
  assumes step:
    "\<And>s tr s'. big_step (Abs_M Fmax) s tr s' \<Longrightarrow>
      \<exists>tr'. big_step (Abs_M Fmax) (mass_scale k s) tr' (mass_scale k s')
        \<and> lander_obs_trace tr' = lander_obs_trace tr"
    and run: "big_step (Rep (Abs_M Fmax)) s tr s'"
  shows "\<exists>tr'. big_step (Rep (Abs_M Fmax)) (mass_scale k s) tr'
      (mass_scale k s') \<and> lander_obs_trace tr' = lander_obs_trace tr"
  using run
proof (induct "Rep (Abs_M Fmax)" s tr s' rule: big_step.induct)
  case (RepetitionB1 s)
  have z: "big_step (Rep (Abs_M Fmax)) (mass_scale k s) [] (mass_scale k s)"
    by (rule RepetitionB1)
  show ?case using z by (auto simp: lander_obs_trace_def)
next
  case (RepetitionB2 s tr1 s2 tr2 s3 tr)
  obtain tr1' where a: "big_step (Abs_M Fmax) (mass_scale k s) tr1'
      (mass_scale k s2)" and ao: "lander_obs_trace tr1' = lander_obs_trace tr1"
    using step RepetitionB2.hyps(1) by blast
  obtain tr2' where b: "big_step (Rep (Abs_M Fmax)) (mass_scale k s2) tr2'
      (mass_scale k s3)" and bo: "lander_obs_trace tr2' = lander_obs_trace tr2"
    using RepetitionB2 by blast
  have c: "big_step (Rep (Abs_M Fmax)) (mass_scale k s) (tr1' @ tr2')
      (mass_scale k s3)"
    by (rule big_step.RepetitionB2[OF a b refl])
  show ?case using c ao bo RepetitionB2.hyps(5)
    by (auto simp: lander_obs_trace_append)
 qed

end
