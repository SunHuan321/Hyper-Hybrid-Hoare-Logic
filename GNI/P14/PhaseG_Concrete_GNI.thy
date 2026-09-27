theory PhaseG_Concrete_GNI
  imports PhaseG_Concrete_Scale
begin

section \<open>Cross-closed initial families for the parallel lander\<close>

definition lander0_initial_cross :: "((char, real) exgstate) set \<Rightarrow> bool" where
  "lander0_initial_cross S \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>lp lc sp sc.
      x = ExParState (ExState (lp, sp)) (ExState (lc, sc))
      \<and> 0 < sp M \<and> lp HI = sp M
      \<and> lp LO = sp V \<and> lp LOW_W = sp W) \<and>
    (\<forall>lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2.
      ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> S
      \<longrightarrow> ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> S
      \<longrightarrow> lp1 LO = lp2 LO \<and> lp1 LOW_W = lp2 LOW_W
      \<longrightarrow> ExParState
        (ExState (lp2(HI := lp1 HI), mass_scale (sp1 M / sp2 M) sp2))
        (ExState (lc2, mass_scale (sp1 M / sp2 M) sc2)) \<in> S)"

lemma lander0_sem_extract:
  fixes S :: "((char, real) exgstate) set"
  assumes cross: "lander0_initial_cross S"
    and mem: "r \<in> par_sem Lander0 S"
  obtains lp lc sp sc fp fc tr where
    "ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<in> S"
    "0 < sp M" "lp HI = sp M"
    "r = (ExParState (ExState (lp, fp)) (ExState (lc, fc)), tr)"
    "par_big_step Lander0 (ParState (State sp) (State sc)) tr
       (ParState (State fp) (State fc))"
proof -
  from mem obtain x where x: "x \<in> S"
    and run: "par_big_step Lander0 (ex2gstate x) (snd r)
      (ex2gstate (fst r))"
    and same: "ex_logical_same x (fst r)"
    unfolding in_par_sem by blast
  from cross x obtain lp lc sp sc where
    xeq: "x = ExParState (ExState (lp, sp)) (ExState (lc, sc))"
    and pos: "0 < sp M" and hi: "lp HI = sp M"
    unfolding lander0_initial_cross_def by blast
  from same[unfolded xeq] have shape:
    "\<exists>fp fc. fst r = ExParState (ExState (lp, fp)) (ExState (lc, fc))"
  proof (cases "fst r")
    case (ExState a)
    then show ?thesis using same unfolding xeq by simp
  next
    case (ExParState u v)
    then have ul: "ex_logical_same (ExState (lp, sp)) u"
      and vl: "ex_logical_same (ExState (lc, sc)) v"
      using same unfolding xeq by simp_all
    from ul obtain fp where ue: "u = ExState (lp, fp)"
      by (cases u) auto
    from vl obtain fc where ve: "v = ExState (lc, fc)"
      by (cases v) auto
    show ?thesis using ExParState ue ve by blast
  qed
  from shape obtain fp fc where
    req: "fst r = ExParState (ExState (lp, fp)) (ExState (lc, fc))"
    by blast
  have init: "ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<in> S"
    using x unfolding xeq .
  have step: "par_big_step Lander0 (ParState (State sp) (State sc))
    (snd r) (ParState (State fp) (State fc))"
    using run unfolding xeq req by simp
  have pair: "r = (ExParState (ExState (lp, fp)) (ExState (lc, fc)), snd r)"
    using req by (cases r) simp
  show thesis by (rule that[OF init pos hi pair step])
qed

theorem lander0_mass_gni_norm:
  fixes S :: "((char, real) exgstate) set"
  assumes cross: "lander0_initial_cross S"
  shows "lander_mass_gni_norm (par_sem Lander0 S)"
proof (unfold lander_mass_gni_norm_def, intro conjI)
  show "\<forall>r\<in>par_sem Lander0 S.
    lander_high_input r \<noteq> None \<and>
    lander_low_input r \<noteq> None \<and>
    lander_final_low (fst r) \<noteq> None"
  proof (intro ballI)
    fix r assume mem: "r \<in> par_sem Lander0 S"
    from lander0_sem_extract[OF cross mem] obtain lp lc sp sc fp fc tr
      where "r = (ExParState (ExState (lp, fp)) (ExState (lc, fc)), tr)"
      by (rule lander0_sem_extract[OF cross mem])
    then show "lander_high_input r \<noteq> None \<and>
      lander_low_input r \<noteq> None \<and>
      lander_final_low (fst r) \<noteq> None"
      unfolding lander_high_input_def lander_low_input_def by simp
  qed
  show "\<forall>r1\<in>par_sem Lander0 S. \<forall>r2\<in>par_sem Lander0 S.
    lander_low_input r1 = lander_low_input r2 \<longrightarrow>
      (\<exists>r3\<in>par_sem Lander0 S.
        lander_high_input r3 = lander_high_input r1 \<and>
        lander_low_input r3 = lander_low_input r2 \<and>
        lander_low_observation_norm r3 = lander_low_observation_norm r2)"
  proof (intro ballI impI)
    fix r1 r2
    assume m1: "r1 \<in> par_sem Lander0 S"
      and m2: "r2 \<in> par_sem Lander0 S"
      and low: "lander_low_input r1 = lander_low_input r2"
    from lander0_sem_extract[OF cross m1] obtain lp1 lc1 sp1 sc1 fp1 fc1 tr1
      where i1: "ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> S"
        and p1: "0 < sp1 M" and h1: "lp1 HI = sp1 M"
        and r1: "r1 = (ExParState (ExState (lp1, fp1)) (ExState (lc1, fc1)), tr1)"
        and run1: "par_big_step Lander0 (ParState (State sp1) (State sc1))
          tr1 (ParState (State fp1) (State fc1))"
      by (rule lander0_sem_extract[OF cross m1])
    from lander0_sem_extract[OF cross m2] obtain lp2 lc2 sp2 sc2 fp2 fc2 tr2
      where i2: "ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> S"
        and p2: "0 < sp2 M" and h2: "lp2 HI = sp2 M"
        and r2: "r2 = (ExParState (ExState (lp2, fp2)) (ExState (lc2, fc2)), tr2)"
        and run2: "par_big_step Lander0 (ParState (State sp2) (State sc2))
          tr2 (ParState (State fp2) (State fc2))"
      by (rule lander0_sem_extract[OF cross m2])
    have ll: "lp1 LO = lp2 LO \<and> lp1 LOW_W = lp2 LOW_W"
      using low unfolding r1 r2 lander_low_input_def by simp
    let ?k = "sp1 M / sp2 M"
    have kp: "0 < ?k" using p1 p2 by simp
    let ?lp3 = "lp2(HI := lp1 HI)"
    let ?i3 = "ExParState (ExState (?lp3, mass_scale ?k sp2))
      (ExState (lc2, mass_scale ?k sc2))"
    have closure: "\<forall>lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2.
      ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> S
      \<longrightarrow> ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> S
      \<longrightarrow> lp1 LO = lp2 LO \<and> lp1 LOW_W = lp2 LOW_W
      \<longrightarrow> ExParState
        (ExState (lp2(HI := lp1 HI), mass_scale (sp1 M / sp2 M) sp2))
        (ExState (lc2, mass_scale (sp1 M / sp2 M) sc2)) \<in> S"
      using cross unfolding lander0_initial_cross_def by simp
    have i3: "?i3 \<in> S"
      by (rule closure[rule_format, OF i1 i2 ll])
    have run3: "par_big_step Lander0
      (ParState (State (mass_scale ?k sp2)) (State (mass_scale ?k sc2)))
      (scale_trace ?k tr2)
      (ParState (State (mass_scale ?k fp2)) (State (mass_scale ?k fc2)))"
      by (rule lander0_scale_run[OF kp run2])
    let ?r3 = "(ExParState (ExState (?lp3, mass_scale ?k fp2))
      (ExState (lc2, mass_scale ?k fc2)), scale_trace ?k tr2)"
    have r3mem: "?r3 \<in> par_sem Lander0 S"
      unfolding in_par_sem
      apply (rule_tac x = ?i3 in exI)
      using i3 run3 by simp
    have hi: "lander_high_input ?r3 = lander_high_input r1"
      unfolding r1 lander_high_input_def by simp
    have lo: "lander_low_input ?r3 = lander_low_input r2"
      unfolding r2 lander_low_input_def by simp
    have obs: "lander_low_observation_norm ?r3 =
      lander_low_observation_norm r2"
      unfolding r2 lander_low_observation_norm_def
      by (simp add: lander_obs_scale_trace)
    show "\<exists>r3\<in>par_sem Lander0 S.
      lander_high_input r3 = lander_high_input r1 \<and>
      lander_low_input r3 = lander_low_input r2 \<and>
      lander_low_observation_norm r3 = lander_low_observation_norm r2"
      by (rule_tac x = ?r3 in bexI) (simp_all add: r3mem hi lo obs)
  qed
qed

definition lander0_zero_family :: "((char, real) exgstate) set" where
  "lander0_zero_family =
    {ExParState
      (ExState ((\<lambda>_. 0)(HI := m), (\<lambda>_. 0)(M := m)))
      (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := m))) |m. 0 < m}"

lemma lander0_zero_family_nonempty: "lander0_zero_family \<noteq> {}"
proof -
  have one: "ExParState
      (ExState ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(M := 1)))
      (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := 1)))
      \<in> lander0_zero_family"
    unfolding lander0_zero_family_def
    by (rule CollectI, rule_tac x = 1 in exI) simp
  show ?thesis using one by auto
qed

lemma lander0_zero_family_cross:
  "lander0_initial_cross lander0_zero_family"
proof -
  have scale: "\<And>m1 m2. 0 < m1 \<Longrightarrow> 0 < m2 \<Longrightarrow>
      mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) =
      ((\<lambda>_. 0)(M := m1))"
  proof -
    fix m1 m2 :: real
    assume m1: "0 < m1" and m2: "0 < m2"
    show "mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) =
      ((\<lambda>_. 0)(M := m1))"
    proof (rule ext)
      fix x
      show "mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) x =
        ((\<lambda>_. 0)(M := m1)) x"
        using m2 by (simp add: mass_scale_def)
    qed
  qed
  have shape: "\<forall>x\<in>lander0_zero_family. \<exists>lp lc sp sc.
    x = ExParState (ExState (lp, sp)) (ExState (lc, sc))
      \<and> 0 < sp M \<and> lp HI = sp M
      \<and> lp LO = sp V \<and> lp LOW_W = sp W"
  proof (intro ballI)
    fix x assume xin: "x \<in> lander0_zero_family"
    from xin obtain m where mp: "0 < m" and xe:
      "x = ExParState
        (ExState ((\<lambda>_. 0)(HI := m), (\<lambda>_. 0)(M := m)))
        (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := m)))"
      unfolding lander0_zero_family_def by blast
    show "\<exists>lp lc sp sc.
      x = ExParState (ExState (lp, sp)) (ExState (lc, sc))
      \<and> 0 < sp M \<and> lp HI = sp M
      \<and> lp LO = sp V \<and> lp LOW_W = sp W"
      unfolding xe using mp by auto
  qed
  have closure: "\<forall>lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2.
      ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1))
        \<in> lander0_zero_family
      \<longrightarrow> ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2))
        \<in> lander0_zero_family
      \<longrightarrow> lp1 LO = lp2 LO \<and> lp1 LOW_W = lp2 LOW_W
      \<longrightarrow> ExParState
        (ExState (lp2(HI := lp1 HI), mass_scale (sp1 M / sp2 M) sp2))
        (ExState (lc2, mass_scale (sp1 M / sp2 M) sc2))
        \<in> lander0_zero_family"
  proof (intro allI impI)
    fix lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2
    assume i1: "ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1))
        \<in> lander0_zero_family"
      and i2: "ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2))
        \<in> lander0_zero_family"
      and low: "lp1 LO = lp2 LO \<and> lp1 LOW_W = lp2 LOW_W"
    from i1 obtain m1 where m1: "0 < m1"
      and e1: "lp1 = (\<lambda>_. 0)(HI := m1)"
        "lc1 = (\<lambda>_. 0)" "sp1 = (\<lambda>_. 0)(M := m1)"
        "sc1 = (\<lambda>_. 0)(M := m1)"
      unfolding lander0_zero_family_def by auto
    from i2 obtain m2 where m2: "0 < m2"
      and e2: "lp2 = (\<lambda>_. 0)(HI := m2)"
        "lc2 = (\<lambda>_. 0)" "sp2 = (\<lambda>_. 0)(M := m2)"
        "sc2 = (\<lambda>_. 0)(M := m2)"
      unfolding lander0_zero_family_def by auto
    have mem: "ExParState
      (ExState ((\<lambda>_. 0)(HI := m1), (\<lambda>_. 0)(M := m1)))
      (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := m1)))
      \<in> lander0_zero_family"
      unfolding lander0_zero_family_def using m1 by blast
    show "ExParState
      (ExState (lp2(HI := lp1 HI), mass_scale (sp1 M / sp2 M) sp2))
      (ExState (lc2, mass_scale (sp1 M / sp2 M) sc2))
      \<in> lander0_zero_family"
      using mem scale[OF m1 m2]
      unfolding e1 e2 by simp
  qed
  show ?thesis unfolding lander0_initial_cross_def using shape closure by simp
qed

theorem lander0_zero_family_gni:
  "lander_mass_gni_norm (par_sem Lander0 lander0_zero_family)"
  by (rule lander0_mass_gni_norm[OF lander0_zero_family_cross])

theorem lander0_zero_family_has_run:
  "\<exists>r\<in>par_sem Lander0 lander0_zero_family. snd r = []"
proof -
  let ?sp = "(\<lambda>_. 0)(M := 1)"
  let ?lp = "(\<lambda>_. 0)(HI := 1)"
  let ?lc = "(\<lambda>_. 0)"
  let ?x = "ExParState (ExState (?lp, ?sp)) (ExState (?lc, ?sp))"
  have init: "?x \<in> lander0_zero_family"
    unfolding lander0_zero_family_def
    by (rule CollectI, rule_tac x = 1 in exI) simp
  have rp: "par_big_step (Single (Rep Plant0)) (State ?sp) [] (State ?sp)"
    by (rule SingleB, rule RepetitionB1)
  have rc: "par_big_step (Single (Rep Ctrl0)) (State ?sp) [] (State ?sp)"
    by (rule SingleB, rule RepetitionB1)
  have run: "par_big_step Lander0 (ex2gstate ?x) [] (ex2gstate ?x)"
    using ParallelB[OF rp rc combine_blocks_empty]
    unfolding Lander0_def by simp
  have mem: "(?x, []) \<in> par_sem Lander0 lander0_zero_family"
    unfolding in_par_sem
    apply (rule_tac x = ?x in exI)
    using init run by simp
  show ?thesis
    by (rule_tac x = "(?x, [])" in bexI) (simp_all add: mem)
qed

end
