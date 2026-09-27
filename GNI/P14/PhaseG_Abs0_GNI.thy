theory PhaseG_Abs0_GNI
  imports "H3L_GNI_WF.PhaseG_Scale_Unbounded"
begin

section \<open>All-branch scaling of the unbounded abstract cycle\<close>

lemma unbounded_guard_scale_iff:
  assumes "0 < k"
  shows "unbounded_guard (mass_scale k s) \<longleftrightarrow> unbounded_guard s"
  using assms unfolding unbounded_guard_def
  by (simp add: zero_less_mult_iff)

lemma mass_scale_cont_any_run:
  assumes pos: "0 < k"
    and run: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard) s tr s'"
  shows "\<exists>tr'. big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      (mass_scale k s) tr' (mass_scale k s')
      \<and> lander_obs_trace tr' = lander_obs_trace tr"
proof -
  from run have cases:
    "(\<not> unbounded_guard s \<and> tr = [] \<and> s' = s) \<or>
     (\<exists>d p. d > 0 \<and> ODEsol (ODE lander_mass_clock_field) p d
       \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (p t))
       \<and> \<not> unbounded_guard (p d) \<and> p 0 = s
       \<and> tr = [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]
       \<and> s' = p d)"
    by (auto elim: contE)
  from cases show ?thesis
  proof (elim disjE)
    assume z: "\<not> unbounded_guard s \<and> tr = [] \<and> s' = s"
    then have ng: "\<not> unbounded_guard (mass_scale k s)"
      using unbounded_guard_scale_iff[OF pos] by blast
    have b: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      (mass_scale k s) [] (mass_scale k s)"
      by (rule ContB1) (fact ng)
    show ?thesis using z b by (auto simp: lander_obs_trace_def)
  next
    assume w: "\<exists>d p. d > 0 \<and> ODEsol (ODE lander_mass_clock_field) p d
       \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (p t))
       \<and> \<not> unbounded_guard (p d) \<and> p 0 = s
       \<and> tr = [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]
       \<and> s' = p d"
    from w obtain d p where dp: "d > 0"
      and sol: "ODEsol (ODE lander_mass_clock_field) p d"
      and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (p t)"
      and ex: "\<not> unbounded_guard (p d)" and p0: "p 0 = s"
      and tr: "tr = [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]"
      and s': "s' = p d" by blast
    have solk: "ODEsol (ODE lander_mass_clock_field) (\<lambda>t. mass_scale k (p t)) d"
      by (rule mass_scale_ODEsol[OF pos sol])
    have ink: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> unbounded_guard (mass_scale k (p t))"
      using inside unbounded_guard_scale_iff[OF pos] by blast
    have exk: "\<not> unbounded_guard (mass_scale k (p d))"
      using ex unbounded_guard_scale_iff[OF pos] by blast
    have p0k: "mass_scale k (p 0) = mass_scale k s" using p0 by simp
    have b: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      (mass_scale k s)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      (mass_scale k (p d))"
      by (rule ContB2[OF dp solk ink exk p0k])
    have obs: "lander_obs_trace [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) ({}, {})]
      = lander_obs_trace [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]"
      by (simp add: lander_obs_trace_def mass_scale_wait_obs)
    show ?thesis using b obs tr s' by blast
  qed
qed

lemma mass_post_steps0_unique:
  assumes "big_step
    (W ::= (\<lambda>s. W_upd (s V) (s W));
     Fc ::= (\<lambda>s. s M * s W)) s tr s'"
  shows "tr = [] \<and> s' = mass_post s"
  using assms unfolding mass_post_def by (auto elim!: seqE assignE)

theorem mass_scale_abs0_step:
  assumes pos: "0 < k" and run: "big_step Abs0 s tr s'"
  shows "\<exists>tr'. big_step Abs0 (mass_scale k s) tr' (mass_scale k s')
    \<and> lander_obs_trace tr' = lander_obs_trace tr"
proof -
  let ?post = "W ::= (\<lambda>s. W_upd (s V) (s W));
               Fc ::= (\<lambda>s. s M * s W)"
  from run[unfolded Abs0_def] obtain u tr0 trrest where
    a: "big_step (T ::= (\<lambda>_. 0)) s tr0 u"
    and rest: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard;
       ?post) u trrest s'" and tr: "tr = tr0 @ trrest"
    by (auto elim: seqE)
  from a have u: "u = s(T := 0)" and tr0: "tr0 = []"
    by (auto elim: assignE)
  from rest obtain v trc trp where
    c: "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard) u trc v"
    and p: "big_step ?post v trp s'" and trrest: "trrest = trc @ trp"
    by (auto elim: seqE)
  from mass_post_steps0_unique[OF p] have trp: "trp = []"
    and s': "s' = mass_post v" by auto
  obtain trc' where c': "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      (mass_scale k u) trc' (mass_scale k v)"
    and obs: "lander_obs_trace trc' = lander_obs_trace trc"
    using mass_scale_cont_any_run[OF pos c] by blast
  have reset: "mass_scale k u = (mass_scale k s)(T := 0)"
    using u by (rule_tac ext) (simp add: mass_scale_def)
  have a': "big_step (T ::= (\<lambda>_. 0)) (mass_scale k s) []
      ((mass_scale k s)(T := 0))" by (rule assignB)
  have c'': "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard)
      ((mass_scale k s)(T := 0)) trc' (mass_scale k v)"
    using c' reset by simp
  have p': "big_step ?post (mass_scale k v) [] (mass_scale k s')"
    using mass_post_steps0[of "mass_scale k v"] s' mass_post_scale by simp
  have cp': "big_step (Cont (ODE lander_mass_clock_field) unbounded_guard;
      ?post) ((mass_scale k s)(T := 0)) trc' (mass_scale k s')"
    using seqB[OF c'' p'] by simp
  have all': "big_step Abs0 (mass_scale k s) trc' (mass_scale k s')"
    unfolding Abs0_def using seqB[OF a' cp'] by simp
  have trobs: "lander_obs_trace trc' = lander_obs_trace tr"
    using obs tr tr0 trrest trp by simp
  show ?thesis using all' trobs by blast
qed

theorem mass_scale_rep_abs0:
  assumes pos: "0 < k" and run: "big_step (Rep Abs0) s tr s'"
  shows "\<exists>tr'. big_step (Rep Abs0) (mass_scale k s) tr' (mass_scale k s')
    \<and> lander_obs_trace tr' = lander_obs_trace tr"
  by (rule scale_rep_by_step[OF mass_scale_abs0_step[OF pos] run])

section \<open>Three-run GNI for the abstract finite-cycle program\<close>

definition abs0_initial_cross :: "((char, real) exstate) set \<Rightarrow> bool" where
  "abs0_initial_cross S \<longleftrightarrow>
    (\<forall>x\<in>S. tproj x = [] \<and> 0 < pproj x M
      \<and> lproj x HI = pproj x M
      \<and> lproj x LO = pproj x V
      \<and> lproj x LOW_W = pproj x W) \<and>
    (\<forall>x\<in>S. \<forall>y\<in>S.
      lproj x LO = lproj y LO \<and> lproj x LOW_W = lproj y LOW_W
      \<longrightarrow> ((lproj y)(HI := lproj x HI),
         mass_scale (pproj x M / pproj y M) (pproj y), []) \<in> S)"

definition abs0_low_observation ::
  "(char, real) exstate \<Rightarrow> (real \<times> real) \<times> lander_obs_event list" where
  "abs0_low_observation r =
    ((pproj r V, pproj r W), norm_lo (lander_obs_trace (tproj r)))"

definition abs0_mass_gni :: "((char, real) exstate) set \<Rightarrow> bool" where
  "abs0_mass_gni Runs \<longleftrightarrow>
    (\<forall>r1\<in>Runs. \<forall>r2\<in>Runs.
      lproj r1 LO = lproj r2 LO \<and> lproj r1 LOW_W = lproj r2 LOW_W
      \<longrightarrow> (\<exists>r3\<in>Runs.
        lproj r3 HI = lproj r1 HI
        \<and> lproj r3 LO = lproj r2 LO
        \<and> lproj r3 LOW_W = lproj r2 LOW_W
        \<and> abs0_low_observation r3 = abs0_low_observation r2))"

theorem abs0_rep_mass_gni:
  fixes S :: "((char, real) exstate) set"
  assumes cross: "abs0_initial_cross S"
  shows "abs0_mass_gni (sem (Rep Abs0) S)"
proof (unfold abs0_mass_gni_def, intro ballI impI)
  fix r1 r2
  assume r1: "r1 \<in> sem (Rep Abs0) S"
    and r2: "r2 \<in> sem (Rep Abs0) S"
    and low: "lproj r1 LO = lproj r2 LO \<and>
      lproj r1 LOW_W = lproj r2 LOW_W"
  from r1 obtain lab1 s1 f1 pre1 tr1 where
    i1: "(lab1, s1, pre1) \<in> S"
    and run1: "big_step (Rep Abs0) s1 tr1 f1"
    and rr1: "r1 = (lab1, f1, pre1 @ tr1)"
    unfolding sem_def by blast
  from r2 obtain lab2 s2 f2 pre2 tr2 where
    i2: "(lab2, s2, pre2) \<in> S"
    and run2: "big_step (Rep Abs0) s2 tr2 f2"
    and rr2: "r2 = (lab2, f2, pre2 @ tr2)"
    unfolding sem_def by blast
  from cross i1 i2 have pre1: "pre1 = []" and pre2: "pre2 = []"
    and m1: "0 < s1 M" and m2: "0 < s2 M"
    unfolding abs0_initial_cross_def tproj_def pproj_def by auto
  have lowlab: "lab1 LO = lab2 LO \<and> lab1 LOW_W = lab2 LOW_W"
    using low rr1 rr2 unfolding lproj_def by simp
  let ?k = "s1 M / s2 M"
  have kpos: "0 < ?k" using m1 m2 by simp
  let ?lab3 = "lab2(HI := lab1 HI)"
  have cross_rule: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow>
      lproj x LO = lproj y LO \<Longrightarrow>
      lproj x LOW_W = lproj y LOW_W \<Longrightarrow>
      ((lproj y)(HI := lproj x HI),
        mass_scale (pproj x M / pproj y M) (pproj y), []) \<in> S"
    using cross unfolding abs0_initial_cross_def by blast
  have i3: "(?lab3, mass_scale ?k s2, []) \<in> S"
    using cross_rule[OF i1 i2] lowlab
    unfolding lproj_def pproj_def by simp
  obtain tr3 where run3: "big_step (Rep Abs0) (mass_scale ?k s2) tr3
      (mass_scale ?k f2)"
    and obs3: "lander_obs_trace tr3 = lander_obs_trace tr2"
    using mass_scale_rep_abs0[OF kpos run2] by blast
  let ?r3 = "(?lab3, mass_scale ?k f2, tr3)"
  have r3mem: "?r3 \<in> sem (Rep Abs0) S"
    unfolding in_sem
    apply (rule_tac x = "mass_scale ?k s2" in exI)
    apply (rule_tac x = "[]" in exI)
    apply (rule_tac x = "tr3" in exI)
    using i3 run3 by simp
  have labs: "lproj ?r3 HI = lproj r1 HI"
    "lproj ?r3 LO = lproj r2 LO"
    "lproj ?r3 LOW_W = lproj r2 LOW_W"
    using rr1 rr2 unfolding lproj_def by simp_all
  have lowobs: "abs0_low_observation ?r3 = abs0_low_observation r2"
    using rr2 pre2 obs3
    unfolding abs0_low_observation_def pproj_def tproj_def by simp
  show "\<exists>r3\<in>sem (Rep Abs0) S.
      lproj r3 HI = lproj r1 HI \<and>
      lproj r3 LO = lproj r2 LO \<and>
      lproj r3 LOW_W = lproj r2 LOW_W \<and>
      abs0_low_observation r3 = abs0_low_observation r2"
    by (rule_tac x = "?r3" in bexI) (simp_all add: r3mem labs lowobs)
qed

definition abs0_zero_family :: "((char, real) exstate) set" where
  "abs0_zero_family =
    {((\<lambda>_. 0)(HI := m), (\<lambda>_. 0)(M := m), []) |m. 0 < m}"

lemma abs0_zero_family_nonempty: "abs0_zero_family \<noteq> {}"
proof -
  have ex: "\<exists>m::real. 0 < m" by (rule_tac x = 1 in exI) simp
  show ?thesis unfolding abs0_zero_family_def using ex by auto
qed

lemma abs0_zero_family_cross: "abs0_initial_cross abs0_zero_family"
proof -
  have scale: "\<And>m1 m2. 0 < m1 \<Longrightarrow> 0 < m2 \<Longrightarrow>
      mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) = ((\<lambda>_. 0)(M := m1))"
  proof -
    fix m1 m2 :: real assume m1: "0 < m1" and m2: "0 < m2"
    show "mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) = ((\<lambda>_. 0)(M := m1))"
    proof (rule ext)
      fix x
      show "mass_scale (m1 / m2) ((\<lambda>_. 0)(M := m2)) x =
        ((\<lambda>_. 0)(M := m1)) x"
        using m2 by (simp add: mass_scale_def)
    qed
  qed
  have shape: "\<forall>x\<in>abs0_zero_family.
      tproj x = [] \<and> 0 < pproj x M
      \<and> lproj x HI = pproj x M
      \<and> lproj x LO = pproj x V
      \<and> lproj x LOW_W = pproj x W"
  proof (intro ballI)
    fix x assume xin: "x \<in> abs0_zero_family"
    then obtain m where mp: "0 < m"
      and x: "x = ((\<lambda>_. 0)(HI := m), (\<lambda>_. 0)(M := m), [])"
      unfolding abs0_zero_family_def by blast
    show "tproj x = [] \<and> 0 < pproj x M
      \<and> lproj x HI = pproj x M
      \<and> lproj x LO = pproj x V
      \<and> lproj x LOW_W = pproj x W"
      using mp unfolding x lproj_def pproj_def tproj_def by simp
  qed
  have cross: "\<forall>x\<in>abs0_zero_family. \<forall>y\<in>abs0_zero_family.
      lproj x LO = lproj y LO \<and> lproj x LOW_W = lproj y LOW_W
      \<longrightarrow> ((lproj y)(HI := lproj x HI),
         mass_scale (pproj x M / pproj y M) (pproj y), [])
           \<in> abs0_zero_family"
  proof (intro ballI impI)
    fix x assume xin: "x \<in> abs0_zero_family"
    fix y assume yin: "y \<in> abs0_zero_family"
    assume "lproj x LO = lproj y LO \<and> lproj x LOW_W = lproj y LOW_W"
    from xin obtain m1 where m1: "0 < m1"
      and x: "x = ((\<lambda>_. 0)(HI := m1), (\<lambda>_. 0)(M := m1), [])"
      unfolding abs0_zero_family_def by blast
    from yin obtain m2 where m2: "0 < m2"
      and y: "y = ((\<lambda>_. 0)(HI := m2), (\<lambda>_. 0)(M := m2), [])"
      unfolding abs0_zero_family_def by blast
    have mem: "((\<lambda>_. 0)(HI := m1), (\<lambda>_. 0)(M := m1), [])
      \<in> abs0_zero_family"
      unfolding abs0_zero_family_def using m1 by blast
    show "((lproj y)(HI := lproj x HI),
         mass_scale (pproj x M / pproj y M) (pproj y), [])
           \<in> abs0_zero_family"
      using mem scale[OF m1 m2]
      unfolding x y lproj_def pproj_def by simp
  qed
  show ?thesis unfolding abs0_initial_cross_def using shape cross by simp
qed

theorem abs0_zero_family_gni:
  "abs0_mass_gni (sem (Rep Abs0) abs0_zero_family)"
  by (rule abs0_rep_mass_gni[OF abs0_zero_family_cross])

section \<open>A positive-time execution of the abstract cycle\<close>

definition abs0_zero_path :: "real \<Rightarrow> real \<Rightarrow> state" where
  "abs0_zero_path m t = ((\<lambda>_. 0)(M := m))(V := -3.732 * t, T := t)"

lemma abs0_zero_path_sol:
  "ODEsol (ODE lander_mass_clock_field) (abs0_zero_path m) Period"
proof -
  let ?D = "{-1..Period+1}"
  have id: "((\<lambda>t. t) has_vderiv_on (\<lambda>t. 1)) ?D"
    by (simp add: has_vderiv_on_id)
  have vd: "((\<lambda>t. -3.732 * t) has_vderiv_on (\<lambda>t. -3.732)) ?D"
    using has_vderiv_on_scale_const[OF id, of "-3.732"] by simp
  have comp: "\<And>x. ((\<lambda>t. abs0_zero_path m t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (abs0_zero_path m t))) ?D"
  proof -
    fix x
    show "((\<lambda>t. abs0_zero_path m t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (abs0_zero_path m t))) ?D"
    proof (cases "x = V")
      case True
      then show ?thesis using vd
        by (simp add: abs0_zero_path_def)
    next
      case v: False
      show ?thesis
      proof (cases "x = T")
        case True
        then show ?thesis using v
          by (simp add: abs0_zero_path_def has_vderiv_on_id)
      next
        case t: False
        show ?thesis
        proof (cases "x = M")
          case True
          then show ?thesis using v t
            by (simp add: abs0_zero_path_def has_vderiv_on_const)
        next
          case m: False
          consider (fc) "x = Fc" | (w) "x = W" |
            (other) "x \<noteq> Fc \<and> x \<noteq> W" by auto
          then show ?thesis
          proof cases
            case fc
            then show ?thesis using v t m
              by (simp add: abs0_zero_path_def has_vderiv_on_const)
          next
            case w
            then show ?thesis using v t m
              by (simp add: abs0_zero_path_def has_vderiv_on_const)
          next
            case other
            then show ?thesis using v t m
              by (simp add: abs0_zero_path_def has_vderiv_on_const)
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    by (rule ODEsol_from_components[OF _ _ comp])
       (simp_all add: Period_def)
qed

lemma abs0_zero_cycle:
  assumes mp: "0 < m"
  shows "big_step Abs0 ((\<lambda>_. 0)(M := m))
    [WaitBlk Period (\<lambda>t. State (abs0_zero_path m t)) ({}, {})]
    (mass_post (abs0_zero_path m Period))"
proof -
  let ?s = "(\<lambda>_. 0)(M := m)"
  let ?p = "abs0_zero_path m"
  have dp: "0 < Period" by (simp add: Period_def)
  have p0: "?p 0 = ?s(T := 0)"
    by (rule ext) (simp add: abs0_zero_path_def)
  have inside: "\<forall>t. 0 \<le> t \<and> t < Period \<longrightarrow> unbounded_guard (?p t)"
    using mp unfolding unbounded_guard_def
    by (simp add: abs0_zero_path_def)
  have ex: "\<not> ?p Period T < Period"
    by (simp add: abs0_zero_path_def)
  have scaled: "big_step Abs0 (mass_scale 1 ?s)
    [WaitBlk Period (\<lambda>t. State (mass_scale 1 (?p t))) ({}, {})]
    (mass_scale 1 (mass_post (?p Period)))"
    by (rule mass_scale_abs0_one_cycle(1)[OF _ dp abs0_zero_path_sol p0 inside ex]) simp
  show ?thesis using scaled by simp
qed

theorem abs0_zero_family_positive_cycle:
  "\<exists>r\<in>sem (Rep Abs0) abs0_zero_family.
     \<exists>d p rdy. 0 < d \<and> tproj r = [WaitBlk d p rdy]"
proof -
  let ?m = "1::real"
  let ?s = "(\<lambda>_. 0)(M := ?m)"
  let ?lab = "(\<lambda>_. 0)(HI := ?m)"
  let ?p = "abs0_zero_path ?m"
  let ?tr = "[WaitBlk Period (\<lambda>t. State (?p t)) ({}, {})]"
  let ?f = "mass_post (?p Period)"
  have ini: "(?lab, ?s, []) \<in> abs0_zero_family"
    unfolding abs0_zero_family_def by auto
  have cycle: "big_step Abs0 ?s ?tr ?f"
    by (rule abs0_zero_cycle) simp
  have stop: "big_step (Rep Abs0) ?f [] ?f" by (rule RepetitionB1)
  have run: "big_step (Rep Abs0) ?s ?tr ?f"
    using big_step.RepetitionB2[OF cycle stop refl] by simp
  have mem: "(?lab, ?f, ?tr) \<in> sem (Rep Abs0) abs0_zero_family"
    unfolding in_sem
    apply (rule_tac x = "?s" in exI)
    apply (rule_tac x = "[]" in exI)
    apply (rule_tac x = "?tr" in exI)
    using ini run by simp
  have exists_obs: "\<exists>d p rdy. 0 < d \<and>
      tproj (?lab, ?f, ?tr) = [WaitBlk d p rdy]"
    unfolding tproj_def
    apply (rule_tac x = "Period" in exI)
    apply (rule_tac x = "\<lambda>t. State (?p t)" in exI)
    apply (rule_tac x = "({}, {})" in exI)
    by (simp add: Period_def)
  show ?thesis using mem exists_obs by blast
qed

end
