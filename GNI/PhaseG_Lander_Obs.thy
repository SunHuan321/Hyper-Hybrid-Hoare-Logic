theory PhaseG_Lander_Obs
  imports PhaseG_Lander_Mass_Consistency
begin

section \<open>Frozen attacker model and normalised observation (P0.1)\<close>

text \<open>
Acceptance item P0.1 (\<^emph>\<open>H3L unified framework acceptance 2026-09-26\<close>).
The attacker model is frozen as follows.

  \<^item> \<^bold>\<open>Visible events\<close>: every communication on any channel except the
    private mass channel \<^term>\<open>''m2c''\<close>: direction, channel, and VALUE
    are all observed.  \<^term>\<open>''m2c''\<close> events are hidden entirely
    (neither occurrence nor value nor timing: communications are
    instantaneous, so hiding them cannot shift any visible timestamp).

  \<^item> \<^bold>\<open>Waits\<close>: a wait block reveals its duration and the plant-side low
    curve \<^const>\<open>lander_low_gstate\<close> (the (V,W) pair of the left/global
    state) on \<^term>\<open>{0..d}\<close>.

  \<^item> \<^bold>\<open>Not observed\<close>: ready sets, and the block structure itself:
    consecutive visible waits are merged (curve concatenation with time
    shift), so artificial splitting of a wait block -- as performed by
    \<^const>\<open>combine_blocks\<close> when the two sides wait for different
    durations -- is observationally invisible
    (\<^theory_text>\<open>obs_lo_wait_split\<close>, the rich F1).

  \<^item> \<^bold>\<open>Direction\<close> on internal (synchronized) channels: the global trace
    contains only the synchronized \<^term>\<open>IO\<close> form, so component-side
    In/Out distinctions never occur in observations.

The observation events are \<^typ>\<open>lander_obs_event\<close> from
\<^theory_text>\<open>PhaseG_Lander_MassModel\<close>; the normalisation below merges
adjacent visible waits.  Wait durations in traces are nonnegative, and the
congruence lemmas record this via an explicit nonnegativity flag.
\<close>


lemma LOW_W_neqs [simp]:
  "LOW_W \<noteq> HI" "LOW_W \<noteq> LO" "LOW_W \<noteq> V" "LOW_W \<noteq> W"
  "LOW_W \<noteq> M" "LOW_W \<noteq> Fc" "LOW_W \<noteq> T"
  "HI \<noteq> LOW_W" "LO \<noteq> LOW_W" "V \<noteq> LOW_W" "W \<noteq> LOW_W"
  "M \<noteq> LOW_W" "Fc \<noteq> LOW_W" "T \<noteq> LOW_W"
  unfolding LOW_W_def HI_def LO_def V_def W_def M_def Fc_def T_def by auto


subsection \<open>Curve concatenation\<close>

definition wcat :: "real \<Rightarrow> (real \<Rightarrow> (real \<times> real) option) \<Rightarrow> real \<Rightarrow>
    (real \<Rightarrow> (real \<times> real) option) \<Rightarrow> real \<Rightarrow> (real \<times> real) option" where
  "wcat d1 c1 d2 c2 t = (if t \<le> d1 then c1 t else c2 (t - d1))"

lemma wcat_assoc:
  assumes d2: "0 \<le> d2" and d3: "0 \<le> d3"
  shows "wcat d1 c1 (d2 + d3) (wcat d2 c2 d3 c3) =
   wcat (d1 + d2) (wcat d1 c1 d2 c2) d3 c3"
proof (rule ext)
  fix t
  consider (a) "t \<le> d1" | (b) "d1 < t \<and> t \<le> d1 + d2" | (c) "d1 + d2 < t"
    by linarith
  then show "wcat d1 c1 (d2 + d3) (wcat d2 c2 d3 c3) t =
        wcat (d1 + d2) (wcat d1 c1 d2 c2) d3 c3 t"
  proof cases
    case a
    then show ?thesis using d2 unfolding wcat_def by auto
  next
    case b
    then show ?thesis using d2 unfolding wcat_def by auto
  next
    case c
    then have gt: "d1 + d2 < t" by simp
    have l3: "wcat d1 c1 (d2 + d3) (wcat d2 c2 d3 c3) t = c3 (t - d1 - d2)"
      using d2 gt unfolding wcat_def by auto
    have r3: "wcat (d1 + d2) (wcat d1 c1 d2 c2) d3 c3 t = c3 (t - (d1 + d2))"
      using d2 gt unfolding wcat_def by auto
    have argseq: "t - d1 - d2 = t - (d1 + d2)" by linarith
    show ?thesis unfolding l3 r3 argseq ..
  qed
qed

lemma wcat_merge_split:
  assumes d1: "0 \<le> d1" and d2: "0 \<le> d2"
  shows "wcat d1 (restrict f {0..d1}) d2 (restrict (\<lambda>u. f (u + d1)) {0..d2})
      = restrict f {0..d1 + d2}"
proof (rule ext)
  fix t
  show "wcat d1 (restrict f {0..d1}) d2 (restrict (\<lambda>u. f (u + d1)) {0..d2}) t
      = restrict f {0..d1 + d2} t"
    using d1 d2 unfolding wcat_def restrict_apply by auto
qed


subsection \<open>Normalised observation\<close>

fun norm_lo :: "lander_obs_event list \<Rightarrow> lander_obs_event list" where
  "norm_lo [] = []"
| "norm_lo (VisibleComm ct ch v # r) = VisibleComm ct ch v # norm_lo r"
| "norm_lo (VisibleWait d1 c1 # VisibleWait d2 c2 # r) =
     norm_lo (VisibleWait (d1 + d2) (wcat d1 c1 d2 c2) # r)"
| "norm_lo (VisibleWait d c # r) = VisibleWait d c # norm_lo r"

fun wnnp :: "lander_obs_event list \<Rightarrow> bool" where
  "wnnp [] = True"
| "wnnp (VisibleComm ct ch v # r) = wnnp r"
| "wnnp (VisibleWait de c # r) = (0 \<le> de \<and> wnnp r)"

definition obs_lo_eq :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  "obs_lo_eq tr tr' \<longleftrightarrow>
    norm_lo (lander_obs_trace tr) = norm_lo (lander_obs_trace tr')"

text \<open>The normalized form below is the GNI target for the frozen
attacker model.  The earlier \<^const>\<open>lander_mass_gni\<close> in the candidate
model compares raw block lists and therefore distinguishes wait splitting.\<close>

definition lander_low_observation_norm where
  "lander_low_observation_norm run =
    (lander_final_low (fst run), norm_lo (lander_obs_trace (snd run)))"

definition lander_mass_gni_norm ::
  "((char, real) exgstate \<times> trace) set \<Rightarrow> bool" where
  "lander_mass_gni_norm Runs \<longleftrightarrow>
    (\<forall>r\<in>Runs. lander_high_input r \<noteq> None \<and>
      lander_low_input r \<noteq> None \<and> lander_final_low (fst r) \<noteq> None) \<and>
    (\<forall>r1\<in>Runs. \<forall>r2\<in>Runs.
      lander_low_input r1 = lander_low_input r2 \<longrightarrow>
      (\<exists>r3\<in>Runs.
        lander_high_input r3 = lander_high_input r1 \<and>
        lander_low_input r3 = lander_low_input r2 \<and>
        lander_low_observation_norm r3 = lander_low_observation_norm r2))"

lemma obs_lo_eq_refl [simp]: "obs_lo_eq tr tr"
  unfolding obs_lo_eq_def by simp

lemma obs_lo_eq_sym: "obs_lo_eq tr tr' \<Longrightarrow> obs_lo_eq tr' tr"
  unfolding obs_lo_eq_def by simp

lemma obs_lo_eq_trans:
  "obs_lo_eq tr1 tr2 \<Longrightarrow> obs_lo_eq tr2 tr3 \<Longrightarrow> obs_lo_eq tr1 tr3"
  unfolding obs_lo_eq_def by simp

lemma obs_lo_eq_of_eq:
  "lander_obs_trace tr = lander_obs_trace tr' \<Longrightarrow> obs_lo_eq tr tr'"
  unfolding obs_lo_eq_def by simp

lemma lander_obs_trace_append:
  "lander_obs_trace (tr1 @ tr2) =
   lander_obs_trace tr1 @ lander_obs_trace tr2"
  unfolding lander_obs_trace_def by simp

text \<open>The rich F1: splitting a wait block (as \<^const>\<open>combine_blocks\<close> does
for the longer side) is invisible to the frozen observer.\<close>

theorem obs_lo_wait_split:
  assumes d1: "0 \<le> d1" and d2: "0 \<le> d2"
  shows "obs_lo_eq [WaitBlock d1 p r, WaitBlock d2 (\<lambda>u. p (u + d1)) r]
                      [WaitBlock (d1 + d2) p r]"
  unfolding obs_lo_eq_def lander_obs_trace_def lander_obs_block.simps
  using wcat_merge_split[OF d1 d2, of "lander_low_gstate \<circ> p"]
  by (simp add: comp_def)


subsection \<open>Head decomposition and congruences\<close>

fun wdur :: "lander_obs_event list \<Rightarrow> real" where
  "wdur (VisibleWait d c # r) = d + wdur r"
| "wdur (VisibleComm ct ch v # r) = 0"
| "wdur [] = 0"

fun wafter :: "lander_obs_event list \<Rightarrow> lander_obs_event list" where
  "wafter (VisibleWait d c # r) = wafter r"
| "wafter (VisibleComm ct ch v # r) = VisibleComm ct ch v # r"
| "wafter [] = []"

fun wcatc :: "real \<Rightarrow> (real \<Rightarrow> (real \<times> real) option) \<Rightarrow>
    lander_obs_event list \<Rightarrow> (real \<Rightarrow> (real \<times> real) option)" where
  "wcatc d c (VisibleWait d2 c2 # r) = wcatc (d + d2) (wcat d c d2 c2) r"
| "wcatc d c (VisibleComm ct ch v # r) = c"
| "wcatc d c [] = c"

lemma wcatc_flatten:
  shows "\<lbrakk>0 \<le> d2; wnnp u\<rbrakk> \<Longrightarrow>
   wcatc d c (VisibleWait d2 c2 # u) =
   wcat d c (d2 + wdur u) (wcatc d2 c2 u)"
proof (induct u arbitrary: d c d2 c2)
  case Nil
  then show ?case by simp
next
  case (Cons e u)
  show ?case
  proof (cases e)
    case (VisibleComm ct ch v)
    then show ?thesis using Cons by simp
  next
    case (VisibleWait d3 c3)
    from Cons.prems have d2nn: "0 \<le> d2" by simp
    from Cons.prems(2) VisibleWait have wn: "0 \<le> d3 \<and> wnnp u" by simp
    then have d3nn: "0 \<le> d3" and unn: "wnnp u" by simp_all
    have l1: "wcatc d c (VisibleWait d2 c2 # VisibleWait d3 c3 # u) =
        wcatc (d + d2) (wcat d c d2 c2) (VisibleWait d3 c3 # u)" by simp
    have l2: "wcatc (d + d2) (wcat d c d2 c2) (VisibleWait d3 c3 # u) =
        wcatc ((d + d2) + d3) (wcat (d + d2) (wcat d c d2 c2) d3 c3) u" by simp
    have r1: "wcatc d c (VisibleWait (d2 + d3) (wcat d2 c2 d3 c3) # u) =
        wcatc (d + (d2 + d3)) (wcat d c (d2 + d3) (wcat d2 c2 d3 c3)) u" by simp
    have wass: "wcat d c (d2 + d3) (wcat d2 c2 d3 c3) =
        wcat (d + d2) (wcat d c d2 c2) d3 c3"
      by (rule wcat_assoc[OF d2nn d3nn])
    have sass: "(d + d2) + d3 = d + (d2 + d3)" by simp
    have sumnn: "0 \<le> d2 + d3" using d2nn d3nn by simp
    have ih: "wcatc d c (VisibleWait (d2 + d3) (wcat d2 c2 d3 c3) # u) =
        wcat d c ((d2 + d3) + wdur u) (wcatc (d2 + d3) (wcat d2 c2 d3 c3) u)"
      by (rule Cons.hyps[OF sumnn unn])
    have lhs: "wcatc d c (VisibleWait d2 c2 # VisibleWait d3 c3 # u) =
        wcatc ((d + d2) + d3) (wcat (d + d2) (wcat d c d2 c2) d3 c3) u"
      by (simp only: l1 l2)
    have A: "wcatc d c (VisibleWait d2 c2 # VisibleWait d3 c3 # u) =
        wcatc d c (VisibleWait (d2 + d3) (wcat d2 c2 d3 c3) # u)"
      unfolding lhs r1 sass wass ..
    have eW: "e = VisibleWait d3 c3" by (rule VisibleWait)
    from A ih Cons.prems show ?thesis unfolding eW
      by (simp only: wdur.simps wcatc.simps add.assoc)
  qed
qed

lemma norm_lo_wait_cons:
  "norm_lo (VisibleWait d c # u) =
   VisibleWait (d + wdur u) (wcatc d c u) # norm_lo (wafter u)"
proof (induct u arbitrary: d c)
  case Nil
  then show ?case by simp
next
  case (Cons e u)
  show ?case
  proof (cases e)
    case (VisibleComm ct ch v)
    then show ?thesis using Cons by simp
  next
    case (VisibleWait d2 c2)
    have "norm_lo (VisibleWait d c # VisibleWait d2 c2 # u) =
        norm_lo (VisibleWait (d + d2) (wcat d c d2 c2) # u)" by simp
    also have "\<dots> =
        VisibleWait (d + d2 + wdur u) (wcatc (d + d2) (wcat d c d2 c2) u)
          # norm_lo (wafter u)"
      by (rule Cons.hyps)
    finally show ?thesis using VisibleWait by simp
  qed
qed

lemma norm_lo_nil [simp]: "norm_lo u = [] \<longleftrightarrow> u = []"
  by (induct u rule: norm_lo.induct) auto

lemma wafter_nnp: "wnnp u \<Longrightarrow> wnnp (wafter u)"
proof (induct u)
  case Nil then show ?case by simp
next
  case (Cons a u) then show ?case by (cases a) simp_all
qed

lemma norm_lo_cong_comm:
  assumes "norm_lo u = norm_lo v"
  shows "norm_lo (VisibleComm ct ch val # u) = norm_lo (VisibleComm ct ch val # v)"
  using assms by simp

text \<open>Prefixing the same visible wait preserves norm-equality: the merged
duration is additive and the merged curve concatenates on the left, so only
the norm-equality of the tails matters.\<close>

lemma norm_lo_cong_wait:
  assumes eq: "norm_lo u = norm_lo v" and nn: "wnnp u" "wnnp v"
  shows "norm_lo (VisibleWait d c # u) = norm_lo (VisibleWait d c # v)"
proof (cases u)
  case Nil
  then have "norm_lo v = []" using eq by (metis norm_lo.simps(1))
  then have "v = []" by (rule norm_lo_nil[THEN iffD1])
  with Nil show ?thesis by simp
next
  case (Cons e u')
  show ?thesis
  proof (cases e)
    case (VisibleComm ct ch val)
    then have uC: "u = VisibleComm ct ch val # u'" using Cons by simp
    show ?thesis
    proof (cases v)
      case Nil
      then show ?thesis using eq uC by simp
    next
      case (Cons e2 v')
      then show ?thesis using eq uC
        by (cases e2) (simp_all add: norm_lo_wait_cons)
    qed
  next
    case (VisibleWait d0 c0)
    then have uW: "u = VisibleWait d0 c0 # u'" using Cons by simp
    have d0nn: "0 \<le> d0" using nn(1) uW by simp
    show ?thesis
    proof (cases v)
      case Nil
      then show ?thesis using eq uW by (simp add: norm_lo_wait_cons)
    next
      case (Cons e2 v')
      then show ?thesis
      proof (cases e2)
        case (VisibleComm ct ch val)
        then have vC: "v = VisibleComm ct ch val # v'" using Cons by simp
        have contr: False
          using eq unfolding uW vC norm_lo_wait_cons by simp
        then show ?thesis ..
      next
        case (VisibleWait d0' c0')
        then have vW: "v = VisibleWait d0' c0' # v'" using Cons by simp
        have d0'nn: "0 \<le> d0'" using nn(2) vW by simp
        have hu: "norm_lo u =
            VisibleWait (d0 + wdur u') (wcatc d0 c0 u') # norm_lo (wafter u')"
          unfolding uW by (rule norm_lo_wait_cons)
        have hv: "norm_lo v =
            VisibleWait (d0' + wdur v') (wcatc d0' c0' v') # norm_lo (wafter v')"
          unfolding vW by (rule norm_lo_wait_cons)
        from eq[unfolded hu hv] have
          hd1: "d0 + wdur u' = d0' + wdur v'" and
          hd2: "wcatc d0 c0 u' = wcatc d0' c0' v'" and
          hd3: "norm_lo (wafter u') = norm_lo (wafter v')" by auto
        have lu: "norm_lo (VisibleWait d c # u) =
            VisibleWait (d + wdur u) (wcatc d c u) # norm_lo (wafter u)"
          by (rule norm_lo_wait_cons)
        have lv: "norm_lo (VisibleWait d c # v) =
            VisibleWait (d + wdur v) (wcatc d c v) # norm_lo (wafter v)"
          by (rule norm_lo_wait_cons)
        have dur: "wdur u = wdur v" using hd1 uW vW by simp
        have cat: "wcatc d c u = wcatc d c v"
        proof -
          have unn: "wnnp u'" using nn(1) uW by simp
          have vnn: "wnnp v'" using nn(2) vW by simp
          have "wcatc d c u = wcat d c (d0 + wdur u') (wcatc d0 c0 u')"
            unfolding uW by (rule wcatc_flatten[OF d0nn unn])
          also have "\<dots> = wcat d c (d0' + wdur v') (wcatc d0' c0' v')"
            using hd1 hd2 by simp
          also have "\<dots> = wcatc d c v"
            unfolding vW by (rule wcatc_flatten[OF d0'nn vnn, symmetric])
          finally show ?thesis .
        qed
        have wu: "wafter u = wafter u'" using uW by simp
        have wv: "wafter v = wafter v'" using vW by simp
        show ?thesis unfolding lu lv dur cat wu wv using hd3 by simp
      qed
    qed
  qed
qed

text \<open>Split congruence: replacing a leading visible wait by its prefix
split (with the curve restricted and shifted) preserves the normalisation,
provided the split is at a smaller positive time.\<close>

lemma norm_lo_split_cong:
  assumes t2: "0 < t2" and lt: "t2 < t1"
  shows "norm_lo (VisibleWait t2 (restrict f {0..t2}) # VisibleWait (t1 - t2)
        (restrict (\<lambda>u. (restrict f {0..t1}) (u + t2)) {0..t1 - t2}) # u)
       = norm_lo (VisibleWait t1 (restrict f {0..t1}) # u)"
proof -
  have pos: "0 < t1 - t2" using lt by simp
  have sec: "restrict (\<lambda>u. (restrict f {0..t1}) (u + t2)) {0..t1 - t2}
      = restrict (\<lambda>u. f (u + t2)) {0..t1 - t2}"
  proof (rule ext)
    fix x
    show "restrict (\<lambda>u. (restrict f {0..t1}) (u + t2)) {0..t1 - t2} x =
          restrict (\<lambda>u. f (u + t2)) {0..t1 - t2} x"
      using t2 by (auto simp: restrict_apply)
  qed
  have cat: "wcat t2 (restrict f {0..t2}) (t1 - t2)
      (restrict (\<lambda>u. f (u + t2)) {0..t1 - t2})
      = restrict f {0..t2 + (t1 - t2)}"
    by (rule wcat_merge_split) (use t2 pos in simp_all)
  have "norm_lo (VisibleWait t2 (restrict f {0..t2}) # VisibleWait (t1 - t2)
      (restrict (\<lambda>u. (restrict f {0..t1}) (u + t2)) {0..t1 - t2}) # u)
    = norm_lo (VisibleWait (t2 + (t1 - t2)) (wcat t2 (restrict f {0..t2}) (t1 - t2)
      (restrict (\<lambda>u. f (u + t2)) {0..t1 - t2})) # u)"
    unfolding sec by (cases u) simp_all
  also have "\<dots> = norm_lo (VisibleWait t1 (restrict f {0..t1}) # u)"
    using cat lt by simp
  finally show ?thesis .
qed


subsection \<open>The admissible initial family with actuator margin\<close>

definition lander_mass_family ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (char, real) exgstate set \<Rightarrow> bool" where
  "lander_mass_family Fmax mlo mhi wlo whi S \<longleftrightarrow>
    0 < mlo \<and> mlo \<le> mhi \<and> 0 < wlo \<and> wlo \<le> whi \<and> 0 < Fmax \<and>
    Fmax * Period < 2500 * mlo \<and> mhi * whi \<le> Fmax \<and> whi * Period < 2500 \<and>
    S \<noteq> {} \<and>
    (\<forall>x \<in> S. \<exists>lp lc sp sc. x = ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<and>
       lp HI = sp M \<and> lp LO = sp V \<and> lp LOW_W = sp W \<and>
       mlo \<le> sp M \<and> sp M \<le> mhi \<and> wlo \<le> sp W \<and> sp W \<le> whi \<and>
       sp Fc = sp M * sp W \<and> lander_force_ok Fmax sp \<and> 0 < sc M) \<and>
    (\<forall>lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2.
      ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> S \<longrightarrow>
      ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> S \<longrightarrow>
      lp1 LO = lp2 LO \<longrightarrow> lp1 LOW_W = lp2 LOW_W \<longrightarrow>
      ExParState (ExState (lp2(HI := lp1 HI),
          sp2(M := sp1 M, Fc := sp1 M * sp2 W))) (ExState (lc2, sc2(M := sp1 M)))
        \<in> S)"

text \<open>A concrete non-empty instance: a fixed low operating point
(\<^term>\<open>v0 = -1.5\<close>, \<^term>\<open>w0 = 3.732\<close>, a fixed point of \<^const>\<open>W_upd\<close>)
and a mass range with ample actuator margin: with \<^term>\<open>Fmax = 8200\<close>,
masses in \<^term>\<open>[1000, 2000]\<close>, and the W-bound \<^term>\<open>whi = 4\<close>, we have
\<^term>\<open>2000 * 4 \<le> (8200::real)\<close> and
\<^term>\<open>8200 * Period < 2500 * (1000::real)\<close>; and at the operating point
\<^term>\<open>W_upd v0 w0 = w0\<close>.\<close>

definition lander_family_example :: "(char, real) exgstate set" where
  "lander_family_example =
    {ExParState (ExState ((\<lambda>_. 0)(HI := m, LO := -1.5, LOW_W := 3.732),
                          (\<lambda>_. 0)(V := -1.5, W := 3.732, M := m,
                                      Fc := m * 3.732)))
               (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := m)))
    |m. 1000 \<le> m \<and> m \<le> 2000}"

lemma W_upd_fixpoint: "W_upd (-1.5) 3.732 = 3.732"
  unfolding W_upd_def by simp

lemma lander_family_example_ok:
  "lander_mass_family 8200 1000 2000 3 4 lander_family_example"
proof -
  have margins: "0 < (1000::real)" "(1000::real) \<le> 2000" "0 < (3::real)"
    "(3::real) \<le> 4" "0 < (8200::real)"
    "8200 * Period < 2500 * 1000" "2000 * 4 \<le> (8200::real)" "4 * Period < (2500::real)"
    unfolding Period_def by simp_all
  have ne: "lander_family_example \<noteq> {}"
    unfolding lander_family_example_def by force
  have mem: "\<forall>x \<in> lander_family_example. \<exists>lp lc sp sc.
      x = ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<and>
      lp HI = sp M \<and> lp LO = sp V \<and> lp LOW_W = sp W \<and>
      1000 \<le> sp M \<and> sp M \<le> 2000 \<and> 3 \<le> sp W \<and> sp W \<le> 4 \<and>
      sp Fc = sp M * sp W \<and> lander_force_ok 8200 sp \<and> 0 < sc M"
  proof (intro ballI)
    fix x assume xin: "x \<in> lander_family_example"
    then obtain m where m: "1000 \<le> m" "m \<le> 2000" and
      x: "x = ExParState (ExState ((\<lambda>_. 0)(HI := m, LO := -1.5, LOW_W := 3.732),
            (\<lambda>_. 0)(V := -1.5, W := 3.732, M := m, Fc := m * 3.732)))
            (ExState ((\<lambda>_. 0), (\<lambda>_. 0)(M := m)))"
      unfolding lander_family_example_def by blast
    have fcb: "m * 3.732 \<le> (8200::real)"
    proof -
      have "m * 3.732 \<le> 2000 * 3.732"
        using m(2) by (intro mult_right_mono) auto
      also have "\<dots> = (7464::real)" by simp
      also have "\<dots> \<le> (8200::real)" by simp
      finally show ?thesis .
    qed
    let ?lp = "(\<lambda>_. 0)(HI := m, LO := -1.5, LOW_W := 3.732)"
    let ?sp = "(\<lambda>_. 0)(V := -1.5, W := 3.732, M := m, Fc := m * 3.732)"
    let ?lc = "(\<lambda>_. 0::real)"
    let ?sc = "(\<lambda>_. 0::real)(M := m)"
    show "\<exists>lp lc sp sc. x = ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<and>
      lp HI = sp M \<and> lp LO = sp V \<and> lp LOW_W = sp W \<and>
      1000 \<le> sp M \<and> sp M \<le> 2000 \<and> 3 \<le> sp W \<and> sp W \<le> 4 \<and>
      sp Fc = sp M * sp W \<and> lander_force_ok 8200 sp \<and> 0 < sc M"
    proof (intro exI)
      show "x = ExParState (ExState (?lp, ?sp)) (ExState (?lc, ?sc)) \<and>
        ?lp HI = ?sp M \<and> ?lp LO = ?sp V \<and> ?lp LOW_W = ?sp W \<and>
        1000 \<le> ?sp M \<and> ?sp M \<le> 2000 \<and> 3 \<le> ?sp W \<and> ?sp W \<le> 4 \<and>
        ?sp Fc = ?sp M * ?sp W \<and> lander_force_ok 8200 ?sp \<and> 0 < ?sc M"
        using x m fcb by (auto simp: lander_force_ok_def)
    qed
  qed
  have cross: "\<forall>lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2.
      ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> lander_family_example \<longrightarrow>
      ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> lander_family_example \<longrightarrow>
      lp1 LO = lp2 LO \<longrightarrow> lp1 LOW_W = lp2 LOW_W \<longrightarrow>
      ExParState (ExState (lp2(HI := lp1 HI),
          sp2(M := sp1 M, Fc := sp1 M * sp2 W))) (ExState (lc2, sc2(M := sp1 M)))
        \<in> lander_family_example"
  proof (intro allI impI)
    fix lp1 lc1 sp1 sc1 lp2 lc2 sp2 sc2
    assume m1: "ExParState (ExState (lp1, sp1)) (ExState (lc1, sc1)) \<in> lander_family_example"
      and m2: "ExParState (ExState (lp2, sp2)) (ExState (lc2, sc2)) \<in> lander_family_example"
    from m1 obtain m1' where m1r: "1000 \<le> m1'" "m1' \<le> 2000"
      "lp1 = (\<lambda>_. 0)(HI := m1', LO := -1.5, LOW_W := 3.732)"
      "sp1 = (\<lambda>_. 0)(V := -1.5, W := 3.732, M := m1', Fc := m1' * 3.732)"
      unfolding lander_family_example_def by blast
    from m2 obtain m2' where m2r: "1000 \<le> m2'" "m2' \<le> 2000"
      "lp2 = (\<lambda>_. 0)(HI := m2', LO := -1.5, LOW_W := 3.732)"
      "sp2 = (\<lambda>_. 0)(V := -1.5, W := 3.732, M := m2', Fc := m2' * 3.732)"
      "lc2 = (\<lambda>_. 0)" "sc2 = (\<lambda>_. 0)(M := m2')"
      unfolding lander_family_example_def by blast
    show "ExParState (ExState (lp2(HI := lp1 HI),
        sp2(M := sp1 M, Fc := sp1 M * sp2 W))) (ExState (lc2, sc2(M := sp1 M)))
      \<in> lander_family_example"
      unfolding lander_family_example_def mem_Collect_eq
      apply (rule_tac x = "m1'" in exI)
      apply (simp add: m1r m2r fun_upd_twist)
      done
  qed
  show "lander_mass_family 8200 1000 2000 3 4 lander_family_example"
    unfolding lander_mass_family_def using margins ne mem cross by blast
qed

end
