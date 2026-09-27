(* Accepted in H3L_GNI on 2026-09-26. The preservation theorem requires
   comm_only, nonnegative waits, and a state-shaped left history. *)
theory PhaseG_GNI_parallel_rich
  imports PhaseG_Lander_Obs PhaseG_GNI_parallel
begin

section \<open>F4 rich: observation preservation under parallel synthesis (P0.3)\<close>

text \<open>
Acceptance item P0.3: per-branch theorems for \<^const>\<open>combine_blocks\<close>
that keep communication values (and directions where they exist), wait
durations, and the plant low curve, for the frozen observer of
\<^theory_text>\<open>PhaseG_Lander_Obs\<close>.

Modeling decisions (part of the frozen attacker model):

  \<^item> \<open>H\<close> is the set of hidden channels (for the lander: \<^term>\<open>{''m2c''}\<close>);
    their events are erased from observations.  They are instantaneous,
    so erasing them cannot shift any visible timestamp.

  \<^item> On the synchronized channels \<^term>\<open>chs\<close> the observer sees the
    canonical \<^term>\<open>IO\<close> direction of the global trace: the global trace
    contains only the synchronized event, so a component-side In/Out is
    presented as IO (\<^const>\<open>lander_low_gstate\<close>-based block mapper canonicalises both sides alike, which
    is exactly what makes the two sides of a synchronization indistinguishable).

  \<^item> On channels outside \<^term>\<open>chs\<close> (external communications) direction
    and value are kept.  For such traces the left-preservation theorem
    below needs all communications to be internal
    (an internality requirement): otherwise the global trace would contain
    right-component external events invisible in the left trace.

  \<^item> Wait blocks reveal duration and plant low curve
    (\<^const>\<open>lander_low_gstate\<close>, left projection); ready sets are not
    observed.  For the global wait curve (built on \<^term>\<open>ParState\<close>) to
    agree with the left component's curve, the left histories must be
    single-process shaped (a state-shapedness requirement) -- always the case for
    traces produced by \<^const>\<open>big_step\<close> of a single process.

The two unequal-duration split branches of \<^const>\<open>combine_blocks\<close> use
exactly the F1 insensitivity of \<^theory_text>\<open>PhaseG_Lander_Obs\<close>
(\<^theory_text>\<open>norm_lo_split_cong\<close>).
\<close>


subsection \<open>The rich block observation\<close>

fun rblock :: "cname set \<Rightarrow> cname set \<Rightarrow> trace_block \<Rightarrow> lander_obs_event option" where
  "rblock chs H (CommBlock ct ch v) =
     (if ch \<in> H then None
      else if ch \<in> chs then Some (VisibleComm IO ch v)
      else Some (VisibleComm ct ch v))"
| "rblock chs H (WaitBlock d p r) =
     Some (VisibleWait d (restrict (lander_low_gstate \<circ> p) {0..d}))"

definition robs :: "cname set \<Rightarrow> cname set \<Rightarrow> trace \<Rightarrow> lander_obs_event list" where
  "robs chs H tr = concat (map (\<lambda>b. case rblock chs H b of
      None \<Rightarrow> [] | Some e \<Rightarrow> [e]) tr)"

definition comm_only :: "cname set \<Rightarrow> trace \<Rightarrow> bool" where
  "comm_only chs tr \<longleftrightarrow>
    (\<forall>b \<in> set tr. case b of CommBlock ct ch v \<Rightarrow> ch \<in> chs | _ \<Rightarrow> True)"

definition wnn_tr :: "trace \<Rightarrow> bool" where
  "wnn_tr tr \<longleftrightarrow>
    (\<forall>b \<in> set tr. case b of WaitBlock d p r \<Rightarrow> 0 \<le> d | _ \<Rightarrow> True)"

definition wf_waits :: "trace \<Rightarrow> bool" where
  "wf_waits tr \<longleftrightarrow>
    (\<forall>b \<in> set tr. case b of WaitBlock d p r \<Rightarrow> (\<forall>\<tau>\<in>{0..d}. \<exists>s. p \<tau> = State s)
                        | _ \<Rightarrow> True)"

lemma comm_only_cons:
  "comm_only chs (b # tr) \<longleftrightarrow>
    (case b of CommBlock ct ch v \<Rightarrow> ch \<in> chs | _ \<Rightarrow> True) \<and> comm_only chs tr"
  unfolding comm_only_def by (cases b) auto

lemma wnn_tr_cons:
  "wnn_tr (b # tr) \<longleftrightarrow>
    (case b of WaitBlock d p r \<Rightarrow> 0 \<le> d | _ \<Rightarrow> True) \<and> wnn_tr tr"
  unfolding wnn_tr_def by (cases b) auto

lemma wf_waits_cons:
  "wf_waits (b # tr) \<longleftrightarrow>
    (case b of WaitBlock d p r \<Rightarrow> (\<forall>\<tau>\<in>{0..d}. \<exists>s. p \<tau> = State s) | _ \<Rightarrow> True)
    \<and> wf_waits tr"
  unfolding wf_waits_def by (cases b) auto

lemma robs_nil [simp]: "robs chs H [] = []"
  unfolding robs_def by simp

lemma robs_cons:
  "robs chs H (b # tr) =
   (case rblock chs H b of None \<Rightarrow> [] | Some e \<Rightarrow> [e]) @ robs chs H tr"
  unfolding robs_def by (cases "rblock chs H b") auto

lemma robs_lander_global_IO:
  assumes hidden: "H = {''m2c''}"
    and io: "\<forall>b\<in>set tr. case b of CommBlock ct ch v \<Rightarrow>
      ch \<in> chs \<longrightarrow> ct = IO | _ \<Rightarrow> True"
  shows "robs chs H tr = lander_obs_trace tr"
  using io unfolding hidden robs_def lander_obs_trace_def
  by (induct tr) (auto split: trace_block.splits)

lemma robs_wnnp:
  assumes nn: "wnn_tr tr" shows "wnnp (robs chs H tr)"
  using nn unfolding robs_def wnn_tr_def
  by (induct tr)
     (auto split: trace_block.splits option.splits)

lemma restrict_comp_restrict:
  "restrict (f \<circ> (restrict g D)) D = restrict (f \<circ> g) D"
proof (rule ext)
  fix x
  show "restrict (f \<circ> (restrict g D)) D x = restrict (f \<circ> g) D x"
    by (auto simp: restrict_apply comp_def)
qed

lemma rblock_WaitBlk [simp]:
  "rblock chs H (WaitBlk d p r) =
   Some (VisibleWait d (restrict (lander_low_gstate \<circ> p) {0..d}))"
  unfolding WaitBlk_def
  by (simp only: rblock.simps restrict_comp_restrict)

lemma lgstate_par_left:
  assumes wf: "\<forall>\<tau>\<in>{0..d}. \<exists>s. h1 \<tau> = State s"
  shows "restrict (lander_low_gstate \<circ> (\<lambda>\<tau>. ParState (h1 \<tau>) (h2 \<tau>))) {0..d}
       = restrict (lander_low_gstate \<circ> h1) {0..d}"
proof (rule ext)
  fix x
  show "restrict (lander_low_gstate \<circ> (\<lambda>\<tau>. ParState (h1 \<tau>) (h2 \<tau>))) {0..d} x =
        restrict (lander_low_gstate \<circ> h1) {0..d} x"
  proof (cases "x \<in> {0..d}")
    case True
    then obtain s where s: "h1 x = State s" using wf by blast
    then show ?thesis using True by (simp add: restrict_apply)
  next
    case False
    then have xn: "x \<notin> {0..d}" by simp
    then have L: "(restrict (lander_low_gstate \<circ> (\<lambda>\<tau>. ParState (h1 \<tau>) (h2 \<tau>))) {0..d}) x = undefined"
      unfolding restrict_apply by (rule if_not_P)
    have R: "(restrict (lander_low_gstate \<circ> h1) {0..d}) x = undefined"
      unfolding restrict_apply by (rule if_not_P[OF xn])
    show ?thesis using L R by simp
  qed
qed

lemma restrict_eq_on:
  assumes eq: "\<And>x. x \<in> D \<Longrightarrow> f x = g x"
  shows "restrict f D = restrict g D"
  by (rule ext) (auto simp: restrict_apply eq)

lemma shift_curve_bridge:
  fixes t1 t2 :: real
  assumes t2: "0 < t2" and lt: "t2 < t1"
  shows "restrict (lander_low_gstate \<circ> (\<lambda>u. h (u + t2))) {0..t1 - t2}
   = restrict (\<lambda>u. (restrict (lander_low_gstate \<circ> h) {0..t1}) (u + t2)) {0..t1 - t2}"
proof (rule restrict_eq_on)
  fix x assume xD: "x \<in> {0..t1 - t2}"
  have x0: "0 \<le> x" and xu: "x \<le> t1 - t2" using xD by auto
  have t2nn: "0 \<le> t2" using t2 by (smt (verit))
  have xlo: "0 \<le> x + t2" using add_nonneg_nonneg[OF x0 t2nn] by simp
  have xhi: "x + t2 \<le> t1"
  proof -
    have "x + t2 \<le> (t1 - t2) + t2" by (rule add_right_mono[OF xu])
    also have "\<dots> = t1" by simp
    finally show ?thesis .
  qed
  have xshift: "x + t2 \<in> {0..t1}"
    using xlo xhi by simp
  show "(lander_low_gstate \<circ> (\<lambda>u. h (u + t2))) x =
        (\<lambda>u. (restrict (lander_low_gstate \<circ> h) {0..t1}) (u + t2)) x"
    using xshift by (simp add: restrict_apply comp_def)
qed


subsection \<open>Left preservation (F4, per branch)\<close>

theorem combine_rich_obs_left:
  assumes cb: "combine_blocks chs tr1 tr2 tr"
  shows "wf_waits tr1 \<Longrightarrow> comm_only chs tr1 \<Longrightarrow> comm_only chs tr2 \<Longrightarrow>
    wnn_tr tr1 \<Longrightarrow> wnn_tr tr2 \<Longrightarrow> wnn_tr tr \<Longrightarrow>
    norm_lo (robs chs H tr) = norm_lo (robs chs H tr1)"
  using cb
proof (induct rule: combine_blocks.induct)
  case (combine_blocks_empty comms)
  then show ?case by simp
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  have ih: "norm_lo (robs comms H blks) = norm_lo (robs comms H blks1)"
  proof -
    have f1: "wf_waits blks1" using combine_blocks_pair1.prems(1) by (simp add: wf_waits_cons)
    have f2: "comm_only comms blks1" using combine_blocks_pair1.prems(2) by (simp add: comm_only_cons)
    have f3: "comm_only comms blks2" using combine_blocks_pair1.prems(3) by (simp add: comm_only_cons)
    have f4: "wnn_tr blks1" using combine_blocks_pair1.prems(4) by (simp add: wnn_tr_cons)
    have f5: "wnn_tr blks2" using combine_blocks_pair1.prems(5) by (simp add: wnn_tr_cons)
    have f6: "wnn_tr blks" using combine_blocks_pair1.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_pair1.hyps(3) f1 f2 f3 f4 f5 f6 by blast
  qed
  show ?case
  proof (cases "ch \<in> H")
    case True
    then show ?thesis using ih by (simp add: robs_cons)
  next
    case False
    then show ?thesis using ih combine_blocks_pair1.hyps(1)
      by (simp add: robs_cons norm_lo_cong_comm)
  qed
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  have ih: "norm_lo (robs comms H blks) = norm_lo (robs comms H blks1)"
  proof -
    have f1: "wf_waits blks1" using combine_blocks_pair2.prems(1) by (simp add: wf_waits_cons)
    have f2: "comm_only comms blks1" using combine_blocks_pair2.prems(2) by (simp add: comm_only_cons)
    have f3: "comm_only comms blks2" using combine_blocks_pair2.prems(3) by (simp add: comm_only_cons)
    have f4: "wnn_tr blks1" using combine_blocks_pair2.prems(4) by (simp add: wnn_tr_cons)
    have f5: "wnn_tr blks2" using combine_blocks_pair2.prems(5) by (simp add: wnn_tr_cons)
    have f6: "wnn_tr blks" using combine_blocks_pair2.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_pair2.hyps(3) f1 f2 f3 f4 f5 f6 by blast
  qed
  show ?case
  proof (cases "ch \<in> H")
    case True
    then show ?thesis using ih by (simp add: robs_cons)
  next
    case False
    then show ?thesis using ih combine_blocks_pair2.hyps(1)
      by (simp add: robs_cons norm_lo_cong_comm)
  qed
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  have ih: "norm_lo (robs comms H blks) = norm_lo (robs comms H blks1)"
  proof -
    have f1: "wf_waits blks1" using combine_blocks_unpair1.prems(1) by (simp add: wf_waits_cons)
    have f2: "comm_only comms blks1" using combine_blocks_unpair1.prems(2) by (simp add: comm_only_cons)
    have f3: "comm_only comms blks2" using combine_blocks_unpair1.prems(3) by (simp add: comm_only_cons)
    have f4: "wnn_tr blks1" using combine_blocks_unpair1.prems(4) by (simp add: wnn_tr_cons)
    have f5: "wnn_tr blks2" using combine_blocks_unpair1.prems(5) by (simp add: wnn_tr_cons)
    have f6: "wnn_tr blks" using combine_blocks_unpair1.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_unpair1.hyps(3) f1 f2 f3 f4 f5 f6 by blast
  qed
  show ?case
  proof (cases "ch \<in> H")
    case True
    then show ?thesis using ih by (simp add: robs_cons)
  next
    case False
    then show ?thesis using ih combine_blocks_unpair1.hyps(1)
      by (simp add: robs_cons norm_lo_cong_comm)
  qed
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  have chmem: "ch \<in> comms" using combine_blocks_unpair2.prems(3)
    by (auto simp: comm_only_cons)
  then show ?case using combine_blocks_unpair2.hyps(1) by simp
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist1 hist2 hist rdy t)
  have ih: "norm_lo (robs comms H blks) = norm_lo (robs comms H blks1)"
  proof -
    have f1: "wf_waits blks1" using combine_blocks_wait1.prems(1) by (simp add: wf_waits_cons)
    have f2: "comm_only comms blks1" using combine_blocks_wait1.prems(2) by (simp add: comm_only_cons)
    have f3: "comm_only comms blks2" using combine_blocks_wait1.prems(3) by (simp add: comm_only_cons)
    have f4: "wnn_tr blks1" using combine_blocks_wait1.prems(4) by (simp add: wnn_tr_cons)
    have f5: "wnn_tr blks2" using combine_blocks_wait1.prems(5) by (simp add: wnn_tr_cons)
    have f6: "wnn_tr blks" using combine_blocks_wait1.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_wait1.hyps(2) f1 f2 f3 f4 f5 f6 by blast
  qed
  have nn1: "wnnp (robs comms H blks)"
    using combine_blocks_wait1.prems(6) by (auto simp: wnn_tr_cons robs_wnnp)
  have nn2: "wnnp (robs comms H blks1)"
    using combine_blocks_wait1.prems(4) by (auto simp: wnn_tr_cons robs_wnnp)
  have wfl: "\<forall>\<tau>\<in>{0..t}. \<exists>s. hist2 \<tau> = State s"
  proof (intro ballI)
    fix \<tau> assume \<tau>: "\<tau> \<in> {0..t}"
    have wfblk: "wf_waits (WaitBlk t (\<lambda>x. hist2 x) rdy1 # blks1)"
      using combine_blocks_wait1.prems(1) by simp
    then have ballform: "\<forall>u\<in>{0..t}. \<exists>s. (restrict (\<lambda>x. hist2 x) {0..t}) u = State s"
      unfolding wf_waits_cons WaitBlk_def by simp
    with \<tau> obtain s where "(restrict (\<lambda>x. hist2 x) {0..t}) \<tau> = State s" by blast
    then show "\<exists>s. hist2 \<tau> = State s" using \<tau> by (simp add: restrict_apply)
  qed
  have cpar: "restrict (lander_low_gstate \<circ> hist1) {0..t}
      = restrict (lander_low_gstate \<circ> hist2) {0..t}"
    unfolding combine_blocks_wait1.hyps(4) using wfl by (rule lgstate_par_left)
  have Lside: "robs comms H (WaitBlk t hist1 rdy # blks) =
      VisibleWait t (restrict (lander_low_gstate \<circ> hist2) {0..t}) # robs comms H blks"
    by (simp add: robs_cons rblock_WaitBlk cpar)
  have Rside: "robs comms H (WaitBlk t (\<lambda>x. hist2 x) rdy1 # blks1) =
      VisibleWait t (restrict (lander_low_gstate \<circ> hist2) {0..t}) # robs comms H blks1"
    by (simp add: robs_cons rblock_WaitBlk)
  show ?case unfolding Lside Rside
    by (rule norm_lo_cong_wait[OF ih nn1 nn2])
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have ih: "norm_lo (robs comms H blks) = norm_lo (robs comms H blks1)"
  proof -
    have f1: "wf_waits blks1" using combine_blocks_wait2.prems(1) by (simp add: wf_waits_cons)
    have f2: "comm_only comms blks1" using combine_blocks_wait2.prems(2) by (simp add: comm_only_cons)
    have f3: "comm_only comms (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)"
      using combine_blocks_wait2.prems(3) by (simp add: comm_only_cons WaitBlk_def)
    have f4: "wnn_tr blks1" using combine_blocks_wait2.prems(4) by (simp add: wnn_tr_cons)
    have f5: "wnn_tr (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)"
      using combine_blocks_wait2.prems(5) combine_blocks_wait2.hyps(4)
      by (auto simp: wnn_tr_cons WaitBlk_def)
    have f6: "wnn_tr blks" using combine_blocks_wait2.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_wait2.hyps(2) f1 f2 f3 f4 f5 f6 by blast
  qed
  have nn1: "wnnp (robs comms H blks)"
    using combine_blocks_wait2.prems(6) by (auto simp: wnn_tr_cons robs_wnnp)
  have nn2: "wnnp (robs comms H blks1)"
    using combine_blocks_wait2.prems(4) by (auto simp: wnn_tr_cons robs_wnnp)
  have wfl: "\<forall>\<tau>\<in>{0..t1}. \<exists>s. hist1 \<tau> = State s"
  proof (intro ballI)
    fix \<tau> assume \<tau>: "\<tau> \<in> {0..t1}"
    have wfblk: "wf_waits (WaitBlk t1 (\<lambda>x. hist1 x) rdy1 # blks1)"
      using combine_blocks_wait2.prems(1) by simp
    then have ballform: "\<forall>u\<in>{0..t1}. \<exists>s. (restrict (\<lambda>x. hist1 x) {0..t1}) u = State s"
      unfolding wf_waits_cons WaitBlk_def by simp
    with \<tau> obtain s where "(restrict (\<lambda>x. hist1 x) {0..t1}) \<tau> = State s" by blast
    then show "\<exists>s. hist1 \<tau> = State s" using \<tau> by (simp add: restrict_apply)
  qed
  have cpar: "restrict (lander_low_gstate \<circ> hist) {0..t1}
      = restrict (lander_low_gstate \<circ> hist1) {0..t1}"
    unfolding combine_blocks_wait2.hyps(6) using wfl by (rule lgstate_par_left)
  have Lside: "robs comms H (WaitBlk t1 hist rdy # blks) =
      VisibleWait t1 (restrict (lander_low_gstate \<circ> hist1) {0..t1}) # robs comms H blks"
    by (simp add: robs_cons rblock_WaitBlk cpar)
  have Rside: "robs comms H (WaitBlk t1 (\<lambda>x. hist1 x) rdy1 # blks1) =
      VisibleWait t1 (restrict (lander_low_gstate \<circ> hist1) {0..t1}) # robs comms H blks1"
    by (simp add: robs_cons rblock_WaitBlk)
  show ?case unfolding Lside Rside
    by (rule norm_lo_cong_wait[OF ih nn1 nn2])
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have wfl: "\<forall>\<tau>\<in>{0..t1}. \<exists>s. hist1 \<tau> = State s"
  proof (intro ballI)
    fix \<tau> assume \<tau>: "\<tau> \<in> {0..t1}"
    have wfblk: "wf_waits (WaitBlk t1 (\<lambda>x. hist1 x) rdy1 # blks1)"
      using combine_blocks_wait3.prems(1) by simp
    then have ballform: "\<forall>u\<in>{0..t1}. \<exists>s. (restrict (\<lambda>x. hist1 x) {0..t1}) u = State s"
      unfolding wf_waits_cons WaitBlk_def by simp
    with \<tau> obtain s where "(restrict (\<lambda>x. hist1 x) {0..t1}) \<tau> = State s" by blast
    then show "\<exists>s. hist1 \<tau> = State s" using \<tau> by (simp add: restrict_apply)
  qed
  have wfshift: "wf_waits (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
  proof -
    have "wf_waits blks1" using combine_blocks_wait3.prems(1) by (simp add: wf_waits_cons)
    moreover have "\<forall>\<tau>\<in>{0..t1 - t2}. \<exists>s.
        (restrict (\<lambda>\<tau>. hist1 (\<tau> + t2)) {0..t1 - t2}) \<tau> = State s"
    proof (intro ballI)
      fix \<tau> assume \<tau>: "\<tau> \<in> {0..t1 - t2}"
      then have "\<tau> + t2 \<in> {0..t1}"
        using combine_blocks_wait3.hyps(4) combine_blocks_wait3.hyps(5) by auto
      then obtain s where s: "hist1 (\<tau> + t2) = State s" using wfl by blast
      then show "\<exists>s. (restrict (\<lambda>\<tau>. hist1 (\<tau> + t2)) {0..t1 - t2}) \<tau> = State s"
        using \<tau> by (auto simp: restrict_apply)
    qed
    ultimately show ?thesis by (simp add: wf_waits_cons WaitBlk_def)
  qed
  have wnnshift: "wnn_tr (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
  proof -
    have t21: "t2 \<le> t1" by (rule less_imp_le[OF combine_blocks_wait3.hyps(4)])
    have dnn: "0 \<le> t1 - t2" using t21 by simp
    show ?thesis using combine_blocks_wait3.prems(4) dnn
      by (auto simp: wnn_tr_cons WaitBlk_def)
  qed
  have ih: "norm_lo (robs comms H blks) =
      norm_lo (robs comms H (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1))"
  proof -
    have f1: "wf_waits (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
      by (rule wfshift)
    have f2: "comm_only comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
      using combine_blocks_wait3.prems(2) by (simp add: comm_only_cons WaitBlk_def)
    have f3: "comm_only comms blks2"
      using combine_blocks_wait3.prems(3) by (simp add: comm_only_cons)
    have f4: "wnn_tr (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
      by (rule wnnshift)
    have f5: "wnn_tr blks2" using combine_blocks_wait3.prems(5) by (simp add: wnn_tr_cons)
    have f6: "wnn_tr blks" using combine_blocks_wait3.prems(6) by (simp add: wnn_tr_cons)
    show ?thesis using combine_blocks_wait3.hyps(2) f1 f2 f3 f4 f5 f6 by blast
  qed
  have nn1: "wnnp (robs comms H blks)"
    using combine_blocks_wait3.prems(6) by (auto simp: wnn_tr_cons robs_wnnp)
  have nn2: "wnnp (robs comms H (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1))"
    by (rule robs_wnnp[OF wnnshift])
  have cpar: "restrict (lander_low_gstate \<circ> hist) {0..t2}
      = restrict (lander_low_gstate \<circ> hist1) {0..t2}"
  proof -
    have short: "\<forall>\<tau>\<in>{0..t2}. \<exists>s. hist1 \<tau> = State s"
    proof (intro ballI)
      fix \<tau> assume tm: "\<tau> \<in> {0..t2}"
      have lo: "0 \<le> \<tau>" and up: "\<tau> \<le> t2" using tm by auto
      have t21: "t2 \<le> t1" by (rule less_imp_le[OF combine_blocks_wait3.hyps(4)])
      have "\<tau> \<le> t1" by (rule order_trans[OF up t21])
      with lo show "\<exists>s. hist1 \<tau> = State s" using wfl by auto
    qed
    show ?thesis unfolding combine_blocks_wait3.hyps(6)
      using short by (rule lgstate_par_left)
  qed
  have cbr: "restrict (lander_low_gstate \<circ> (\<lambda>\<tau>. hist1 (\<tau> + t2))) {0..t1 - t2}
      = restrict (\<lambda>u. (restrict (lander_low_gstate \<circ> hist1) {0..t1}) (u + t2)) {0..t1 - t2}"
    by (rule shift_curve_bridge[OF combine_blocks_wait3.hyps(5)
        combine_blocks_wait3.hyps(4)])
  have step: "robs comms H (WaitBlk t2 hist rdy # blks) =
      VisibleWait t2 (restrict (lander_low_gstate \<circ> hist1) {0..t2})
      # robs comms H blks"
    by (simp add: robs_cons rblock_WaitBlk cpar)
  have lhs: "norm_lo (robs comms H (WaitBlk t2 hist rdy # blks)) =
      norm_lo (VisibleWait t2 (restrict (lander_low_gstate \<circ> hist1) {0..t2})
        # robs comms H (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1))"
    unfolding step
    by (rule norm_lo_cong_wait[OF ih nn1 nn2])
  have split: "norm_lo (VisibleWait t2 (restrict (lander_low_gstate \<circ> hist1) {0..t2})
      # robs comms H (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1))
      = norm_lo (VisibleWait t1 (restrict (lander_low_gstate \<circ> hist1) {0..t1})
          # robs comms H blks1)"
    using norm_lo_split_cong[OF combine_blocks_wait3.hyps(5)
        combine_blocks_wait3.hyps(4), of "lander_low_gstate \<circ> hist1"
          "robs comms H blks1"] cbr
    by (simp add: robs_cons rblock_WaitBlk)
  show ?case using lhs split
    by (simp add: robs_cons rblock_WaitBlk)
qed

text \<open>Two-run version: if two left components are observationally equal,
so are the two global traces.\<close>

theorem combine_rich_obs_preserved:
  assumes c1: "combine_blocks chs tr1 tr2 tr"
    and c2: "combine_blocks chs tr1' tr2' tr'"
    and w1: "wf_waits tr1" and w1': "wf_waits tr1'"
    and co1: "comm_only chs tr1" and co2: "comm_only chs tr2"
    and co1': "comm_only chs tr1'" and co2': "comm_only chs tr2'"
    and n1: "wnn_tr tr1" and n2: "wnn_tr tr2" and n: "wnn_tr tr"
    and n1': "wnn_tr tr1'" and n2': "wnn_tr tr2'" and n': "wnn_tr tr'"
    and eq: "norm_lo (robs chs H tr1) = norm_lo (robs chs H tr1')"
  shows "norm_lo (robs chs H tr) = norm_lo (robs chs H tr')"
  using combine_rich_obs_left[OF c1 w1 co1 co2 n1 n2 n]
    combine_rich_obs_left[OF c2 w1' co1' co2' n1' n2' n'] eq
  by simp

end
