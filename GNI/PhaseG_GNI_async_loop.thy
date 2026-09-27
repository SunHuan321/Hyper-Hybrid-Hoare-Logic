theory PhaseG_GNI_async_loop
  imports PhaseG_GNI_comm
begin

section \<open>Two exit rounds with distinct trace observations\<close>

definition async_tag :: "real \<Rightarrow> char \<Rightarrow> real" where
  "async_tag h = (\<lambda>_. 0)(HI := h)"

definition async_state :: "real \<Rightarrow> state" where
  "async_state n = (\<lambda>_. 0)(LL2 := n)"

definition async_wait :: trace where
  "async_wait = [WaitBlk 1 (\<lambda>_. State (async_state 1)) ({}, {})]"

definition async_initial :: "(char, real) exstate set" where
  "async_initial = {(async_tag h, async_state n, []) |h n.
    h \<in> {1, 2} \<and> n \<in> {0, 1}}"

definition async_guard :: fform where
  "async_guard s \<longleftrightarrow> s LL2 = 1"

definition async_body :: proc where
  "async_body = Wait (\<lambda>_. 1); Assign LL2 (\<lambda>_. 0)"

definition async_done :: "(char, real) exstate set" where
  "async_done = {(async_tag h, async_state 0, tr) |h tr.
    h \<in> {1, 2} \<and> tr \<in> {[], async_wait}}"

lemma async_state_bit [simp]: "async_state n LL2 = n"
  by (simp add: async_state_def)

lemma async_tag_high [simp]: "async_tag h HI = h"
  by (simp add: async_tag_def)

lemma async_tag_low [simp]: "async_tag h LO = 0"
  by (simp add: async_tag_def)

lemma async_state_reset [simp]: "(async_state n)(LL2 := 0) = async_state 0"
  by (rule ext) (simp add: async_state_def)

lemma async_state_10_neq [simp]: "async_state 1 \<noteq> async_state 0"
  by (metis async_state_bit one_neq_zero)

lemma async_step:
  "sem (Assume async_guard; async_body) async_initial =
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
  unfolding async_initial_def async_guard_def async_body_def
    sem_seq sem_assume sem_wait sem_assign async_wait_def
  apply (auto simp: pproj_def async_state_def)
  apply (rule_tac x="(\<lambda>_. 0)(LL2 := 1)" in exI)
   apply auto
  apply (rule_tac x="(\<lambda>_. 0)(LL2 := 1)" in exI)
  apply auto
  done

lemma async_step_done:
  "sem (Assume async_guard; async_body)
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}} = {}"
proof -
  have "sem (Assume async_guard)
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}} = {}"
    unfolding async_guard_def sem_assume by (auto simp: pproj_def)
  then show ?thesis by (simp add: sem_seq)
qed

lemma async_round0:
  "{\<phi>\<in>async_initial. \<not> async_guard (pproj \<phi>)} =
    {(async_tag h, async_state 0, []) |h. h \<in> {1, 2}}"
  unfolding async_initial_def async_guard_def
  by (auto simp: pproj_def)

lemma async_round1:
  "{\<phi>\<in>iterate_sem 1 (Assume async_guard; async_body) async_initial.
    \<not> async_guard (pproj \<phi>)} =
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
  by (auto simp: async_step async_guard_def pproj_def async_state_def)

lemma async_round_ge2:
  "iterate_sem (Suc (Suc n)) (Assume async_guard; async_body) async_initial = {}"
proof (induct n)
  case 0
  have one: "iterate_sem 1 (Assume async_guard; async_body) async_initial =
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
    by (simp add: async_step)
  have two: "iterate_sem (Suc (Suc 0)) (Assume async_guard; async_body) async_initial =
    sem (Assume async_guard; async_body)
      {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
    by (simp only: iterate_sem.simps async_step)
  show ?case using two async_step_done by simp
next
  case (Suc n)
  have "iterate_sem (Suc (Suc (Suc n))) (Assume async_guard; async_body) async_initial =
    sem (Assume async_guard; async_body)
      (iterate_sem (Suc (Suc n)) (Assume async_guard; async_body) async_initial)"
    by (rule iterate_sem.simps(2))
  also have "... = {}" using Suc.hyps by simp
  finally show ?case .
qed

lemma async_output:
  "sem (while_cond async_guard async_body) async_initial = async_done"
proof -
  have split: "sem (while_cond async_guard async_body) async_initial =
    {(async_tag h, async_state 0, []) |h. h \<in> {1, 2}} \<union>
    {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
  proof (rule set_eqI, rule iffI)
    fix \<phi> assume "\<phi> \<in> sem (while_cond async_guard async_body) async_initial"
    then obtain n where hit:
      "\<phi> \<in> iterate_sem n (Assume async_guard; async_body) async_initial"
      "\<not> async_guard (pproj \<phi>)"
      unfolding while_cond_exit_rounds by blast
    show "\<phi> \<in> {(async_tag h, async_state 0, []) |h. h \<in> {1, 2}} \<union>
      {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
    proof (cases n)
      case 0
      have "\<phi> \<in> {\<psi>\<in>async_initial. \<not> async_guard (pproj \<psi>)}"
        using hit 0 by simp
      then show ?thesis using async_round0 by blast
    next
      case (Suc m)
      note nSuc = Suc
      then show ?thesis
      proof (cases m)
        case 0
        have "\<phi> \<in> {\<psi>\<in>iterate_sem 1 (Assume async_guard; async_body) async_initial.
          \<not> async_guard (pproj \<psi>)}"
          using hit Suc 0 by simp
        then show ?thesis using async_round1 by blast
      next
        case (Suc k)
        have empty: "iterate_sem n (Assume async_guard; async_body) async_initial = {}"
          using nSuc Suc async_round_ge2[of k] by simp
        then show ?thesis using hit by simp
      qed
    qed
  next
    fix \<phi> assume hit:
      "\<phi> \<in> {(async_tag h, async_state 0, []) |h. h \<in> {1, 2}} \<union>
        {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
    show "\<phi> \<in> sem (while_cond async_guard async_body) async_initial"
    proof (cases "\<phi> \<in> {(async_tag h, async_state 0, []) |h. h \<in> {1, 2}}")
      case True
      have "\<phi> \<in> {\<psi>\<in>iterate_sem 0 (Assume async_guard; async_body) async_initial.
        \<not> async_guard (pproj \<psi>)}"
        using True async_round0 by simp
      then show ?thesis unfolding while_cond_exit_rounds by blast
    next
      case False
      have "\<phi> \<in> {(async_tag h, async_state 0, async_wait) |h. h \<in> {1, 2}}"
        using hit False by blast
      then have "\<phi> \<in> {\<psi>\<in>iterate_sem 1 (Assume async_guard; async_body) async_initial.
        \<not> async_guard (pproj \<psi>)}"
        using async_round1 by simp
      then show ?thesis unfolding while_cond_exit_rounds by blast
    qed
  qed
  then show ?thesis unfolding async_done_def by auto
qed

lemma async_zero_run:
  "(async_tag h, async_state 0, [])
    \<in> sem (while_cond async_guard async_body) async_initial"
  if "h \<in> {1, 2}"
  using that by (auto simp: async_output async_done_def)

lemma async_one_run:
  "(async_tag h, async_state 0, async_wait)
    \<in> sem (while_cond async_guard async_body) async_initial"
  if "h \<in> {1, 2}"
  using that by (auto simp: async_output async_done_def)

theorem async_observations_distinct:
  "low_obs LL2 (async_tag h, async_state 0, []) \<noteq>
    low_obs LL2 (async_tag h, async_state 0, async_wait)"
  by (simp add: low_obs_def obs_tr_def obs_block_def async_wait_def
      WaitBlk_def pproj_def tproj_def)

theorem async_loop_gni:
  "gni_obs HI LO LL2 (sem (while_cond async_guard async_body) async_initial)"
proof (unfold async_output gni_obs_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> async_done" and m2: "\<phi>2 \<in> async_done"
    and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
  from m1 obtain h1 tr1 where p1: "\<phi>1 = (async_tag h1, async_state 0, tr1)"
    and h1: "h1 \<in> {1, 2}" and t1: "tr1 \<in> {[], async_wait}"
    unfolding async_done_def by blast
  from m2 obtain h2 tr2 where p2: "\<phi>2 = (async_tag h2, async_state 0, tr2)"
    and h2: "h2 \<in> {1, 2}" and t2: "tr2 \<in> {[], async_wait}"
    unfolding async_done_def by blast
  have mem: "(async_tag h1, async_state 0, tr2) \<in> async_done"
    using h1 t2 unfolding async_done_def by blast
  show "\<exists>\<phi>3\<in>async_done. lproj \<phi>3 HI = lproj \<phi>1 HI
      \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
      \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
    by (rule_tac x="(async_tag h1, async_state 0, tr2)" in bexI)
       (simp_all add: mem p1 p2 lproj_def low_obs_def pproj_def tproj_def)
qed

theorem async_loop_gni_curve:
  "gni_obs_c HI LO LL2 (sem (while_cond async_guard async_body) async_initial)"
proof (unfold async_output gni_obs_c_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> async_done" and m2: "\<phi>2 \<in> async_done"
    and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
  from m1 obtain h1 tr1 where p1: "\<phi>1 = (async_tag h1, async_state 0, tr1)"
    and h1: "h1 \<in> {1, 2}" and t1: "tr1 \<in> {[], async_wait}"
    unfolding async_done_def by blast
  from m2 obtain h2 tr2 where p2: "\<phi>2 = (async_tag h2, async_state 0, tr2)"
    and h2: "h2 \<in> {1, 2}" and t2: "tr2 \<in> {[], async_wait}"
    unfolding async_done_def by blast
  have mem: "(async_tag h1, async_state 0, tr2) \<in> async_done"
    using h1 t2 unfolding async_done_def by blast
  show "\<exists>\<phi>3\<in>async_done. lproj \<phi>3 HI = lproj \<phi>1 HI
      \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
      \<and> low_obs_c LL2 \<phi>3 = low_obs_c LL2 \<phi>2"
    by (rule_tac x="(async_tag h1, async_state 0, tr2)" in bexI)
       (simp_all add: mem p1 p2 lproj_def low_obs_c_def pproj_def tproj_def)
qed

definition async_tags :: "(real \<times> real) set" where
  "async_tags = {(0, h) |h. h \<in> {1, 2}}"

definition async_obs :: "(real \<times> obs_event list) set" where
  "async_obs = {(0, []), (0, [Inl 1])}"

definition async_cert ::
  "(real \<times> real) \<Rightarrow> (real \<times> obs_event list) \<Rightarrow>
    (char, real) exstate \<Rightarrow> bool" where
  "async_cert tag obs \<phi> \<longleftrightarrow> tag \<in> async_tags \<and> obs \<in> async_obs \<and>
    ((obs = (0, []) \<and> \<phi> = (async_tag (snd tag), async_state 0, [])) \<or>
     (obs = (0, [Inl 1]) \<and>
       (\<phi> = (async_tag (snd tag), async_state 1, []) \<or>
        \<phi> = (async_tag (snd tag), async_state 0, async_wait))))"

definition async_rank :: "(char, real) exstate \<Rightarrow> nat" where
  "async_rank \<phi> = (if async_guard (pproj \<phi>) then 1 else 0)"

lemma async_one_step_member:
  "(async_tag h, async_state 0, async_wait)
    \<in> sem (Assume async_guard; async_body)
      {(async_tag h, async_state 1, [])}"
proof -
  have a: "big_step (Assume async_guard) (async_state 1) [] (async_state 1)"
    by (rule AssumeB) (simp add: async_guard_def)
  have w: "big_step (Wait (\<lambda>_. 1)) (async_state 1)
    [WaitBlk 1 (\<lambda>_. State (async_state 1)) ({}, {})] (async_state 1)"
    by (rule waitB1) simp
  have r: "big_step (Assign LL2 (\<lambda>_. 0)) (async_state 1) [] (async_state 0)"
    using assignB[of LL2 "\<lambda>_. 0" "async_state 1"] by simp
  have b: "big_step async_body (async_state 1) async_wait (async_state 0)"
    using seqB[OF w r] unfolding async_body_def async_wait_def by simp
  have step: "big_step (Assume async_guard; async_body) (async_state 1)
    async_wait (async_state 0)"
    using seqB[OF a b] by simp
  show ?thesis using step by (auto simp: in_sem)
qed

theorem async_loop_gni_by_certificate:
  "gni_obs HI LO LL2
    (sem (while_cond async_guard async_body) async_initial)"
proof (rule gni_obs_while_wf_cover
    [where Tags=async_tags and Obs=async_obs and Inv=async_cert
      and rank="\<lambda>_ _. async_rank"])
  fix tag obs
  assume tag: "tag \<in> async_tags" and ob: "obs \<in> async_obs"
  show "\<exists>\<phi>\<in>async_initial. async_cert tag obs \<phi>"
  proof (cases "obs = (0, [])")
    case True
    have m: "(async_tag (snd tag), async_state 0, []) \<in> async_initial"
      using tag unfolding async_tags_def async_initial_def by auto
    show ?thesis by (rule bexI[OF _ m])
      (simp add: async_cert_def async_obs_def tag ob True)
  next
    case False
    have ow: "obs = (0, [Inl 1])" using ob False unfolding async_obs_def by auto
    have m: "(async_tag (snd tag), async_state 1, []) \<in> async_initial"
      using tag unfolding async_tags_def async_initial_def by auto
    show ?thesis by (rule bexI[OF _ m])
      (simp add: async_cert_def async_obs_def tag ob ow)
  qed
next
  fix tag obs \<phi>
  assume tag: "tag \<in> async_tags" and ob: "obs \<in> async_obs"
    and cert: "async_cert tag obs \<phi>" and guard: "async_guard (pproj \<phi>)"
  have p: "\<phi> = (async_tag (snd tag), async_state 1, [])"
    using cert guard unfolding async_cert_def async_guard_def
    by (auto simp: pproj_def)
  have m: "(async_tag (snd tag), async_state 0, async_wait)
    \<in> sem (Assume async_guard; async_body) {\<phi>}"
    using async_one_step_member by (simp add: p)
  have cert': "async_cert tag obs
    (async_tag (snd tag), async_state 0, async_wait)"
    using cert guard unfolding async_cert_def async_guard_def
    by (auto simp: p pproj_def)
  show "\<exists>\<psi>\<in>sem (Assume async_guard; async_body) {\<phi>}.
    async_cert tag obs \<psi> \<and> async_rank \<psi> < async_rank \<phi>"
    by (rule bexI[OF _ m])
       (simp add: cert' p async_rank_def async_guard_def pproj_def)
next
  fix tag obs \<phi>
  assume tag: "tag \<in> async_tags" and ob: "obs \<in> async_obs"
    and cert: "async_cert tag obs \<phi>" and exit: "\<not> async_guard (pproj \<phi>)"
  show "(lproj \<phi> LO, lproj \<phi> HI) = tag \<and> low_obs LL2 \<phi> = obs"
    using cert exit unfolding async_cert_def async_guard_def async_tags_def
      async_obs_def low_obs_def obs_tr_def obs_block_def async_wait_def
    by (auto simp: pproj_def lproj_def tproj_def WaitBlk_def)
next
  fix \<phi> assume m: "\<phi> \<in> sem (while_cond async_guard async_body) async_initial"
  show "(lproj \<phi> LO, lproj \<phi> HI) \<in> async_tags"
    using m unfolding async_output async_done_def async_tags_def
    by (auto simp: lproj_def)
next
  fix \<phi> assume m: "\<phi> \<in> sem (while_cond async_guard async_body) async_initial"
  show "low_obs LL2 \<phi> \<in> async_obs"
    using m unfolding async_output async_done_def async_obs_def
      low_obs_def obs_tr_def obs_block_def async_wait_def
    by (auto simp: pproj_def tproj_def WaitBlk_def)
qed

end
