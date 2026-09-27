theory PhaseG_GNI_trace
  imports PhaseG_GNI_v3
begin

section \<open>T1: observation algebra and trace-level GNI\<close>

text \<open>
Minimal observer model (roadmap \<^bold>\<open>T1/T5\<close>, \<^bold>\<open>\<S>4\<close>).  The attacker
observes, for every execution, the final value of the low program variable
TOGETHER with the communication/timing structure of the trace: the duration
of every wait block and the channel of every communication (data values are
not yet distinguished; adding visible low data requires channel labels and
is future work).

  \<^item> \<open>low_obs l \<phi> = (pproj \<phi> l, obs_tr (tproj \<phi>))\<close> is the total
    observation; \<open>gni_obs\<close> is \<^const>\<open>gni_final\<close> with the low-output
    conjunct replaced by equality of total observations.

  \<^item> \<^theory_text>\<open>gni_obs_imp_gni_final\<close>: the projection lemma (T5, forward
    direction) -- trace-level GNI implies final-state GNI, because the
    observation determines the low output.

  \<^item> \<^theory_text>\<open>wait_gni_final_holds\<close> / \<^theory_text>\<open>wait_gni_obs_fails\<close>:
    a program-level separation.  \<^term>\<open>Wait (\<lambda>\<sigma>. \<sigma> HH2)\<close> publishes the
    high input as a waiting duration.  All low outputs are unchanged, so
    final-state GNI holds trivially; but no run with the first execution's
    recorded high input can reproduce the second execution's trace, so
    trace-level GNI fails.  This is the concrete instantiation of the
    "same endpoints, different curves" counterexample class.
\<close>


subsection \<open>Observation algebra\<close>

type_synonym obs_event = "real + cname"

definition obs_block :: "trace_block \<Rightarrow> obs_event" where
  "obs_block blk = (case blk of
      WaitBlock d p rdy \<Rightarrow> Inl d
    | CommBlock ct ch v \<Rightarrow> Inr ch)"

definition obs_tr :: "trace \<Rightarrow> obs_event list" where
  "obs_tr = map obs_block"

definition low_obs :: "var \<Rightarrow> (('lvar, 'lval) exstate) \<Rightarrow> real \<times> obs_event list" where
  "low_obs l \<phi> = (pproj \<phi> l, obs_tr (tproj \<phi>))"

lemma obs_append:
  "obs_tr (t1 @ t2) = obs_tr t1 @ obs_tr t2"
  by (simp add: obs_tr_def)

lemma obs_wait_block:
  "obs_block (WaitBlk d p rdy) = Inl d"
  by (simp add: obs_block_def WaitBlk_def)

lemma obs_comm_block:
  "obs_block (CommBlock ct ch v) = Inr ch"
  by (simp add: obs_block_def)


subsection \<open>Trace-level GNI and the projection lemma\<close>

definition gni_obs :: "'lvar \<Rightarrow> 'lvar \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni_obs hi lo l S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. lproj \<phi>1 lo = lproj \<phi>2 lo \<longrightarrow>
      (\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
        \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
        \<and> low_obs l \<phi>3 = low_obs l \<phi>2))"

text \<open>A live coverage certificate records the pair (low input, high
input) and a target low observation. The terminal premise turns a live
promise into an actual observation.\<close>

theorem gni_obs_from_live_cover:
  fixes S :: "(('lvar, 'lval) exstate) set"
  assumes cov: "witness_cover (\<lambda>\<phi>. (lproj \<phi> lo, lproj \<phi> hi))
      may_complete Tags Obs S"
    and tags: "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> (lproj \<phi> lo, lproj \<phi> hi) \<in> Tags"
    and targets: "\<And>\<phi>. \<phi> \<in> S \<Longrightarrow> low_obs l \<phi> \<in> Obs"
    and terminal: "\<And>\<phi> obs. \<phi> \<in> S \<Longrightarrow> may_complete \<phi> obs
      \<Longrightarrow> low_obs l \<phi> = obs"
  shows "gni_obs hi lo l S"
proof (unfold gni_obs_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> S" and m2: "\<phi>2 \<in> S"
    and eq: "lproj \<phi>1 lo = lproj \<phi>2 lo"
  have tag: "(lproj \<phi>1 lo, lproj \<phi>1 hi) \<in> Tags" by (rule tags[OF m1])
  have target: "low_obs l \<phi>2 \<in> Obs" by (rule targets[OF m2])
  from cov have all: "\<forall>tag\<in>Tags. \<forall>obs\<in>Obs.
      \<exists>\<phi>\<in>S. (lproj \<phi> lo, lproj \<phi> hi) = tag \<and> may_complete \<phi> obs"
    unfolding witness_cover_def .
  from all[rule_format, OF tag target]
  obtain \<phi>3 where w: "\<phi>3 \<in> S"
    "(lproj \<phi>3 lo, lproj \<phi>3 hi) = (lproj \<phi>1 lo, lproj \<phi>1 hi)"
    "may_complete \<phi>3 (low_obs l \<phi>2)" by blast
  have hi: "lproj \<phi>3 hi = lproj \<phi>1 hi" using w(2) by simp
  have lo: "lproj \<phi>3 lo = lproj \<phi>2 lo" using w(2) eq by simp
  have obs: "low_obs l \<phi>3 = low_obs l \<phi>2"
    by (rule terminal[OF w(1) w(3)])
  show "\<exists>\<phi>3\<in>S. lproj \<phi>3 hi = lproj \<phi>1 hi
        \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
        \<and> low_obs l \<phi>3 = low_obs l \<phi>2"
    by (rule_tac x = "\<phi>3" in bexI) (simp_all add: hi lo obs w(1))
qed

lemma while_cond_exit_rounds:
  "sem (while_cond b C) S =
    (\<Union>n. {\<phi>\<in>iterate_sem n (Assume b; C) S. \<not> b (pproj \<phi>)})"
  unfolding while_cond_def sem_seq sem_while sem_assume lnot_def pproj_def
  by auto

text \<open>Different targets may exit in different loop rounds. The cover
premise is the program-specific witness and progress obligation; the theorem
connects such a round-indexed proof to trace-level GNI.\<close>

theorem gni_obs_while_from_exited_round_cover:
  fixes S :: "(('lvar, 'lval) exstate) set"
  assumes cover: "\<And>tag obs. tag \<in> Tags \<Longrightarrow> obs \<in> Obs \<Longrightarrow>
      \<exists>n \<phi>. \<phi> \<in> iterate_sem n (Assume b; C) S
        \<and> \<not> b (pproj \<phi>)
        \<and> (lproj \<phi> lo, lproj \<phi> hi) = tag
        \<and> low_obs l \<phi> = obs"
    and tags: "\<And>\<phi>. \<phi> \<in> sem (while_cond b C) S
      \<Longrightarrow> (lproj \<phi> lo, lproj \<phi> hi) \<in> Tags"
    and targets: "\<And>\<phi>. \<phi> \<in> sem (while_cond b C) S
      \<Longrightarrow> low_obs l \<phi> \<in> Obs"
  shows "gni_obs hi lo l (sem (while_cond b C) S)"
proof (rule gni_obs_from_live_cover
    [where may_complete = "\<lambda>\<phi> obs. low_obs l \<phi> = obs"
      and Tags = Tags and Obs = Obs])
  show "witness_cover (\<lambda>\<phi>. (lproj \<phi> lo, lproj \<phi> hi))
      (\<lambda>\<phi> obs. low_obs l \<phi> = obs) Tags Obs
      (sem (while_cond b C) S)"
  proof (unfold witness_cover_def, intro ballI)
    fix tag assume tag: "tag \<in> Tags"
    fix obs assume obs: "obs \<in> Obs"
    from cover[OF tag obs] obtain n \<phi> where w:
      "\<phi> \<in> iterate_sem n (Assume b; C) S" "\<not> b (pproj \<phi>)"
      "(lproj \<phi> lo, lproj \<phi> hi) = tag" "low_obs l \<phi> = obs"
      by blast
    have mem: "\<phi> \<in> sem (while_cond b C) S"
      using w(1) w(2) unfolding while_cond_exit_rounds by blast
    show "\<exists>\<phi>\<in>sem (while_cond b C) S.
        (lproj \<phi> lo, lproj \<phi> hi) = tag
        \<and> low_obs l \<phi> = obs"
      by (rule_tac x = "\<phi>" in bexI) (simp_all add: mem w(3) w(4))
  qed
next
  fix \<phi> assume "\<phi> \<in> sem (while_cond b C) S"
  then show "(lproj \<phi> lo, lproj \<phi> hi) \<in> Tags" by (rule tags)
next
  fix \<phi> assume "\<phi> \<in> sem (while_cond b C) S"
  then show "low_obs l \<phi> \<in> Obs" by (rule targets)
next
  fix \<phi> obs assume "\<phi> \<in> sem (while_cond b C) S"
    and "low_obs l \<phi> = obs"
  then show "low_obs l \<phi> = obs" by simp
qed

text \<open>A proof rule with explicit per-target certificates: an invariant
records the high-input tag and desired low observation, and a natural-number
rank forces each live witness to reach an exit. The two output-range premises
say which tags and observations the program can actually produce.\<close>

theorem gni_obs_while_wf_cover:
  fixes S :: "(('lvar, 'lval) exstate) set"
    and Inv :: "('lval \<times> 'lval) \<Rightarrow> (real \<times> obs_event list) \<Rightarrow>
      ('lvar, 'lval) exstate \<Rightarrow> bool"
    and rank :: "('lval \<times> 'lval) \<Rightarrow> (real \<times> obs_event list) \<Rightarrow>
      ('lvar, 'lval) exstate \<Rightarrow> nat"
  assumes start: "\<And>tag obs. tag \<in> Tags \<Longrightarrow> obs \<in> Obs \<Longrightarrow>
      \<exists>\<phi>\<in>S. Inv tag obs \<phi>"
    and progress: "\<And>tag obs \<phi>. tag \<in> Tags \<Longrightarrow> obs \<in> Obs \<Longrightarrow>
      Inv tag obs \<phi> \<Longrightarrow> b (pproj \<phi>) \<Longrightarrow>
      \<exists>\<psi>\<in>sem (Assume b; C) {\<phi>}.
        Inv tag obs \<psi> \<and> rank tag obs \<psi> < rank tag obs \<phi>"
    and exit: "\<And>tag obs \<phi>. tag \<in> Tags \<Longrightarrow> obs \<in> Obs \<Longrightarrow>
      Inv tag obs \<phi> \<Longrightarrow> \<not> b (pproj \<phi>) \<Longrightarrow>
      (lproj \<phi> lo, lproj \<phi> hi) = tag \<and> low_obs l \<phi> = obs"
    and tags: "\<And>\<phi>. \<phi> \<in> sem (while_cond b C) S \<Longrightarrow>
      (lproj \<phi> lo, lproj \<phi> hi) \<in> Tags"
    and targets: "\<And>\<phi>. \<phi> \<in> sem (while_cond b C) S \<Longrightarrow>
      low_obs l \<phi> \<in> Obs"
  shows "gni_obs hi lo l (sem (while_cond b C) S)"
proof (rule gni_obs_while_from_exited_round_cover[where Tags=Tags and Obs=Obs])
  fix tag obs assume tag: "tag \<in> Tags" and ob: "obs \<in> Obs"
  have hit: "\<exists>\<phi>\<in>sem (while_cond b C) S.
    Inv tag obs \<phi> \<and> \<not> b (pproj \<phi>)"
  proof (rule while_exists_wf[where Inv="Inv tag obs" and rank="rank tag obs"])
    show "\<exists>\<phi>\<in>S. Inv tag obs \<phi>" by (rule start[OF tag ob])
    fix \<phi> assume inv: "Inv tag obs \<phi>" and b: "b (pproj \<phi>)"
    show "\<exists>\<psi>\<in>sem (Assume b; C) {\<phi>}.
      Inv tag obs \<psi> \<and> rank tag obs \<psi> < rank tag obs \<phi>"
      by (rule progress[OF tag ob inv b])
  qed
  then obtain \<phi> where mem: "\<phi> \<in> sem (while_cond b C) S"
    and inv: "Inv tag obs \<phi>" and nb: "\<not> b (pproj \<phi>)" by blast
  from mem nb obtain n where round:
    "\<phi> \<in> iterate_sem n (Assume b; C) S"
    unfolding while_cond_exit_rounds by blast
  have out: "(lproj \<phi> lo, lproj \<phi> hi) = tag \<and> low_obs l \<phi> = obs"
    by (rule exit[OF tag ob inv nb])
  show "\<exists>n \<phi>. \<phi> \<in> iterate_sem n (Assume b; C) S
    \<and> \<not> b (pproj \<phi>) \<and> (lproj \<phi> lo, lproj \<phi> hi) = tag
    \<and> low_obs l \<phi> = obs"
    using round nb out by blast
next
  fix \<phi> assume "\<phi> \<in> sem (while_cond b C) S"
  then show "(lproj \<phi> lo, lproj \<phi> hi) \<in> Tags" by (rule tags)
next
  fix \<phi> assume "\<phi> \<in> sem (while_cond b C) S"
  then show "low_obs l \<phi> \<in> Obs" by (rule targets)
qed

text \<open>T5 forward direction: the observation determines the low output.\<close>

theorem gni_obs_imp_gni_final:
  assumes "gni_obs hi lo l S"
  shows "gni_final hi lo l S"
  using assms unfolding gni_obs_def gni_final_def low_obs_def by fastforce

text \<open>Whenever all low outputs coincide, final-state GNI holds trivially;
the separation example below is of exactly this shape.\<close>

lemma gni_final_low_const:
  assumes lc: "low_const l c S"
  shows "gni_final hi lo l (S :: ((char, real) exstate) set)"
proof (unfold gni_final_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> S" and m2: "\<phi>2 \<in> S"
     and loeq: "lproj \<phi>1 lo = lproj \<phi>2 lo"
  have pf1: "pproj \<phi>1 l = c"
    using lc [unfolded low_const_def, rule_format, OF m1] .
  have pf2: "pproj \<phi>2 l = c"
    using lc [unfolded low_const_def, rule_format, OF m2] .
  have key: "\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
          \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
          \<and> pproj \<phi>3 l = pproj \<phi>2 l"
    apply (rule_tac x = "\<phi>1" in bexI)
     apply (rule conjI)
    apply (rule refl)
     apply (rule conjI)
    apply (rule loeq)
    apply (simp add: pf1 pf2)
    apply (rule m1)
    done
  show "\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
          \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
          \<and> pproj \<phi>3 l = pproj \<phi>2 l"
    by (rule key)
qed


subsection \<open>The timing leak: same endpoints, different traces\<close>

definition wait_init1 :: "(char, real) exstate" where
  "wait_init1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1), [])"

definition wait_init2 :: "(char, real) exstate" where
  "wait_init2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2), [])"

definition S_wait :: "(char, real) exstate set" where
  "S_wait = {wait_init1, wait_init2}"

definition C_time :: proc where
  "C_time = Wait (\<lambda>\<sigma>. \<sigma> HH2)"

definition wait_run1 :: "(char, real) exstate" where
  "wait_run1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1),
      [WaitBlk 1 (\<lambda>_. State ((\<lambda>_. 0)(HH2 := 1))) ({}, {})])"

definition wait_run2 :: "(char, real) exstate" where
  "wait_run2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2),
      [WaitBlk 2 (\<lambda>_. State ((\<lambda>_. 0)(HH2 := 2))) ({}, {})])"

lemma wait_no_instant:
  assumes "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S_wait"
  shows "0 < (\<lambda>\<sigma>. \<sigma> HH2) \<sigma>\<^sub>p"
  using assms by (auto simp: S_wait_def wait_init1_def wait_init2_def)

lemma wait_run1_mem:
  "wait_run1 \<in> sem C_time S_wait"
proof -
  have src: "(fst wait_init1, fst (snd wait_init1), snd (snd wait_init1)) \<in> S_wait"
    by (simp add: S_wait_def)
  have pos: "0 < (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init1))"
    by (simp add: wait_init1_def)
  have "(fst wait_init1, fst (snd wait_init1),
          snd (snd wait_init1) @ [WaitBlk ((\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init1)))
              (\<lambda>_. State (fst (snd wait_init1))) ({}, {})])
        \<in> sem C_time S_wait"
    unfolding C_time_def sem_wait using src pos by blast
  moreover have "wait_run1 = (fst wait_init1, fst (snd wait_init1),
          snd (snd wait_init1) @ [WaitBlk ((\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init1)))
              (\<lambda>_. State (fst (snd wait_init1))) ({}, {})])"
    by (simp add: wait_run1_def wait_init1_def)
  ultimately show ?thesis by simp
qed

lemma wait_run2_mem:
  "wait_run2 \<in> sem C_time S_wait"
proof -
  have src: "(fst wait_init2, fst (snd wait_init2), snd (snd wait_init2)) \<in> S_wait"
    by (simp add: S_wait_def)
  have pos: "0 < (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init2))"
    by (simp add: wait_init2_def)
  have "(fst wait_init2, fst (snd wait_init2),
          snd (snd wait_init2) @ [WaitBlk ((\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init2)))
              (\<lambda>_. State (fst (snd wait_init2))) ({}, {})])
        \<in> sem C_time S_wait"
    unfolding C_time_def sem_wait using src pos by blast
  moreover have "wait_run2 = (fst wait_init2, fst (snd wait_init2),
          snd (snd wait_init2) @ [WaitBlk ((\<lambda>\<sigma>. \<sigma> HH2) (fst (snd wait_init2)))
              (\<lambda>_. State (fst (snd wait_init2))) ({}, {})])"
    by (simp add: wait_run2_def wait_init2_def)
  ultimately show ?thesis by simp
qed

lemma wait_mem_cases:
  assumes m: "\<phi> \<in> sem C_time S_wait"
  shows "\<phi> = wait_run1 \<or> \<phi> = wait_run2"
proof -
  obtain a b t where pd: "\<phi> = (a, b, t)" by (metis prod.exhaust)
  from m pd have mem: "(a, b, t) \<in> sem C_time S_wait" by simp
  from mem [unfolded C_time_def sem_wait] consider
      (inst) bp l0 where "(a, bp, l0) \<in> S_wait" "\<not> 0 < (\<lambda>\<sigma>. \<sigma> HH2) bp"
        "b = bp" "t = l0"
    | (wait) bp l0 where "(a, bp, l0) \<in> S_wait" "0 < (\<lambda>\<sigma>. \<sigma> HH2) bp"
        "t = l0 @ [WaitBlk ((\<lambda>\<sigma>. \<sigma> HH2) bp) (\<lambda>_. State bp) ({}, {})]"
        "b = bp"
    by blast
  then show ?thesis
  proof cases
    case inst
    from wait_no_instant [OF inst(1)] inst(2) show ?thesis by simp
  next
    case wait
    from wait(1) have "(a, bp, l0) = wait_init1 \<or> (a, bp, l0) = wait_init2"
      by (auto simp: S_wait_def)
    with wait pd show ?thesis
      by (auto simp: wait_run1_def wait_run2_def wait_init1_def wait_init2_def)
  qed
qed

lemma wait_low_const:
  "low_const LL2 0 (sem C_time S_wait)"
proof (unfold low_const_def, rule ballI)
  fix \<phi> assume m: "\<phi> \<in> sem C_time S_wait"
  from wait_mem_cases [OF m] have c: "\<phi> = wait_run1 \<or> \<phi> = wait_run2" .
  then show "pproj \<phi> LL2 = 0"
  proof (elim disjE)
    assume "\<phi> = wait_run1"
    then show ?thesis by (simp add: wait_run1_def pproj_def)
  next
    assume "\<phi> = wait_run2"
    then show ?thesis by (simp add: wait_run2_def pproj_def)
  qed
qed

theorem wait_gni_final_holds:
  "gni_final HI LO LL2 (sem C_time S_wait)"
  by (rule gni_final_low_const [OF wait_low_const])

theorem wait_gni_obs_fails:
  "\<not> gni_obs HI LO LL2 (sem C_time S_wait)"
proof -
  have loeq: "lproj wait_run1 LO = lproj wait_run2 LO"
    by (simp add: wait_run1_def wait_run2_def lproj_def)
  show ?thesis
  proof
    assume g: "gni_obs HI LO LL2 (sem C_time S_wait)"
    from g [unfolded gni_obs_def, rule_format,
            OF wait_run1_mem wait_run2_mem loeq]
    obtain \<phi>3 where w3: "\<phi>3 \<in> sem C_time S_wait"
      "lproj \<phi>3 HI = lproj wait_run1 HI"
      "lproj \<phi>3 LO = lproj wait_run2 LO"
      "low_obs LL2 \<phi>3 = low_obs LL2 wait_run2" by blast
    from wait_mem_cases [OF w3(1)] show False
    proof
      assume "\<phi>3 = wait_run1"
      with w3(4) show False
        by (simp add: wait_run1_def wait_run2_def low_obs_def obs_tr_def
                      tproj_def pproj_def obs_block_def WaitBlk_def)
    next
      assume "\<phi>3 = wait_run2"
      with w3(2) show False
        by (simp add: wait_run1_def wait_run2_def lproj_def)
    qed
  qed
qed


subsection \<open>Trace-level GNI of the havoc loop\<close>

text \<open>
Havoc neither touches the low program variable nor appends to the trace, so
under a trace-constant initial set (e.g. all traces empty) the havoc loop
satisfies the stronger trace-level assertion.
\<close>

definition t_const_at :: "trace \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "t_const_at tr S \<longleftrightarrow> (\<forall>\<phi>\<in>S. tproj \<phi> = tr)"

definition t_const :: "(('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "t_const S \<longleftrightarrow> (\<exists>tr. t_const_at tr S)"

lemma havoc_preserves_tconst:
  "hyper_hoare_triple (t_const_at tr) (Havoc x) (t_const_at tr)"
proof (rule hyper_hoare_tripleI)
  fix T assume a0: "t_const_at tr T"
  show "t_const_at tr (sem (Havoc x) T)"
  proof (unfold t_const_at_def, rule ballI)
    fix \<phi>' assume m: "\<phi>' \<in> sem (Havoc x) T"
    then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p l v where pd: "\<phi>' = (\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := v), l)"
      and src: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> T"
      unfolding sem_havoc by blast
    from a0 [unfolded t_const_at_def, rule_format, OF src]
    have "tproj (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) = tr" .
    then show "tproj \<phi>' = tr" using pd by (simp add: tproj_def)
  qed
qed

lemma t_const_at_union_closed:
  assumes "\<forall>S'\<in>F. t_const_at tr S'"
  shows "t_const_at tr (\<Union> F)"
  using assms unfolding t_const_at_def by blast

lemma havoc_rep_low_const:
  assumes lc: "low_const LL2 c S"
  shows "low_const LL2 c (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
proof -
  have h1: "low_const LL2 c (sem (Havoc HH2) S)"
    using havoc_preserves_low [OF HH2_LL2_neq(1)] lc
    unfolding hyper_hoare_triple_def by blast
  have h2: "low_const LL2 c (sem (Rep (Havoc HH2)) (sem (Havoc HH2) S))"
  proof (rule rep_invariant_param
          [where C = "Havoc HH2" and P = "\<lambda>c S. low_const LL2 c S"])
    fix T c' assume a: "low_const LL2 c' T"
    show "low_const LL2 c' (sem (Havoc HH2) T)"
      using havoc_preserves_low [OF HH2_LL2_neq(1)] a
      unfolding hyper_hoare_triple_def by blast
  next
    fix c' F assume hF: "\<forall>S'\<in>F. low_const LL2 c' S'"
    show "low_const LL2 c' (\<Union> F)" using hF unfolding low_const_def by blast
  next
    show "low_const LL2 c (sem (Havoc HH2) S)" using h1 .
  qed
  then show ?thesis unfolding sem_seq .
qed

lemma havoc_rep_t_const_at:
  assumes tc: "t_const_at tr S"
  shows "t_const_at tr (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
proof -
  have h1: "t_const_at tr (sem (Havoc HH2) S)"
    using havoc_preserves_tconst tc
    unfolding hyper_hoare_triple_def by blast
  have h2: "t_const_at tr (sem (Rep (Havoc HH2)) (sem (Havoc HH2) S))"
  proof (rule rep_invariant_param
          [where C = "Havoc HH2" and P = "\<lambda>tr S. t_const_at tr S"])
    fix T tr' assume a: "t_const_at tr' T"
    show "t_const_at tr' (sem (Havoc HH2) T)"
      using havoc_preserves_tconst a
      unfolding hyper_hoare_triple_def by blast
  next
    fix tr' F assume hF: "\<forall>S'\<in>F. t_const_at tr' S'"
    show "t_const_at tr' (\<Union> F)" by (rule t_const_at_union_closed [OF hF])
  next
    show "t_const_at tr (sem (Havoc HH2) S)" using h1 .
  qed
  then show ?thesis unfolding sem_seq .
qed

lemma gni_obs_havoc_rep_set:
  assumes c: "low_const LL2 c (S :: ((char, real) exstate) set)"
      and tr: "t_const_at tr S"
  shows "gni_obs HI LO LL2 (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
proof (unfold gni_obs_def, rule ballI, rule ballI, rule impI)
  have low_inv: "low_const LL2 c (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    by (rule havoc_rep_low_const [OF c])
  have tr_inv: "t_const_at tr (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    by (rule havoc_rep_t_const_at [OF tr])
  fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
       and m2: "\<phi>2 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
       and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
    from sem_lproj_src [OF m1] obtain src1 where
      src1: "src1 \<in> S" "lproj \<phi>1 = lproj src1" by blast
    obtain a q t where sq: "src1 = (a, q, t)" by (metis prod.exhaust)
    with src1(1) have qmem: "(a, q, t) \<in> S" by simp
    have wstep: "(a, q(HH2 := 0), t) \<in> sem (Havoc HH2) S"
      using qmem unfolding sem_havoc by blast
    have wrep: "(a, q(HH2 := 0), t) \<in> sem (Rep (Havoc HH2)) (sem (Havoc HH2) S)"
      using wstep sem_rep_subset by blast
    have wmem: "(a, q(HH2 := 0), t) \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
      unfolding sem_seq using wrep .
    have l1: "lproj \<phi>1 = a" using src1(2) sq by (simp add: lproj_def)
    have whi: "lproj (a, q(HH2 := 0), t) HI = lproj \<phi>1 HI"
      by (metis l1 lproj_def fst_conv)
    have wlo: "lproj (a, q(HH2 := 0), t) LO = lproj \<phi>2 LO"
      using l1 loeq by (metis lproj_def fst_conv)
    have wlow: "low_obs LL2 (a, q(HH2 := 0), t) = low_obs LL2 \<phi>2"
    proof -
      have p1: "pproj (a, q(HH2 := 0), t) LL2 = q LL2"
        by (simp add: pproj_def)
      also have "\<dots> = c"
        using c [unfolded low_const_def, rule_format, OF qmem]
        by (simp add: pproj_def)
      finally have pe: "pproj (a, q(HH2 := 0), t) LL2 = c" .
      have pe2: "pproj \<phi>2 LL2 = c" using m2 low_inv by (simp add: low_const_def)
      from pe pe2 have ppr: "pproj (a, q(HH2 := 0), t) LL2 = pproj \<phi>2 LL2" by simp
      from tr [unfolded t_const_at_def, rule_format, OF qmem]
      have "tproj (a, q, t) = tr" .
      then have tw: "tproj (a, q(HH2 := 0), t) = tr" by (simp add: tproj_def)
      have tt: "tproj \<phi>2 = tr" using m2 tr_inv by (simp add: t_const_at_def)
      from ppr tw tt show ?thesis unfolding low_obs_def by simp
    qed
    have key: "\<exists>\<phi>3 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S.
             lproj \<phi>3 HI = lproj \<phi>1 HI \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
             \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
      apply (rule_tac x = "(a, q(HH2 := 0), t)" in bexI)
       apply (rule conjI [OF whi conjI [OF wlo wlow]])
      apply (rule wmem)
      done
    show "\<exists>\<phi>3 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S.
             lproj \<phi>3 HI = lproj \<phi>1 HI \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
             \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
    by (rule key)
qed

theorem gni_obs_havoc_rep:
  "hyper_hoare_triple ((\<lambda>S. low_agree LL2 S \<and> t_const S)
        :: ((char, real) exstate) set \<Rightarrow> bool)
       (Seq (Havoc HH2) (Rep (Havoc HH2)))
       (gni_obs HI LO LL2)"
proof (rule hyper_hoare_tripleI)
  fix S :: "(char, real) exstate set"
  assume pre: "low_agree LL2 S \<and> t_const S"
  then obtain c where c: "low_const LL2 c S" by (auto simp: low_agree_def)
  from pre obtain tr where tr: "t_const_at tr S" by (auto simp: t_const_def)
  from c tr show "gni_obs HI LO LL2 (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    by (rule gni_obs_havoc_rep_set)
qed

end
