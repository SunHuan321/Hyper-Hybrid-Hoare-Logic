theory PhaseG_BigStep_Wf
  imports "H3L_GNI.PhaseG_GNI_parallel_rich"
begin

section \<open>Well-formedness of real execution traces (P0.3 closure)\<close>

text \<open>
The rich observation-preservation theorem \<^theory_text>\<open>combine_rich_obs_left\<close>
is conditional on three trace well-formedness predicates:
\<^const>\<open>comm_only\<close> (all communications on the synchronized channels),
\<^const>\<open>wnn_tr\<close> (nonnegative wait durations), and \<^const>\<open>wf_waits\<close>
(State-shaped wait histories).  This theory discharges all three for
traces produced by \<^const>\<open>big_step\<close> of arbitrary single processes,
shows that combining two such traces yields nonnegative waits and IO
communications in the global trace, and packages everything into a
corollary connecting the left component's observation directly to the
global trace of a real parallel execution under the frozen attacker
model (hidden channel set \<^term>\<open>{''m2c''}\<close>).\<close>


subsection \<open>Cons lemmas for WaitBlk heads\<close>

lemma wnn_tr_WaitBlk:
  "wnn_tr (WaitBlk d p r # tr) \<longleftrightarrow> 0 \<le> d \<and> wnn_tr tr"
  unfolding WaitBlk_def wnn_tr_cons by simp

lemma comm_only_WaitBlk:
  "comm_only chs (WaitBlk d p r # tr) \<longleftrightarrow> comm_only chs tr"
  unfolding WaitBlk_def comm_only_cons by simp

lemma wf_waits_WaitBlk_const:
  "wf_waits (WaitBlk d (\<lambda>_. State s) r # tr) \<longleftrightarrow> wf_waits tr"
  unfolding WaitBlk_def wf_waits_cons
  by (auto simp: restrict_apply)

lemma wf_waits_WaitBlk_path:
  "wf_waits (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) r # tr) \<longleftrightarrow> wf_waits tr"
  unfolding WaitBlk_def wf_waits_cons
  by (auto simp: restrict_apply)

lemma wnn_tr_CommBlock:
  "wnn_tr (CommBlock ct ch v # tr) \<longleftrightarrow> wnn_tr tr"
  by (simp add: wnn_tr_cons)

lemma wf_waits_CommBlock:
  "wf_waits (CommBlock ct ch v # tr) \<longleftrightarrow> wf_waits tr"
  by (simp add: wf_waits_cons)

lemma comm_only_CommBlock:
  "comm_only chs (CommBlock ct ch v # tr) \<longleftrightarrow>
    ch \<in> chs \<and> comm_only chs tr"
  by (simp add: comm_only_cons)

lemma comm_only_nil: "comm_only chs []"
  unfolding comm_only_def by simp

lemma wnn_tr_nil: "wnn_tr []"
  unfolding wnn_tr_def by simp

lemma wf_waits_nil: "wf_waits []"
  unfolding wf_waits_def by simp

lemma comm_only_append:
  "comm_only chs (tr1 @ tr2) \<longleftrightarrow> comm_only chs tr1 \<and> comm_only chs tr2"
  by (induct tr1) (auto simp: comm_only_def)

lemma wnn_tr_append:
  "wnn_tr (tr1 @ tr2) \<longleftrightarrow> wnn_tr tr1 \<and> wnn_tr tr2"
  by (induct tr1) (auto simp: wnn_tr_def)

lemma wf_waits_append:
  "wf_waits (tr1 @ tr2) \<longleftrightarrow> wf_waits tr1 \<and> wf_waits tr2"
  by (induct tr1) (auto simp: wf_waits_def)

lemma comm_only_mono:
  assumes sub: "chs \<subseteq> chs'" and co: "comm_only chs tr"
  shows "comm_only chs' tr"
  using sub co unfolding comm_only_def
  by (auto split: trace_block.splits)


subsection \<open>Syntactic channel universe\<close>

fun comm_chan :: "comm \<Rightarrow> cname set" where
  "comm_chan (Send ch e) = {ch}"
| "comm_chan (Receive ch var) = {ch}"

fun proc_chans :: "proc \<Rightarrow> cname set" where
  "proc_chans (Cm c) = comm_chan c"
| "proc_chans Skip = {}"
| "proc_chans (Assign var e) = {}"
| "proc_chans (Havoc var) = {}"
| "proc_chans (Seq p1 p2) = proc_chans p1 \<union> proc_chans p2"
| "proc_chans (Assume b) = {}"
| "proc_chans (Wait e) = {}"
| "proc_chans (IChoice p1 p2) = proc_chans p1 \<union> proc_chans p2"
| "proc_chans (Rep p) = proc_chans p"
| "proc_chans (Cont ode b) = {}"
| "proc_chans (Interrupt ode b cs) =
     (\<Union>x \<in> set cs. comm_chan (fst x) \<union> proc_chans (snd x))"

lemma interrupt_chans_branch:
  assumes i: "i < length cs" and entry: "cs ! i = (c, p)"
  shows "comm_chan c \<union> proc_chans p \<subseteq> proc_chans (Interrupt ode b cs)"
proof -
  have mem: "(c, p) \<in> set cs" using i entry by (auto simp: in_set_conv_nth)
  have unf: "proc_chans (Interrupt ode b cs) =
      (\<Union>x \<in> set cs. comm_chan (fst x) \<union> proc_chans (snd x))"
    by simp
  show ?thesis
  proof
    fix y assume yin: "y \<in> comm_chan c \<union> proc_chans p"
    then have y2: "y \<in> comm_chan (fst (c, p)) \<union> proc_chans (snd (c, p))"
      by simp
    then show "y \<in> proc_chans (Interrupt ode b cs)"
      unfolding unf UN_iff using y2 mem
      by (rule_tac x = "(c, p)" in bexI, simp_all)
  qed
qed

lemma comm_only_interrupt_send_now:
  assumes i: "i < length cs" and entry: "cs ! i = (Send ch e, p2)"
    and ih: "comm_only (proc_chans p2) tr2"
  shows "comm_only (proc_chans (Interrupt ode b cs))
    (OutBlock ch v # tr2)"
proof -
  have mem: "(Send ch e, p2) \<in> set cs"
    using i entry by (auto simp: in_set_conv_nth)
  have mono: "comm_only (proc_chans (Interrupt ode b cs)) tr2"
    by (rule comm_only_mono[OF subset_trans[OF Un_upper2
        interrupt_chans_branch[OF i entry]] ih])
  have chinc: "ch \<in> comm_chan (fst (Send ch e, p2))" by simp
  have chmem: "ch \<in>
    (\<Union>x \<in> set cs. comm_chan (fst x) \<union> proc_chans (snd x))"
    by (rule UN_I[where a = "(Send ch e, p2)"], rule mem,
        rule UnI1, rule chinc)
  show ?thesis using mono chmem by (simp add: comm_only_cons)
qed

lemma comm_only_interrupt_recv_now:
  assumes i: "i < length cs" and entry: "cs ! i = (Receive ch var, p2)"
    and ih: "comm_only (proc_chans p2) tr2"
  shows "comm_only (proc_chans (Interrupt ode b cs))
    (InBlock ch v # tr2)"
proof -
  have mem: "(Receive ch var, p2) \<in> set cs"
    using i entry by (auto simp: in_set_conv_nth)
  have mono: "comm_only (proc_chans (Interrupt ode b cs)) tr2"
    by (rule comm_only_mono[OF subset_trans[OF Un_upper2
        interrupt_chans_branch[OF i entry]] ih])
  have chinc: "ch \<in> comm_chan (fst (Receive ch var, p2))" by simp
  have chmem: "ch \<in>
    (\<Union>x \<in> set cs. comm_chan (fst x) \<union> proc_chans (snd x))"
    by (rule UN_I[where a = "(Receive ch var, p2)"], rule mem,
        rule UnI1, rule chinc)
  show ?thesis using mono chmem by (simp add: comm_only_cons)
qed

lemma comm_only_interrupt_send_wait:
  "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
   comm_only (proc_chans p2) tr2 \<Longrightarrow>
   comm_only (proc_chans (Interrupt ode b cs))
     (WaitBlk d h rdy # OutBlock ch v # tr2)"
  by (simp only: comm_only_WaitBlk, rule comm_only_interrupt_send_now)

lemma comm_only_interrupt_recv_wait:
  "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
   comm_only (proc_chans p2) tr2 \<Longrightarrow>
   comm_only (proc_chans (Interrupt ode b cs))
     (WaitBlk d h rdy # InBlock ch v # tr2)"
  by (simp only: comm_only_WaitBlk, rule comm_only_interrupt_recv_now)

theorem big_step_comm_only:
  assumes run: "big_step C s tr s'"
  shows "comm_only (proc_chans C) tr"
  using run
proof (induct C s tr s' rule: big_step.induct)
  case skipB
  then show ?case by (simp add: comm_only_nil)
next
  case assignB
  then show ?case by (simp add: comm_only_nil)
next
  case HavocB
  then show ?case by (simp add: comm_only_nil)
next
  case (seqB p1 s1 tr1 s2 p2 tr2 s3)
  have m1: "comm_only (proc_chans p1 \<union> proc_chans p2) tr1"
    using comm_only_mono Un_upper1 seqB by blast
  have m2: "comm_only (proc_chans p1 \<union> proc_chans p2) tr2"
    using comm_only_mono Un_upper2 seqB by blast
  show ?case using m1 m2 by (simp add: comm_only_append)
next
  case AssumeB
  then show ?case by (simp add: comm_only_nil)
next
  case waitB1
  then show ?case by (simp add: comm_only_WaitBlk comm_only_nil)
next
  case waitB2
  then show ?case by (simp add: comm_only_nil)
next
  case sendB1
  then show ?case
    by (simp add: comm_only_CommBlock comm_only_nil)
next
  case sendB2
  then show ?case
    by (simp add: comm_only_WaitBlk comm_only_CommBlock
        comm_only_nil)
next
  case receiveB1
  then show ?case
    by (simp add: comm_only_CommBlock comm_only_nil)
next
  case receiveB2
  then show ?case
    by (simp add: comm_only_WaitBlk comm_only_CommBlock
        comm_only_nil)
next
  case IChoiceB1
  then show ?case
    by (metis comm_only_mono Un_upper1 proc_chans.simps(8))
next
  case IChoiceB2
  then show ?case
    by (metis comm_only_mono Un_upper2 proc_chans.simps(8))
next
  case RepetitionB1
  then show ?case by (simp add: comm_only_nil)
next
  case RepetitionB2
  then show ?case by (simp add: comm_only_append)
next
  case ContB1
  then show ?case by (simp add: comm_only_nil)
next
  case ContB2
  then show ?case by (simp add: comm_only_WaitBlk comm_only_nil)
next
  case (InterruptSendB1 i cs ch e p2 sa tr2 s2 ode b)
  then show ?case
    by (metis comm_only_interrupt_send_now)
next
  case (InterruptSendB2 d ode p s1 b i cs ch e p2 rdy tr2 s2)
  then show ?case
    by (metis comm_only_interrupt_send_wait)
next
  case (InterruptReceiveB1 i cs ch var p2 v sa tr2 s2 ode b)
  then show ?case
    by (metis comm_only_interrupt_recv_now)
next
  case (InterruptReceiveB2 d ode p s1 b i cs ch var p2 rdy v tr2 s2)
  then show ?case
    by (metis comm_only_interrupt_recv_wait)
next
  case InterruptB1
  then show ?case by (simp add: comm_only_nil)
next
  case InterruptB2
  then show ?case by (simp add: comm_only_WaitBlk comm_only_nil)
qed


theorem big_step_wnn_tr:
  assumes run: "big_step C s tr s'"
  shows "wnn_tr tr"
  using run
proof (induct C s tr s' rule: big_step.induct)
  case skipB
  then show ?case by (simp add: wnn_tr_nil)
next
  case assignB
  then show ?case by (simp add: wnn_tr_nil)
next
  case HavocB
  then show ?case by (simp add: wnn_tr_nil)
next
  case (seqB p1 s1 tr1 s2 p2 tr2 s3)
  then show ?case by (simp add: wnn_tr_append)
next
  case AssumeB
  then show ?case by (simp add: wnn_tr_nil)
next
  case waitB1
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_nil less_imp_le)
next
  case waitB2
  then show ?case by (simp add: wnn_tr_nil)
next
  case sendB1
  then show ?case by (simp add: wnn_tr_CommBlock wnn_tr_nil)
next
  case sendB2
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_CommBlock wnn_tr_nil
        less_imp_le)
next
  case receiveB1
  then show ?case by (simp add: wnn_tr_CommBlock wnn_tr_nil)
next
  case receiveB2
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_CommBlock wnn_tr_nil
        less_imp_le)
next
  case IChoiceB1
  then show ?case by metis
next
  case IChoiceB2
  then show ?case by metis
next
  case RepetitionB1
  then show ?case by (simp add: wnn_tr_nil)
next
  case RepetitionB2
  then show ?case by (simp add: wnn_tr_append)
next
  case ContB1
  then show ?case by (simp add: wnn_tr_nil)
next
  case ContB2
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_nil less_imp_le)
next
  case (InterruptSendB1 i cs ch e p2 sa tr2 s2 ode b)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (InterruptSendB2 d ode p s1 b i cs ch e p2 rdy tr2 s2)
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_CommBlock less_imp_le)
next
  case (InterruptReceiveB1 i cs ch var p2 v sa tr2 s2 ode b)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (InterruptReceiveB2 d ode p s1 b i cs ch var p2 rdy v tr2 s2)
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_CommBlock less_imp_le)
next
  case InterruptB1
  then show ?case by (simp add: wnn_tr_nil)
next
  case InterruptB2
  then show ?case
    by (simp add: wnn_tr_WaitBlk wnn_tr_nil less_imp_le)
qed

theorem big_step_wf_waits:
  assumes run: "big_step C s tr s'"
  shows "wf_waits tr"
  using run
proof (induct C s tr s' rule: big_step.induct)
  case skipB
  then show ?case by (simp add: wf_waits_nil)
next
  case assignB
  then show ?case by (simp add: wf_waits_nil)
next
  case HavocB
  then show ?case by (simp add: wf_waits_nil)
next
  case (seqB p1 s1 tr1 s2 p2 tr2 s3)
  then show ?case by (simp add: wf_waits_append)
next
  case AssumeB
  then show ?case by (simp add: wf_waits_nil)
next
  case waitB1
  then show ?case
    by (simp add: wf_waits_WaitBlk_const wf_waits_nil)
next
  case waitB2
  then show ?case by (simp add: wf_waits_nil)
next
  case sendB1
  then show ?case by (simp add: wf_waits_CommBlock wf_waits_nil)
next
  case sendB2
  then show ?case
    by (simp add: wf_waits_WaitBlk_const wf_waits_CommBlock
        wf_waits_nil)
next
  case receiveB1
  then show ?case by (simp add: wf_waits_CommBlock wf_waits_nil)
next
  case receiveB2
  then show ?case
    by (simp add: wf_waits_WaitBlk_const wf_waits_CommBlock
        wf_waits_nil)
next
  case IChoiceB1
  then show ?case by metis
next
  case IChoiceB2
  then show ?case by metis
next
  case RepetitionB1
  then show ?case by (simp add: wf_waits_nil)
next
  case RepetitionB2
  then show ?case by (simp add: wf_waits_append)
next
  case ContB1
  then show ?case by (simp add: wf_waits_nil)
next
  case ContB2
  then show ?case
    by (simp add: wf_waits_WaitBlk_path wf_waits_nil)
next
  case (InterruptSendB1 i cs ch e p2 sa tr2 s2 ode b)
  then show ?case by (simp add: wf_waits_CommBlock)
next
  case (InterruptSendB2 d ode p s1 b i cs ch e p2 rdy tr2 s2)
  then show ?case
    by (simp add: wf_waits_WaitBlk_path wf_waits_CommBlock)
next
  case (InterruptReceiveB1 i cs ch var p2 v sa tr2 s2 ode b)
  then show ?case by (simp add: wf_waits_CommBlock)
next
  case (InterruptReceiveB2 d ode p s1 b i cs ch var p2 rdy v tr2 s2)
  then show ?case
    by (simp add: wf_waits_WaitBlk_path wf_waits_CommBlock)
next
  case InterruptB1
  then show ?case by (simp add: wf_waits_nil)
next
  case InterruptB2
  then show ?case
    by (simp add: wf_waits_WaitBlk_path wf_waits_nil)
qed



theorem combine_wnn_tr:
  assumes cb: "combine_blocks chs tr1 tr2 tr"
    and n1: "wnn_tr tr1" and n2: "wnn_tr tr2"
  shows "wnn_tr tr"
  using cb n1 n2
proof (induct rule: combine_blocks.induct)
  case combine_blocks_empty
  then show ?case by (simp add: wnn_tr_nil)
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  then show ?case by (simp add: wnn_tr_CommBlock)
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case by (simp add: wnn_tr_WaitBlk)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have e1: "0 \<le> t1" "wnn_tr blks1"
    using combine_blocks_wait2.prems(1) unfolding wnn_tr_WaitBlk by auto
  have e2: "wnn_tr blks2"
    using combine_blocks_wait2.prems(2) unfolding wnn_tr_WaitBlk by auto
  have IHapp: "wnn_tr blks"
    apply (rule combine_blocks_wait2.hyps(2))
     apply (rule e1(2))
    unfolding wnn_tr_WaitBlk
    using combine_blocks_wait2.hyps(4) e2 by auto
  show ?case unfolding wnn_tr_WaitBlk using e1(1) IHapp by simp
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have e1: "wnn_tr blks1"
    using combine_blocks_wait3.prems(1) unfolding wnn_tr_WaitBlk by auto
  have e2: "0 \<le> t2" "wnn_tr blks2"
    using combine_blocks_wait3.prems(2) unfolding wnn_tr_WaitBlk by auto
  have IHapp: "wnn_tr blks"
    apply (rule combine_blocks_wait3.hyps(2))
    unfolding wnn_tr_WaitBlk
    using combine_blocks_wait3.hyps(4) e1 e2(2)
    by (auto simp: diff_le_eq less_imp_le)
  show ?case unfolding wnn_tr_WaitBlk using e2(1) IHapp by simp
qed


definition global_IO :: "cname set \<Rightarrow> trace \<Rightarrow> bool" where
  "global_IO chs tr \<longleftrightarrow>
    (\<forall>b \<in> set tr. case b of CommBlock ct ch v \<Rightarrow> ch \<in> chs \<longrightarrow> ct = IO
                       | _ \<Rightarrow> True)"

theorem combine_global_IO:
  assumes cb: "combine_blocks chs tr1 tr2 tr"
    and c1: "comm_only chs tr1" and c2: "comm_only chs tr2"
  shows "global_IO chs tr"
  using cb c1 c2
proof (induct rule: combine_blocks.induct)
  case combine_blocks_empty
  then show ?case by (simp add: global_IO_def)
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  have b1: "comm_only comms blks1"
    using combine_blocks_pair1.prems(1) unfolding comm_only_cons by simp
  have b2: "comm_only comms blks2"
    using combine_blocks_pair1.prems(2) unfolding comm_only_cons by simp
  have IH: "global_IO comms blks"
    using combine_blocks_pair1.hyps(3) b1 b2 by blast
  then show ?case
    by (simp add: global_IO_def WaitBlk_def)
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  have b1: "comm_only comms blks1"
    using combine_blocks_pair2.prems(1) unfolding comm_only_cons by simp
  have b2: "comm_only comms blks2"
    using combine_blocks_pair2.prems(2) unfolding comm_only_cons by simp
  have IH: "global_IO comms blks"
    using combine_blocks_pair2.hyps(3) b1 b2 by blast
  then show ?case
    by (simp add: global_IO_def WaitBlk_def)
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ch_type v)
  have chnotin: "ch \<notin> comms" by (rule combine_blocks_unpair1.hyps(1))
  have chin: "ch \<in> comms"
    using combine_blocks_unpair1.prems(1)[unfolded comm_only_cons,
      THEN conjunct1] by simp
  from chnotin chin have F: False by simp
  then show ?case by simp
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ch_type v)
  have chnotin: "ch \<notin> comms" by (rule combine_blocks_unpair2.hyps(1))
  have chin: "ch \<in> comms"
    using combine_blocks_unpair2.prems(2)[unfolded comm_only_cons,
      THEN conjunct1] by simp
  from chnotin chin have F: False by simp
  then show ?case by simp
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have b1: "comm_only comms blks1"
    using combine_blocks_wait1.prems(1) unfolding comm_only_WaitBlk by simp
  have b2: "comm_only comms blks2"
    using combine_blocks_wait1.prems(2) unfolding comm_only_WaitBlk by simp
  have IH: "global_IO comms blks"
    using combine_blocks_wait1.hyps(2) b1 b2 by blast
  then show ?case
    by (simp add: global_IO_def WaitBlk_def)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have b1: "comm_only comms blks1"
    using combine_blocks_wait2.prems(1) unfolding comm_only_WaitBlk by simp
  have b2: "comm_only comms blks2"
    using combine_blocks_wait2.prems(2) unfolding comm_only_WaitBlk by simp
  have b2s: "comm_only comms
    (WaitBlk (t2 - t1) (\<lambda>\<tau>. hist2 (\<tau> + t1)) rdy2 # blks2)"
    using b2 by (simp add: comm_only_WaitBlk)
  have IH: "global_IO comms blks"
    using combine_blocks_wait2.hyps(2) b1 b2s by blast
  then show ?case
    by (simp add: global_IO_def WaitBlk_def)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have b1: "comm_only comms blks1"
    using combine_blocks_wait3.prems(1) unfolding comm_only_WaitBlk by simp
  have b2: "comm_only comms blks2"
    using combine_blocks_wait3.prems(2) unfolding comm_only_WaitBlk by simp
  have b1s: "comm_only comms
    (WaitBlk (t1 - t2) (\<lambda>\<tau>. hist1 (\<tau> + t2)) rdy1 # blks1)"
    using b1 by (simp add: comm_only_WaitBlk)
  have IH: "global_IO comms blks"
    using combine_blocks_wait3.hyps(2) b1s b2 by blast
  then show ?case
    by (simp add: global_IO_def WaitBlk_def)
qed

corollary lander_global_obs_left_big_step:
  assumes b1: "big_step C1 s1 tr1 s1'"
    and b2: "big_step C2 s2 tr2 s2'"
    and cb: "combine_blocks chs tr1 tr2 tr"
    and ch1: "proc_chans C1 \<subseteq> chs" and ch2: "proc_chans C2 \<subseteq> chs"
  shows "norm_lo (lander_obs_trace tr) = norm_lo (robs chs {''m2c''} tr1)"
proof -
  have wf: "wf_waits tr1" by (rule big_step_wf_waits[OF b1])
  have co1: "comm_only chs tr1"
    by (rule comm_only_mono[OF ch1 big_step_comm_only[OF b1]])
  have co2: "comm_only chs tr2"
    by (rule comm_only_mono[OF ch2 big_step_comm_only[OF b2]])
  have n1: "wnn_tr tr1" by (rule big_step_wnn_tr[OF b1])
  have n2: "wnn_tr tr2" by (rule big_step_wnn_tr[OF b2])
  have ntr: "wnn_tr tr" by (rule combine_wnn_tr[OF cb n1 n2])
  have rio: "norm_lo (robs chs {''m2c''} tr) = norm_lo (robs chs {''m2c''} tr1)"
    by (rule combine_rich_obs_left[OF cb wf co1 co2 n1 n2 ntr])
  have gi: "global_IO chs tr"
    by (rule combine_global_IO[OF cb co1 co2])
  have bridge_tr: "robs chs {''m2c''} tr = lander_obs_trace tr"
  proof (rule robs_lander_global_IO)
    show "{''m2c''} = {''m2c''}" by (rule refl)
    show "\<forall>b\<in>set tr. case b of CommBlock ct ch v \<Rightarrow>
        ch \<in> chs \<longrightarrow> ct = IO | _ \<Rightarrow> True"
      by (fact gi[unfolded global_IO_def])
  qed
  show ?thesis using rio bridge_tr by simp
qed

end
