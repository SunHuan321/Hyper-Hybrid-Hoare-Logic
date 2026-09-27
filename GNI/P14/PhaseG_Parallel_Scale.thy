theory PhaseG_Parallel_Scale
  imports PhaseG_Abs0_GNI
begin

section \<open>Mass scaling commutes with trace synchronization\<close>

fun scale_gstate :: "real \<Rightarrow> gstate \<Rightarrow> gstate" where
  "scale_gstate k (State s) = State (mass_scale k s)"
| "scale_gstate k (ParState a b) =
    ParState (scale_gstate k a) (scale_gstate k b)"

definition scale_comm_value :: "real \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> real" where
  "scale_comm_value k ch v = (if ch = ''m2c'' then k * v else v)"

fun scale_block :: "real \<Rightarrow> trace_block \<Rightarrow> trace_block" where
  "scale_block k (CommBlock ct ch v) =
    CommBlock ct ch (scale_comm_value k ch v)"
| "scale_block k (WaitBlock d p rdy) =
    WaitBlk d (\<lambda>t. scale_gstate k (p t)) rdy"

definition scale_trace :: "real \<Rightarrow> trace \<Rightarrow> trace" where
  "scale_trace k tr = map (scale_block k) tr"

lemma scale_block_WaitBlk:
  "scale_block k (WaitBlk d h rdy) =
    WaitBlk d (\<lambda>t. scale_gstate k (h t)) rdy"
proof -
  have hist: "restrict (\<lambda>t. scale_gstate k (restrict h {0..d} t)) {0..d}
      = restrict (\<lambda>t. scale_gstate k (h t)) {0..d}"
    by (rule ext) (simp add: restrict_apply)
  show ?thesis using hist by (simp add: WaitBlk_def)
qed

lemma scale_trace_cons [simp]:
  "scale_trace k (b # tr) = scale_block k b # scale_trace k tr"
  unfolding scale_trace_def by simp

lemma scale_trace_nil [simp]: "scale_trace k [] = []"
  unfolding scale_trace_def by simp

lemma lander_low_scale_gstate [simp]:
  "lander_low_gstate (scale_gstate k s) = lander_low_gstate s"
proof (cases s)
  case (State x)
  then show ?thesis by simp
next
  case (ParState a b)
  then show ?thesis by (cases a) simp_all
qed

lemma lander_obs_scale_trace:
  "lander_obs_trace (scale_trace k tr) = lander_obs_trace tr"
proof (induct tr)
  case Nil
  then show ?case by (simp add: scale_trace_def lander_obs_trace_def)
next
  case (Cons b tr)
  show ?case
  proof (cases b)
    case (CommBlock ct ch v)
    then show ?thesis using Cons
      by (simp add: lander_obs_trace_def scale_comm_value_def)
  next
    case (WaitBlock d p rdy)
    have curve: "restrict (lander_low_gstate \<circ>
        (restrict (\<lambda>t. scale_gstate k (p t)) {0..d})) {0..d}
       = restrict (lander_low_gstate \<circ> p) {0..d}"
      by (rule ext) (simp add: restrict_apply)
    then show ?thesis using Cons WaitBlock
      by (simp add: lander_obs_trace_def WaitBlk_def)
  qed
qed

theorem combine_blocks_scale:
  assumes cb: "combine_blocks chs tr1 tr2 tr"
  shows "combine_blocks chs (scale_trace k tr1) (scale_trace k tr2)
    (scale_trace k tr)"
  using cb
proof (induct rule: combine_blocks.induct)
  case combine_blocks_empty
  then show ?case by (simp add: combine_blocks.combine_blocks_empty)
next
  case (combine_blocks_pair1 ch comms blks1 blks2 blks v)
  then show ?case
    by (auto simp: scale_comm_value_def intro: combine_blocks.combine_blocks_pair1)
next
  case (combine_blocks_pair2 ch comms blks1 blks2 blks v)
  then show ?case
    by (auto simp: scale_comm_value_def intro: combine_blocks.combine_blocks_pair2)
next
  case (combine_blocks_unpair1 ch comms blks1 blks2 blks ct v)
  then show ?case
    by (auto simp: scale_comm_value_def intro: combine_blocks.combine_blocks_unpair1)
next
  case (combine_blocks_unpair2 ch comms blks1 blks2 blks ct v)
  then show ?case
    by (auto simp: scale_comm_value_def intro: combine_blocks.combine_blocks_unpair2)
next
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case
    by (auto simp: scale_block_WaitBlk intro: combine_blocks.combine_blocks_wait1)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then show ?case
    by (auto simp: scale_block_WaitBlk intro: combine_blocks.combine_blocks_wait2)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then show ?case
    by (auto simp: scale_block_WaitBlk intro: combine_blocks.combine_blocks_wait3)
qed

end
