theory PhaseG_GNI_parallel
  imports PhaseG_GNI_hybrid
begin

section \<open>F4 foundations: duration conservation and split insensitivity\<close>

text \<open>
Two facts used by parallel observation reasoning:

  \<^item> \<^term>\<open>combine_duration_conserved\<close>: a synthesis spends exactly the
    total time of EACH component.  This is what makes the two sides'
    observations comparable (F4's premise that waiting pieces can be
    aligned as in F1 presupposes it).

  \<^item> \<^term>\<open>combine_wait_split_obs\<close>: in the unequal-duration branches
    the longer component's head block is split precisely in the way
    \<^term>\<open>obs_wait_split\<close> (F1) shows to be observationally invisible.

The channel-and-duration observer \<open>sync_obs\<close> below is preserved by
every \<open>combine_blocks\<close> derivation.  A richer observer that retains
communication values and low continuous curves remains separate work.
\<close>

fun total_dur :: "trace \<Rightarrow> real" where
  "total_dur [] = 0"
| "total_dur (WaitBlock d p r # tr) = d + total_dur tr"
| "total_dur (CommBlock c ch v # tr) = total_dur tr"

theorem combine_dur1:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow> total_dur tr1 = total_dur tr"
  by (induct rule: combine_blocks.induct) (simp_all add: WaitBlk_def)

theorem combine_dur2:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow> total_dur tr2 = total_dur tr"
  by (induct rule: combine_blocks.induct) (simp_all add: WaitBlk_def)

theorem combine_duration_conserved:
  assumes cb: "combine_blocks chs tr1 tr2 tr"
  shows "total_dur tr1 = total_dur tr" and "total_dur tr2 = total_dur tr"
  by (rule combine_dur1 [OF cb], rule combine_dur2 [OF cb])

text \<open>Unequal-duration splitting is observationally invisible (F1 instance):\<close>

lemma combine_wait_split_obs:
  assumes lt: "t1 < t2"
  shows "norm_obs (obs_tr [WaitBlk t2 h2 r2])
       = norm_obs (obs_tr [WaitBlk t1 h2 r2, WaitBlk (t2 - t1) (\<lambda>\<tau>. h2 (\<tau> + t1)) r2])"
proof -
  have "t1 + (t2 - t1) = t2" using lt by simp
  then show ?thesis by (simp add: WaitBlk_def obs_tr_def obs_block_def)
qed

lemma combine_wait2_split:
  assumes lt: "t1 < t2"
  shows "norm_obs (obs_tr [WaitBlk t2 h2 r2])
       = norm_obs (obs_tr [WaitBlk t1 h2 r2, WaitBlk (t2 - t1) (\<lambda>\<tau>. h2 (\<tau> + t1)) r2])"
  by (rule combine_wait_split_obs [OF lt])

lemma combine_wait3_split:
  assumes lt: "t2 < t1"
  shows "norm_obs (obs_tr [WaitBlk t1 h1 r1])
       = norm_obs (obs_tr [WaitBlk t2 h1 r1, WaitBlk (t1 - t2) (\<lambda>\<tau>. h1 (\<tau> + t2)) r1])"
  by (rule combine_wait_split_obs [OF lt])


subsection \<open>F4 main: observation preservation for synchronized channels\<close>

definition vis_block :: "cname set \<Rightarrow> trace_block \<Rightarrow> bool" where
  "vis_block chs b \<longleftrightarrow> (case b of
      CommBlock ct ch v \<Rightarrow> ch \<in> chs
    | WaitBlock d p r \<Rightarrow> True)"

definition sync_obs :: "cname set \<Rightarrow> trace \<Rightarrow> obs_event list" where
  "sync_obs chs tr = norm_obs (map obs_block (filter (vis_block chs) tr))"

lemma norm_obs_nil [simp]: "norm_obs xs = [] \<longleftrightarrow> xs = []"
  by (induct xs rule: norm_obs.induct) auto

lemma norm_obs_nil' [simp]: "[] = norm_obs xs \<longleftrightarrow> xs = []"
  by (metis norm_obs_nil)

text \<open>Preceding a list by the same wait event preserves norm-equality:\<close>

fun lead_Inl :: "obs_event list \<Rightarrow> real" where
  "lead_Inl [] = 0"
| "lead_Inl (Inl d # r) = d + lead_Inl r"
| "lead_Inl (Inr c # r) = 0"

fun after_Inl :: "obs_event list \<Rightarrow> obs_event list" where
  "after_Inl [] = []"
| "after_Inl (Inl d # r) = after_Inl r"
| "after_Inl (Inr c # r) = Inr c # r"

lemma norm_obs_Inl_cons:
  "norm_obs (Inl a # u) = Inl (a + lead_Inl u) # norm_obs (after_Inl u)"
  by (induct u arbitrary: a rule: lead_Inl.induct) auto

lemma norm_obs_lead:
  assumes "norm_obs u = Inl s # r"
  shows "s = lead_Inl u" and "r = norm_obs (after_Inl u)"
  using assms
  by (induct u rule: lead_Inl.induct, auto simp: norm_obs_Inl_cons)+

lemma norm_obs_cong_Inl:
  assumes eq: "norm_obs u = norm_obs v"
  shows "norm_obs (Inl a # u) = norm_obs (Inl a # v)"
proof (cases u)
  case Nil
  with eq show ?thesis by (cases v) (auto simp: norm_obs_nil)
next
  case (Cons b tl)
  show ?thesis
  proof (cases b)
    case (Inl d)
    have uh: "norm_obs (Inl d # tl) = Inl (d + lead_Inl tl) # norm_obs (after_Inl tl)"
      by (rule norm_obs_Inl_cons)
    have uh2: "norm_obs u = Inl (d + lead_Inl tl) # norm_obs (after_Inl tl)"
      using Cons Inl by (simp add: norm_obs_Inl_cons)
    obtain d' tl' where vh: "v = Inl d' # tl'"
    proof (cases v)
      case Nil
      with uh2 eq show ?thesis by simp
    next
      case (Cons b2 tl2)
      with uh2 eq show ?thesis
        by (cases b2) (auto simp: norm_obs_Inl_cons intro: that)
    qed
    have vh2: "norm_obs (Inl d' # tl') = Inl (d' + lead_Inl tl') # norm_obs (after_Inl tl')"
      by (rule norm_obs_Inl_cons)
    from eq Cons Inl vh have
      h12: "Inl (d + lead_Inl tl) # norm_obs (after_Inl tl)
          = Inl (d' + lead_Inl tl') # norm_obs (after_Inl tl')"
      by (simp add: norm_obs_Inl_cons)
    then have h1: "d + lead_Inl tl = d' + lead_Inl tl'"
      and h2: "norm_obs (after_Inl tl) = norm_obs (after_Inl tl')"
      by auto
    have "norm_obs (Inl a # Inl d # tl) = norm_obs (Inl (a + d) # tl)" by simp
    also have "\<dots> = Inl (a + d + lead_Inl tl) # norm_obs (after_Inl tl)"
      by (rule norm_obs_Inl_cons)
    also have "\<dots> = Inl (a + d' + lead_Inl tl') # norm_obs (after_Inl tl')"
      using h1 h2 by simp
    also have "\<dots> = norm_obs (Inl (a + d') # tl')"
      by (rule norm_obs_Inl_cons [symmetric])
    also have "\<dots> = norm_obs (Inl a # Inl d' # tl')" by simp
    finally show ?thesis using vh Cons Inl by simp
  next
    case (Inr c)
    have uh: "norm_obs (Inr c # tl) = Inr c # norm_obs tl" by simp
    have uh3: "norm_obs u = Inr c # norm_obs tl"
      using Cons Inr uh by simp
    obtain c' tl' where vh: "v = Inr c' # tl'" and ceq: "c = c'" and teq: "norm_obs tl = norm_obs tl'"
    proof (cases v)
      case Nil
      with uh3 eq show ?thesis by simp
    next
      case (Cons b2 tl2)
      with uh3 eq show ?thesis
        by (cases b2) (auto simp: norm_obs_Inl_cons intro: that)
    qed
    have "norm_obs (Inl a # Inr c # tl) = Inl a # norm_obs (Inr c # tl)" by simp
    also have "\<dots> = Inl a # Inr c # norm_obs tl" by simp
    also have "\<dots> = Inl a # Inr c' # norm_obs tl'" using ceq teq by simp
    also have "\<dots> = norm_obs (Inl a # Inr c' # tl')" by simp
    finally show ?thesis using vh Cons Inr ceq by simp
  qed
qed

lemma norm_obs_cong_Inr:
  assumes "norm_obs u = norm_obs v"
  shows "norm_obs (Inr c # u) = norm_obs (Inr c # v)"
  using assms by simp

lemma norm_obs_cong_split:
  assumes eq: "norm_obs v = norm_obs (Inl b # u)"
  shows "norm_obs (Inl a # v) = norm_obs (Inl (a + b) # u)"
proof -
  have "norm_obs (Inl a # v) = norm_obs (Inl a # Inl b # u)"
    by (rule norm_obs_cong_Inl[OF eq])
  also have "... = norm_obs (Inl (a + b) # u)" by simp
  finally show ?thesis .
qed

lemma norm_obs_cong_split_diff:
  assumes eq: "norm_obs v = norm_obs (Inl (t1 - t2) # u)"
    and lt: "t2 < t1"
  shows "norm_obs (Inl t2 # v) = norm_obs (Inl t1 # u)"
proof -
  have "norm_obs (Inl t2 # v) = norm_obs (Inl (t2 + (t1 - t2)) # u)"
    by (rule norm_obs_cong_split[OF eq])
  then show ?thesis using lt by simp
qed

theorem combine_obs_left:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow> sync_obs chs tr = sync_obs chs tr1"
  by (induct rule: combine_blocks.induct)
     (auto simp: sync_obs_def vis_block_def obs_block_def obs_tr_def WaitBlk_def
       intro: norm_obs_cong_Inl norm_obs_cong_Inr norm_obs_cong_split_diff)

theorem combine_obs_right:
  "combine_blocks chs tr1 tr2 tr \<Longrightarrow> sync_obs chs tr = sync_obs chs tr2"
  by (induct rule: combine_blocks.induct)
     (auto simp: sync_obs_def vis_block_def obs_block_def obs_tr_def WaitBlk_def
       intro: norm_obs_cong_Inl norm_obs_cong_Inr norm_obs_cong_split_diff)

theorem combine_obs_preserved:
  assumes c1: "combine_blocks chs tr1 tr2 tr"
      and c2: "combine_blocks chs tr1' tr2' tr'"
      and e1: "sync_obs chs tr1 = sync_obs chs tr1'"
  shows "sync_obs chs tr = sync_obs chs tr'"
  by (metis combine_obs_left c1 c2 e1)


end
