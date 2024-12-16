theory Language
  imports Analysis_More
begin

subsection \<open>Syntax\<close>

text \<open>Channel names\<close>
type_synonym cname = string

text \<open>Ready information.
  First component is set of channels that are ready to output.
  Second component is set of channels that are ready to input.\<close>
type_synonym rdy_info = "cname set \<times> cname set"

text \<open>Communications\<close>
datatype comm =
  Send cname exp        ("_[!]_" [110,108] 100)
| Receive cname var     ("_[?]_" [110,108] 100)

text \<open>HCSP processes\<close>
datatype proc =
  Cm comm
| Skip
| Assign var exp             ("_ ::= _" [99,95] 94)
| Havoc var                 ("_ ::= *" [99] 94)
| Seq proc proc           ("_; _" [91,90] 90)
| Assume fform         
| IChoice proc proc  \<comment> \<open>Nondeterminism\<close>
| Rep proc   \<comment> \<open>Nondeterministic repetition\<close>
| Cont ODE fform  \<comment> \<open>ODE with boundary\<close>
| Interrupt ODE fform "(comm \<times> proc) list"  \<comment> \<open>Interrupt\<close>

text \<open>Parallel of several HCSP processes\<close>
datatype pproc =
  Single proc
| Parallel pproc "cname set" pproc

text \<open>Global states\<close>
datatype gstate =
  State state
| ParState gstate gstate

subsection \<open>Traces\<close>

datatype comm_type = In | Out | IO

datatype trace_block =
  CommBlock comm_type cname real
| WaitBlock ereal "real \<Rightarrow> gstate" rdy_info

abbreviation "InBlock ch v \<equiv> CommBlock In ch v"
abbreviation "OutBlock ch v \<equiv> CommBlock Out ch v"
abbreviation "IOBlock ch v \<equiv> CommBlock IO ch v"

fun WaitBlk :: "ereal \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> trace_block" where
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
| "WaitBlk PInfty p rdy = WaitBlock PInfty (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
| "WaitBlk MInfty p rdy = WaitBlock MInfty (\<lambda>_. undefined) rdy"

lemma WaitBlk_simps [simp]:
  "WaitBlk (ereal d) p rdy = WaitBlock (ereal d) (\<lambda>\<tau>\<in>{0..d}. p \<tau>) rdy"
  "WaitBlk \<infinity> p rdy = WaitBlock \<infinity> (\<lambda>\<tau>\<in>{0..}. p \<tau>) rdy"
  "WaitBlk (-\<infinity>) p rdy = WaitBlock (-\<infinity>) (\<lambda>_. undefined) rdy"
  apply auto
  using WaitBlk.simps(2) infinity_ereal_def apply presburger
  using WaitBlk.simps(3) by auto

declare WaitBlk.simps [simp del]

lemma WaitBlk_not_Comm [simp]:
  "WaitBlk d p rdy \<noteq> CommBlock ch_type ch v"
  "CommBlock ch_type ch v \<noteq> WaitBlk d p rdy"
  by (cases d, auto)+

lemma restrict_cong_to_eq:
  fixes x :: real
  shows "restrict p1 {0..t} = restrict p2 {0..t} \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma restrict_cong_to_eq2:
  fixes x :: real
  shows "restrict p1 {0..} = restrict p2 {0..} \<Longrightarrow> 0 \<le> x \<Longrightarrow> p1 x = p2 x"
  apply (auto simp add: restrict_def) by metis

lemma WaitBlk_ext:
  fixes t1 t2 :: ereal
    and hist1 hist2 :: "real \<Rightarrow> gstate"
  shows "t1 = t2 \<Longrightarrow>
   (\<And>\<tau>::real. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
   WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
  apply (cases t1)
  apply (auto simp add: restrict_def)
  apply (rule ext) by auto

lemma WaitBlk_ext_real:
  fixes t1 :: real
    and t2 :: real
  shows "t1 = t2 \<Longrightarrow> (\<And>\<tau>. 0 \<le> \<tau> \<Longrightarrow> \<tau> \<le> t1 \<Longrightarrow> hist1 \<tau> = hist2 \<tau>) \<Longrightarrow> rdy1 = rdy2 \<Longrightarrow>
         WaitBlk (ereal t1) hist1 rdy1 = WaitBlk (ereal t2) hist2 rdy2"
  by (auto simp add: restrict_def)

lemma WaitBlk_cong:
  "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2 \<Longrightarrow> t1 = t2 \<and> rdy1 = rdy2"
  apply (cases t1) by (cases t2, auto)+

lemma WaitBlk_cong2:
  assumes "WaitBlk t1 hist1 rdy1 = WaitBlk t2 hist2 rdy2"
    and "0 \<le> t" "t \<le> t1"
  shows "hist1 t = hist2 t"
proof -
  have a: "t1 = t2" "rdy1 = rdy2"
    using assms WaitBlk_cong by auto
  show ?thesis
  proof (cases t1)
    case (real r)
    have real2: "t2 = ereal r"
      using real a by auto
    show ?thesis
      using assms(1)[unfolded real real2]
      apply auto using restrict_cong_to_eq assms ereal_less_eq(3) real by blast
  next
    case PInf
    have PInf2: "t2 = \<infinity>"
      using PInf a by auto
    show ?thesis
      using assms(1)[unfolded PInf PInf2] restrict_cong_to_eq2 assms by auto
  next
    case MInf
    show ?thesis
      using assms MInf by auto
  qed
qed

lemma WaitBlk_split1:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (ereal t1) p1 rdy = WaitBlk (ereal t1) p2 rdy"
proof (cases t)
  case (real r)
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded real] 
      using restrict_cong_to_eq[of p1 r p2 x] by auto
    done
next
  case PInf
  show ?thesis
    apply auto apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 x] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemma WaitBlk_split2:
  fixes t1 :: real
  assumes "WaitBlk t p1 rdy = WaitBlk t p2 rdy"
    and "0 < t1" "ereal t1 < t"
  shows "WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p1 (\<tau> + t1)) rdy =
         WaitBlk (t - ereal t1) (\<lambda>\<tau>::real. p2 (\<tau> + t1)) rdy"
proof (cases t)
  case (real r)
  have a: "t - ereal t1 = ereal (r - t1)"
    unfolding real by auto
  show ?thesis
    unfolding a apply auto apply (rule ext) subgoal for x
      using assms[unfolded real]
      using restrict_cong_to_eq[of p1 r p2 "x + t1"] by auto
    done
next
  case PInf
  have a: "t - ereal t1 = \<infinity>"
    unfolding PInf by auto
  show ?thesis
    unfolding a
    apply auto
    apply (rule ext) subgoal for x
      using assms[unfolded PInf] restrict_cong_to_eq2[of p1 p2 "x + t1"] by auto
    done
next
  case MInf
  then show ?thesis
    using assms by auto
qed

lemmas WaitBlk_split = WaitBlk_split1 WaitBlk_split2
declare WaitBlk_simps [simp del]

type_synonym trace = "trace_block list"

type_synonym tassn = "trace \<Rightarrow> bool"


subsection \<open>Big-step semantics for the single process\<close>

text \<open>Compute list of ready communications for an external choice.\<close>
fun rdy_of_echoice :: "(comm \<times> proc) list \<Rightarrow> rdy_info" where
  "rdy_of_echoice [] = ({}, {})"
| "rdy_of_echoice ((ch[!]e, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (insert ch (fst rdy), snd rdy))"
| "rdy_of_echoice ((ch[?]var, _) # rest) = (
    let rdy = rdy_of_echoice rest in
      (fst rdy, insert ch (snd rdy)))"

text \<open>big_step p s1 tr s2 means executing p starting from state s1 results
in a trace tr and final state s2.\<close>
inductive big_step :: "proc \<Rightarrow> state \<Rightarrow> trace \<Rightarrow> state \<Rightarrow> bool" where
  skipB: "big_step Skip s [] s"
| assignB: "big_step (var ::= e) s [] (s(var := e s))"
| HavocB: "big_step (var ::= *) s [] (s(var := v))"
| seqB: "big_step p1 s1 tr1 s2 \<Longrightarrow>
         big_step p2 s2 tr2 s3 \<Longrightarrow>
         big_step (p1; p2) s1 (tr1 @ tr2) s3"
| AssumeB: "b s1 \<Longrightarrow> big_step (Assume b) s1 [] s1"
| sendB1: "big_step (Cm (ch[!]e)) s [OutBlock ch (e s)] s"
| sendB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[!]e)) s
            [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
             OutBlock ch (e s)] s"
| sendB3: "big_step (Cm (ch[!]e)) s [WaitBlk \<infinity> (\<lambda>_. State s) ({ch}, {})] s"
| receiveB1: "big_step (Cm (ch[?]var)) s [InBlock ch v] (s(var := v))"
| receiveB2: "(d::real) > 0 \<Longrightarrow> big_step (Cm (ch[?]var)) s
            [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
             InBlock ch v] (s(var := v))"
| receiveB3: "big_step (Cm (ch[?]var)) s [WaitBlk \<infinity> (\<lambda>_. State s) ({}, {ch})] s"
| IChoiceB1: "big_step p1 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| IChoiceB2: "big_step p2 s1 tr s2 \<Longrightarrow> big_step (IChoice p1 p2) s1 tr s2"
| RepetitionB1: "big_step (Rep p) s [] s"
| RepetitionB2: "big_step p s1 tr1 s2 \<Longrightarrow> big_step (Rep p) s2 tr2 s3 \<Longrightarrow>
    tr = tr1 @ tr2 \<Longrightarrow>
    big_step (Rep p) s1 tr s3"
| ContB1: "\<not>b s \<Longrightarrow> big_step (Cont ode b) s [] s"
| ContB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    big_step (Cont ode b) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
| InterruptSendB1: "i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    big_step p2 s tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (OutBlock ch (e s) # tr2) s2"
| InterruptSendB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Send ch e, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 (p d) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      OutBlock ch (e (p d)) # tr2) s2"
| InterruptReceiveB1: "i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    big_step p2 (s(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s (InBlock ch v # tr2) s2"
| InterruptReceiveB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow> p 0 = s1 \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    i < length cs \<Longrightarrow> cs ! i = (Receive ch var, p2) \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step p2 ((p d)(var := v)) tr2 s2 \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 (WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy #
                                      InBlock ch v # tr2) s2"
| InterruptB1: "\<not>b s \<Longrightarrow> big_step (Interrupt ode b cs) s [] s"
| InterruptB2: "d > 0 \<Longrightarrow> ODEsol ode p d \<Longrightarrow>
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<Longrightarrow>
    \<not>b (p d) \<Longrightarrow> p 0 = s1 \<Longrightarrow> p d = s2 \<Longrightarrow>
    rdy = rdy_of_echoice cs \<Longrightarrow>
    big_step (Interrupt ode b cs) s1 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) rdy] s2"

lemma big_step_cong:
  "big_step c s1 tr s2 \<Longrightarrow> tr = tr' \<Longrightarrow> s2 = s2' \<Longrightarrow> big_step c s1 tr' s2'"
  by auto

inductive_cases skipE: "big_step Skip s1 tr s2"
inductive_cases assignE: "big_step (Assign var e) s1 tr s2"
inductive_cases HavocE: "big_step (Havoc var) s1 tr s2"
inductive_cases sendE: "big_step (Cm (ch[!]e)) s1 tr s2"
inductive_cases receiveE: "big_step (Cm (ch[?]var)) s1 tr s2"
inductive_cases seqE: "big_step (Seq p1 p2) s1 tr s2"
inductive_cases AssumeE: "big_step (Assume b) s1 tr s2"
inductive_cases waitE: "big_step (Wait d) s1 tr s2"
inductive_cases echoiceE: "big_step (EChoice es) s1 tr s2"
inductive_cases ichoiceE: "big_step (IChoice p1 p2) s1 tr s2"
inductive_cases contE: "big_step (Cont ode b) s1 tr s2"
inductive_cases interruptE: "big_step (Interrupt ode b cs) s1 tr s2"

subsection \<open>Extended Semantics for the single process\<close>

definition sem :: "proc \<Rightarrow> (state \<times> trace) set \<Rightarrow> (state \<times> trace) set"
  where "sem C S = {(\<sigma>', l @ l') | \<sigma> \<sigma>' l l'. (\<sigma>, l) \<in> S \<and> big_step C \<sigma> l' \<sigma>'}"

lemma in_sem: 
  "\<phi> \<in> sem C S \<longleftrightarrow> (\<exists>\<sigma> l l'. (\<sigma>, l) \<in> S \<and> big_step C \<sigma> l' (fst \<phi>) \<and> (snd \<phi>) = l @ l')" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain \<sigma> \<sigma>' l l' where "\<phi> = (\<sigma>', l @ l')" "(\<sigma>, l) \<in> S"  "big_step C \<sigma> l' \<sigma>'"
    using sem_def[of C S] by auto
  then show ?B
    by auto
next
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) mem_Collect_eq prod.collapse sem_def)
qed

text \<open>Lemma: Useful properties of the extended semantics\<close>
lemma sem_seq:
  "sem (Seq C1 C2) S = sem C2 (sem C1 S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain s1 tr0 tr3 where a0: "(s1, tr0) \<in> S"  "big_step (Seq C1 C2) s1 tr3 (fst \<phi>)" "snd \<phi> = tr0 @ tr3"
      using in_sem by auto
    then obtain tr1 s2 tr2 where "big_step C1 s1 tr1 s2" "big_step C2 s2 tr2 (fst \<phi>)" "tr3 = tr1 @ tr2"
      by (meson seqE)
    with a0 show "\<phi> \<in> ?B"
      by (metis append.assoc in_sem split_pairs)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<phi> assume "\<phi> \<in> ?B"
    then obtain s2 tr1' tr2 where b0: "(s2, tr1') \<in> sem C1 S" "big_step C2 s2 tr2 (fst \<phi>)" "snd \<phi> = tr1' @ tr2"
      by (meson in_sem)
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S" "big_step C1 s1 tr1 s2" "tr1' = tr0 @ tr1"
      using in_sem by auto
    with b0 show "\<phi> \<in> ?A"
      by (smt (verit, best) append.assoc in_sem seqB)
  qed
qed

lemma sem_skip: 
  "sem Skip S = S" (is "?A = ?B")
proof
  show "sem Skip S \<subseteq> S"
  proof 
    fix \<phi> assume "\<phi> \<in> sem Skip S"
    then obtain s1 tr0 tr1 where a0: "(s1, tr0) \<in> S" "big_step Skip s1 tr1 (fst \<phi>)" "snd \<phi> = tr0 @ tr1"
      using in_sem by auto
    then have  "tr1 = [] \<and> fst \<phi> = s1"
      using skipE by blast
    with a0 show "\<phi> \<in> S"
      by auto
  qed
  show "S \<subseteq> sem Skip S"
  proof
    fix \<phi> assume "\<phi> \<in> S"
    then show "\<phi> \<in> sem Skip S"
      using in_sem[of \<phi> Skip S] skipE skipB 
      by (metis prod.collapse self_append_conv)
  qed
qed

lemma sem_union:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" 
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S1 \<union> S2" "big_step C s1 tr1 (fst \<phi>)" "snd \<phi> = tr0 @ tr1"
      using in_sem by auto
    then show "\<phi> \<in> ?B"
      by (metis Un_iff in_sem)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<phi> assume "\<phi> \<in> ?B"
    show "\<phi> \<in> ?A"
    proof (cases "\<phi> \<in> sem C S1")
      case True
      then show ?thesis
        using in_sem by auto
    next
      case False
      then show ?thesis
        using \<open>\<phi> \<in> sem C S1 \<union> sem C S2\<close> in_sem by auto
    qed
  qed
qed

lemma sem_union_general:
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain s1 tr0 tr1 where a0: "(s1, tr0) \<in> (\<Union>x. f x)" "big_step C s1 tr1 (fst \<phi>)" "snd \<phi> = tr0 @ tr1"
      using in_sem by auto
    then obtain x where "(s1, tr0) \<in> f x" by auto
    with a0 have "\<phi> \<in> sem C (f x)"
      using in_sem by blast
    then show "\<phi> \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<phi> assume "\<phi> \<in> ?B"
    then obtain x where " \<phi> \<in> sem C (f x)" 
      by blast
    then show "\<phi> \<in> ?A"
      using in_sem by auto
  qed
qed

lemma sem_monotonic:
  assumes "S \<subseteq> S'"
  shows "sem C S \<subseteq> sem C S'"
  by (metis assms sem_union subset_Un_eq)

lemma subsetPairI:
  assumes "\<And>\<sigma> l. (\<sigma>, l) \<in> A \<Longrightarrow> (\<sigma>, l) \<in> B"
  shows "A \<subseteq> B"
  by (simp add: assms subrelI)

lemma sem_if:
  "sem (IChoice C1 C2) S = sem C1 S \<union> sem C2 S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l assume "(\<sigma>, l) \<in> ?A"
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S" "big_step (IChoice C1 C2) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>, l) \<in> ?B" using ichoiceE UnI1 UnI2 in_sem
      by (metis fst_conv snd_conv)
  qed
  show "?B \<subseteq> ?A"
    using IChoiceB1 IChoiceB2 in_sem
    by (metis (no_types, lifting) Un_subset_iff subsetI)
qed

lemma sem_assume:
  "sem (Assume b) S = {(\<sigma>, l) | \<sigma> l. (\<sigma>, l) \<in> S \<and> b \<sigma>}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l assume "(\<sigma>, l) \<in> ?A" 
    then obtain s1 tr0 tr1 where a0: "(s1, tr0) \<in> S" "big_step (Assume b) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      using in_sem by auto
    then have "s1 = \<sigma>" "tr1 = [] \<and> b \<sigma>"
      using AssumeE by blast+
    with a0 show "(\<sigma>, l) \<in> ?B"
      by simp
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix \<sigma> l assume a0: "(\<sigma>, l) \<in> ?B"
    then have "(\<sigma>, l) \<in> S" "b \<sigma>"
      by simp_all
    then show "(\<sigma>, l) \<in> ?A"
      by (metis AssumeB append.right_neutral fst_conv in_sem snd_conv)
  qed
qed


definition big_step_rel :: "proc \<Rightarrow> state \<times> trace \<Rightarrow> state \<times> trace \<Rightarrow> bool"
  where "big_step_rel C \<phi> \<phi>' = (\<exists>tr. big_step C (fst \<phi>) tr (fst \<phi>') \<and> snd \<phi>' = snd \<phi> @ tr)"

lemma while_then_reaches: 
  assumes "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  shows "(big_step_rel (Rep C)) \<phi> \<phi>'"
  using assms
proof (induct rule: converse_rtranclp_induct)
  case base
  then show ?case
    by (simp add: RepetitionB1 big_step_rel_def)
next
  case (step y z)
  then show ?case 
    using RepetitionB2 big_step_rel_def by auto
qed

lemma in_closure_then_while:
  assumes "big_step C' \<sigma> tr \<sigma>''"
  shows "\<And>C. C' = Rep C \<Longrightarrow> (big_step_rel C)\<^sup>*\<^sup>* (\<sigma>, l) (\<sigma>'', l @ tr)"
  using assms
proof(induct arbitrary: l rule: big_step.induct)
  case (RepetitionB2 C' \<sigma> tr1 \<sigma>' tr2 \<sigma>'' tr3)
  then show ?case
    by (metis append.assoc big_step_rel_def converse_rtranclp_into_rtranclp fst_conv proc.inject(7) snd_conv)
next
  case (RepetitionB1 C' \<sigma>)
  then show ?case
    by force
qed(auto)

theorem loop_equiv:
  "big_step_rel (Rep C) \<phi> \<phi>' \<longleftrightarrow> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  by (metis big_step_rel_def in_closure_then_while prod.collapse while_then_reaches)
  
fun iterate_sem where
  "iterate_sem 0 _ S = S"
| "iterate_sem (Suc n) C S = sem C (iterate_sem n C S)"

lemma in_iterate_then_in_trans:
  assumes "\<phi>' \<in> iterate_sem n C S"
  shows "\<exists>\<phi>. \<phi> \<in> S \<and> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
  using assms
proof (induct n arbitrary: \<phi>' S)
  case 0
  then show ?case
    using iterate_sem.simps(1) by blast
next
  case (Suc n)
  then show ?case
    using in_sem rtranclp.rtrancl_into_rtrancl
    by (smt (verit, del_insts) big_step_rel_def fst_conv iterate_sem.simps(2) snd_conv)    
qed

lemma reciprocal:
  assumes "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
      and "\<phi> \<in> S"
    shows "\<exists>n. \<phi>' \<in> iterate_sem n C S"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case
    using iterate_sem.simps(1) by blast
next
  case (step y z)
  then obtain n where "y \<in> iterate_sem n C S" by blast
  then show ?case
    using in_sem iterate_sem.simps(2) step.hyps(2)
    by (metis big_step_rel_def prod.collapse)
qed

lemma union_iterate_sem_trans:
  "\<phi>' \<in> (\<Union>n. iterate_sem n C S) \<longleftrightarrow> (\<exists>\<phi>. \<phi> \<in> S \<and> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>')" (is "?A \<longleftrightarrow> ?B")
  using in_iterate_then_in_trans reciprocal by (meson UNIV_I UN_E UN_I)

lemma sem_while:
  "sem (Rep C) S = (\<Union>n. iterate_sem n C S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof 
    fix \<phi>' assume "\<phi>' \<in> ?A"
    then obtain \<phi> where x_def: "\<phi> \<in> S" "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
      using in_closure_then_while in_sem
      by (metis prod.collapse)      
    then have "big_step_rel (Rep C) \<phi> \<phi>'"
      using while_then_reaches by blast
    then show "\<phi>' \<in> ?B"
      by (metis x_def union_iterate_sem_trans)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<phi>' assume "\<phi>' \<in> ?B"
    then obtain \<phi> where "\<phi> \<in> S" "(big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
      using union_iterate_sem_trans by blast
    then show "\<phi>' \<in> ?A"
      using in_sem while_then_reaches by (metis big_step_rel_def prod.collapse)
  qed
qed

lemma assume_sem:
  "sem (Assume b) S = Set.filter (b \<circ> fst) S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume asm0: "(\<sigma>, l) \<in> ?A"
    then show "(\<sigma>, l) \<in> ?B"
      using sem_assume by auto
  qed
  show "?B \<subseteq> ?A"
    using sem_assume by fastforce
qed

lemma sem_split_general:
  "sem C (\<Union>x. F x) = (\<Union>x. sem C (F x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume a0: "(\<sigma>, l) \<in> sem C (\<Union> (range F))"
    then obtain x s1 tr0 tr1 where "(s1, tr0) \<in> F x" "big_step C s1 tr1 \<sigma>" "l = tr0 @ tr1"
      using in_sem by auto     
    with a0 show "(\<sigma>, l) \<in> (\<Union>x. sem C (F x))"
      using sem_union_general by blast
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SUP_least Sup_upper sem_monotonic)
qed

lemma sem_assign:
  "sem (Assign x e) S = {(\<sigma>(x := e \<sigma>), l) | \<sigma> l. (\<sigma>, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> sem (Assign x e) S"
    then obtain s1 where "(s1, l) \<in> S" "big_step (Assign x e) s1 [] \<sigma>" "\<sigma> = s1(x := e s1)"
      by (metis append.right_neutral assignE fst_conv in_sem snd_conv) 
    then show "(\<sigma>, l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> ?B"
    then obtain \<sigma>' where "\<sigma> = \<sigma>'(x := e \<sigma>')" "(\<sigma>', l) \<in> S"
      by blast
    then show "(\<sigma>, l) \<in> ?A"
      by (metis append.right_neutral assignB fst_conv in_sem snd_conv)
  qed
qed

lemma sem_havoc:
  "sem (Havoc x) S = {(\<sigma>(x := v), l) |\<sigma> l v. (\<sigma>, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> ?A"
    then obtain s1 v where "(s1, l) \<in> S" "big_step (Havoc x) s1 [] \<sigma>" "\<sigma> = s1(x := v)"
      by (metis HavocE append.right_neutral fst_conv in_sem snd_conv)
    then show "(\<sigma>, l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> ?B"
    then obtain \<sigma>' v where "\<sigma> = \<sigma>'(x := v)" "(\<sigma>', l) \<in> S"
      by blast
    then show "(\<sigma>, l) \<in> ?A"
      using HavocB in_sem by fastforce 
  qed
qed

lemma sem_send:
  "sem (Cm (ch[!]e)) S = {(\<sigma>, l @ [OutBlock ch (e \<sigma>)]) |\<sigma> l. (\<sigma>, l) \<in> S} \<union>
  {(\<sigma>, l @ [WaitBlk d (\<lambda>_. State \<sigma>) ({ch}, {}), OutBlock ch (e \<sigma>)]) |\<sigma> l d. (d::real) > 0 \<and> (\<sigma>, l) \<in> S} \<union>
  {(\<sigma>, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>) ({ch}, {})]) |\<sigma> l. (\<sigma>, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> ?A"
    then obtain tr0 tr1 where "(\<sigma>, tr0) \<in> S" "big_step (Cm (ch[!]e)) \<sigma> tr1 \<sigma>" "l = tr0 @ tr1"
      by (metis fst_conv in_sem sendE snd_conv)
    then show "(\<sigma>, l) \<in> ?B"
      apply (rule_tac sendE[of ch e \<sigma> tr1 \<sigma>], simp_all) by auto
  qed
  show "?B \<subseteq> ?A" (is "?C \<union> ?D \<union> ?F \<subseteq> ?A")
  proof (rule Un_least)+
    show "?C \<subseteq> ?A"
      using sem_def sendB1 by fastforce
    show "?D \<subseteq> ?A"
      using sem_def sendB2 by fastforce
    show "?F \<subseteq> ?A"
      using sem_def sendB3 by fastforce
  qed
qed

lemma sem_recv:
  "sem (Cm (ch[?]var)) S = {(\<sigma>(var := v), l @ [InBlock ch v]) |\<sigma> l v. (\<sigma>, l) \<in> S} \<union>
  {(\<sigma>(var := v), l @ [WaitBlk d (\<lambda>_. State \<sigma>) ({}, {ch}), InBlock ch v]) |\<sigma> l d v. (d::real) > 0 \<and> (\<sigma>, l) \<in> S} \<union>
  {(\<sigma>, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>) ({}, {ch})]) |\<sigma> l. (\<sigma>, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l
    assume "(\<sigma>, l) \<in> ?A"
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S" "big_step (Cm (ch[?]var)) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>, l) \<in> ?B"
      apply (rule_tac receiveE[of ch var s1 tr1 \<sigma>], simp) by auto
  qed
  show "?B \<subseteq> ?A" (is "?C \<union> ?D \<union> ?F \<subseteq> ?A")
  proof (rule Un_least)+
    show "?C \<subseteq> ?A"
      using sem_def receiveB1 by fastforce
    show "?D \<subseteq> ?A"
      using sem_def receiveB2 by fastforce
    show "?F \<subseteq> ?A"
      using sem_def receiveB3 by fastforce
  qed
qed

lemma sem_ode:
  "sem (Cont ode b) S = {(\<sigma>, l) |\<sigma> l. (\<sigma>, l) \<in> S \<and> \<not> b \<sigma>} \<union> 
  {(p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma> l p d. (\<sigma>, l) \<in> S \<and> d > 0 \<and> ODEsol ode p d 
   \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and> p 0 = \<sigma>}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetPairI)
    fix \<sigma> l assume "(\<sigma>, l) \<in> ?A"
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S" "big_step (Cont ode b) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      using in_sem by auto
    then show "(\<sigma>, l) \<in> ?B"
      apply (rule_tac contE[of ode b s1 tr1 \<sigma>], simp_all) by auto
  qed
  show "?B \<subseteq> ?A" (is "?C \<union> ?D \<subseteq> ?A")
  proof(rule Un_least)
    show "?C \<subseteq> ?A"
    proof(rule subsetPairI)
      fix \<sigma> l assume "(\<sigma>, l) \<in> ?C"
      then have "(\<sigma>, l) \<in> S \<and> \<not> b \<sigma>" 
        by simp
      then show "(\<sigma>, l) \<in> ?A"
        by (metis ContB1 append.right_neutral fst_conv in_sem snd_conv)
    qed
    show "?D \<subseteq> ?A"
    proof(rule subsetPairI)
      fix \<sigma>' l' assume "(\<sigma>', l') \<in> ?D"
      then obtain \<sigma> l p d where a0: "(\<sigma>, l) \<in> S" "d > 0" "ODEsol ode p d" "\<not>b (p d)" "p 0 = \<sigma>"
      "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"  "\<sigma>' = p d" "l' = l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
        by blast
      then have "big_step (Cont ode b) \<sigma> [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
        by (rule_tac ContB2, simp_all)
      with a0 show "(\<sigma>', l') \<in> ?A"
        using in_sem by auto
    qed
  qed
qed

lemma sem_int:
  "sem (Interrupt ode b cs) S = {(s2, tr0 @ OutBlock ch (e s1) # tr1) |s1 tr0 i ch e p tr1 s2. (s1, tr0) \<in> S \<and>
   i < length cs \<and> cs ! i = (Send ch e, p) \<and> big_step p s1 tr1 s2} \<union>
   {(s2, tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) rdy # OutBlock ch (e (sl d)) # tr1)) 
    |s1 tr0 d sl i ch e p rdy tr1 s2. (s1, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = s1 \<and>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Send ch e, p) \<and> 
   rdy = rdy_of_echoice cs \<and> big_step p (sl d) tr1 s2} \<union>
   {(s2, tr0 @ InBlock ch v # tr1) |s1 tr0 i ch var v p tr1 s2. (s1, tr0) \<in> S \<and>
   i < length cs \<and> cs ! i = (Receive ch var, p) \<and> big_step p (s1(var := v)) tr1 s2} \<union>
   {(s2, tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) rdy # InBlock ch v # tr1)) 
    |s1 tr0 d sl i ch var v p rdy tr1 s2. (s1, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = s1 \<and> 
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Receive ch var, p) \<and> 
    rdy = rdy_of_echoice cs \<and> big_step p ((sl d)(var := v)) tr1 s2} \<union>
   {(\<sigma>, l) |\<sigma> l. (\<sigma>, l) \<in> S \<and> \<not> b \<sigma>} \<union>
   {(s2, tr0 @ [WaitBlk d (\<lambda> \<tau>. State (sl \<tau>)) rdy]) |s1 tr0 d sl rdy s2. (s1, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d 
   \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> \<not> b (sl d) \<and> sl 0 = s1 \<and> sl d = s2 \<and> rdy = rdy_of_echoice cs}" 
  (is "?A = ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H")
proof
  show "?A \<subseteq> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H"
  proof(rule subsetPairI)
    fix \<sigma> l assume "(\<sigma>, l) \<in> ?A"
    then obtain s1 tr0 tr1 where "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>"
    "l = tr0 @ tr1"
      using in_sem by auto
    then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H"
    proof (rule_tac interruptE[of ode b cs s1 tr1 \<sigma>], simp)
      fix i ch e p2 tr2
      assume "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" 
      "l = tr0 @ tr1" "tr1 = OutBlock ch (e s1) # tr2" 
      "i < length cs" "cs ! i = (ch[!]e, p2)" 
      "big_step p2 s1 tr2 \<sigma>"
      then have "(\<sigma>, l) \<in> ?C" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p i ch e p2 tr2
      assume "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      "tr1 = WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2" 
      "0 < d" "ODEsol ode p d" "p 0 = s1" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "i < length cs"
      "cs ! i = (ch[!]e, p2)" "big_step p2 (p d) tr2 \<sigma>"
      then have "(\<sigma>, l) \<in> ?D" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix i ch var p2 v tr2
      assume "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" "l = tr0 @ tr1" "tr1 = InBlock ch v # tr2" 
      "i < length cs" "cs ! i = (ch[?]var, p2)" "big_step p2 (s1(var := v)) tr2 \<sigma>"
      then have "(\<sigma>, l) \<in> ?E" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p i ch var p2 v tr2
      assume "(s1, tr0) \<in> S" 
      "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      "tr1 = WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2"
      "0 < d" "ODEsol ode p d" "p 0 = s1" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" 
      "i < length cs" "cs ! i = (ch[?]var, p2)" "big_step p2 ((p d)(var := v)) tr2 \<sigma>"
      then have "(\<sigma>, l) \<in> ?F" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      assume "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" "l = tr0 @ tr1"
             "tr1 = []" "\<sigma> = s1" "\<not> b s1"
      then have "(\<sigma>, l) \<in> ?G" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p
      assume "(s1, tr0) \<in> S" "big_step (Interrupt ode b cs) s1 tr1 \<sigma>" "l = tr0 @ tr1"
      "tr1 = [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)]"
      "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
      "\<not> b \<sigma>" "p 0 = s1" "p d = \<sigma>"
      then have "(\<sigma>, l) \<in> ?H" by blast
      then show "(\<sigma>, l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    qed
  qed
  show "?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H \<subseteq> ?A"
  proof(rule Un_least)+
    show "?C \<subseteq> ?A"
      using InterruptSendB1 sem_def by fastforce
    show "?D \<subseteq> ?A"
    proof(rule subsetPairI)
      fix \<sigma> l assume "(\<sigma>, l) \<in> ?D"
      then obtain s1 tr0 d sl i ch e p rdy tr1 where
      "l = tr0 @ WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # OutBlock ch (e (sl d)) # tr1"
      "(s1, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "sl 0 = s1" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "i < length cs" "cs ! i = (ch[!]e, p)" "rdy = rdy_of_echoice cs"
      "big_step p (sl d) tr1 \<sigma>"
        by blast
      then show "(\<sigma>, l) \<in> ?A"
        using InterruptSendB2[of d ode sl s1 b i cs ch e p rdy tr1 \<sigma>] sem_def
        by auto
    qed
    show "?E \<subseteq> ?A"
      using InterruptReceiveB1 sem_def by fastforce
    show "?F \<subseteq> ?A"
    proof(rule subsetPairI)
      fix \<sigma> l assume "(\<sigma>, l) \<in> ?F"
      then obtain s1 tr0 d sl i ch var v p rdy tr1 where
      "l = tr0 @ WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # InBlock ch v # tr1"
      "(s1, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "sl 0 = s1" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "i < length cs" "cs ! i = (ch[?]var, p)" "rdy = rdy_of_echoice cs"
      "big_step p ((sl d)(var := v)) tr1 \<sigma>"
        by blast
      then show "(\<sigma>, l) \<in> ?A"
        using InterruptReceiveB2[of d ode sl s1 b i cs ch var p rdy v tr1 \<sigma>] sem_def by auto
    qed
    show "?G \<subseteq> ?A"
    proof (rule subsetPairI)
      fix \<sigma> l assume "(\<sigma>, l) \<in> ?G"
      then have "(\<sigma>, l) \<in> S" "\<not> b \<sigma>" by auto
      then show "(\<sigma>, l) \<in> ?A"
        using InterruptB1[of b \<sigma> ode cs] in_sem by auto
    qed
    show "?H \<subseteq> ?A"
    proof (rule subsetPairI)
      fix \<sigma> l assume "(\<sigma>, l) \<in> ?H"
      then obtain s1 tr0 d sl rdy where "l = tr0 @ [WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy]"
      "(s1, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "\<not> b (sl d)" "sl 0 = s1" "sl d = \<sigma>" "rdy = rdy_of_echoice cs"
        by blast
      then show "(\<sigma>, l) \<in> ?A"
        using InterruptB2[of d ode sl b s1 \<sigma> rdy cs] in_sem by auto
    qed
  qed
qed

subsection \<open>Combining two traces\<close>

text \<open>Whether two rdy_infos from different processes are compatible.\<close>
fun compat_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> bool" where
  "compat_rdy (r11, r12) (r21, r22) = (r11 \<inter> r22 = {} \<and> r12 \<inter> r21 = {})"

text \<open>Merge two rdy infos\<close>
fun merge_rdy :: "rdy_info \<Rightarrow> rdy_info \<Rightarrow> rdy_info" where
  "merge_rdy (r11, r12) (r21, r22) = (r11 \<union> r21, r12 \<union> r22)"


lemma WaitBlk_eq_combine:
  assumes "WaitBlk d1 p1 rdy1 = WaitBlk d1' p1' rdy1'"
    and "WaitBlk d1 p2 rdy2 = WaitBlk d1' p2' rdy2'"
   shows "WaitBlk d1 (\<lambda>\<tau>. ParState (p1 \<tau>) (p2 \<tau>)) (merge_rdy rdy1 rdy2) =
          WaitBlk d1' (\<lambda>\<tau>. ParState (p1' \<tau>) (p2' \<tau>)) (merge_rdy rdy1' rdy2')"
proof -
  have a1: "d1 = d1'" "rdy1 = rdy1'" "rdy2 = rdy2'"
    using assms WaitBlk_cong by blast+
  have a2: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p1 t = p1' t"
    using assms(1) WaitBlk_cong2 by auto
  have a3: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> d1 \<Longrightarrow> p2 t = p2' t"
    using assms(2) WaitBlk_cong2 by auto
  show ?thesis
  proof (cases d1)
    case (real r)
    have b: "d1' = ereal r"
      using real a1(1) by auto
    show ?thesis
      unfolding real b apply (auto simp add: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: real)
      subgoal for x apply (rule a3) by (auto simp add: real)
      using a1 by auto
  next
    case PInf
    have b: "d1' = \<infinity>"
      using PInf a1 by auto
    show ?thesis
      unfolding PInf b infinity_ereal_def
      apply (auto simp: WaitBlk_simps)
       apply (rule ext) apply auto
      subgoal for x apply (rule a2) by (auto simp add: PInf)
      subgoal for x apply (rule a3) by (auto simp add: PInf)
      using a1 by auto
  next
    case MInf
    have b: "d1' = - \<infinity>"
      using MInf a1 by auto
    show ?thesis
      unfolding MInf b
      by (auto simp: a1 WaitBlk_simps)
  qed
qed


text \<open>combine_blocks comms tr1 tr2 tr means tr1 and tr2 combines to tr, where
comms is the list of internal communication channels.\<close>
inductive combine_blocks :: "cname set \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  \<comment> \<open>Empty case\<close>
  combine_blocks_empty:
  "combine_blocks comms [] [] []"

  \<comment> \<open>Paired communication\<close>
| combine_blocks_pair1:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (InBlock ch v # blks1) (OutBlock ch v # blks2) (IOBlock ch v # blks)"
| combine_blocks_pair2:
  "ch \<in> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (OutBlock ch v # blks1) (InBlock ch v # blks2) (IOBlock ch v # blks)"

  \<comment> \<open>Unpaired communication\<close>
| combine_blocks_unpair1:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms (CommBlock ch_type ch v # blks1) blks2 (CommBlock ch_type ch v # blks)"
| combine_blocks_unpair2:
  "ch \<notin> comms \<Longrightarrow>
   combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   combine_blocks comms blks1 (CommBlock ch_type ch v # blks2) (CommBlock ch_type ch v # blks)"

  \<comment> \<open>Wait\<close>
| combine_blocks_wait1:
  "combine_blocks comms blks1 blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t hist rdy # blks)"
| combine_blocks_wait2:
  "combine_blocks comms blks1 (WaitBlk (t2 - t1) (\<lambda>\<tau>. (\<lambda>x::real. hist2 x) (\<tau> + t1)) rdy2 # blks2) blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 < t2 \<Longrightarrow> t1 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t1 hist rdy # blks)"
| combine_blocks_wait3:
  "combine_blocks comms (WaitBlk (t1 - t2) (\<lambda>\<tau>. (\<lambda>x::real. hist1 x) (\<tau> + t2)) rdy1 # blks1) blks2 blks \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   t1 > t2 \<Longrightarrow> t2 > 0 \<Longrightarrow>
   hist = (\<lambda>\<tau>. ParState ((\<lambda>x::real. hist1 x) \<tau>) ((\<lambda>x::real. hist2 x) \<tau>)) \<Longrightarrow>
   rdy = merge_rdy rdy1 rdy2 \<Longrightarrow>
   combine_blocks comms (WaitBlk t1 (\<lambda>x::real. hist1 x) rdy1 # blks1)
                        (WaitBlk t2 (\<lambda>x::real. hist2 x) rdy2 # blks2)
                        (WaitBlk t2 hist rdy # blks)"

subsection \<open>Big-step semantics for parallel processes.\<close>

inductive par_big_step :: "pproc \<Rightarrow> gstate \<Rightarrow> trace \<Rightarrow> gstate \<Rightarrow> bool" where
  SingleB: "big_step p s1 tr s2 \<Longrightarrow> par_big_step (Single p) (State s1) tr (State s2)"
| ParallelB:
    "par_big_step p1 s11 tr1 s12 \<Longrightarrow>
     par_big_step p2 s21 tr2 s22 \<Longrightarrow>
     combine_blocks chs tr1 tr2 tr \<Longrightarrow>
     par_big_step (Parallel p1 chs p2) (ParState s11 s21) tr (ParState s12 s22)"

inductive_cases SingleE: "par_big_step (Single p) s1 tr s2"
inductive_cases ParallelE: "par_big_step (Parallel p1 ch p2) s1 tr s2"

subsection \<open>Extended Semantics for the single process\<close>

definition par_sem :: "pproc \<Rightarrow> gstate set \<Rightarrow> (gstate \<times> trace) set"
  where "par_sem C S = {(s', l) | s s' l.  s \<in> S \<and> par_big_step C s l s'}"

lemma in_par_sem: 
  "\<phi> \<in> par_sem C S \<longleftrightarrow> (\<exists>s l. s \<in> S \<and> par_big_step C s l (fst \<phi>) \<and> (snd \<phi>) = l)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain \<sigma>' \<sigma> l where "\<phi> = (\<sigma>', l)" "\<sigma> \<in> S"  "par_big_step C \<sigma> l \<sigma>'"
    using par_sem_def[of C S] by auto 
  then show ?B
    by auto
next
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) mem_Collect_eq prod.collapse par_sem_def)
qed

lemma par_sem_single: 
  "par_sem (Single C) S = {(State \<sigma>', l) | \<sigma> \<sigma>' l. (State \<sigma>) \<in> S \<and> big_step C \<sigma> l \<sigma>'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?A"
    then obtain s where "s \<in> S" "par_big_step (Single C) s l s'"
      using in_par_sem by auto
    then obtain \<sigma> \<sigma>' where "State \<sigma> \<in> S" "big_step C \<sigma> l \<sigma>'" "s' = State \<sigma>'"
      by (metis SingleE)
    then show "(s', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?B"
    then show "(s', l) \<in> ?A"
      using SingleB in_par_sem by auto
  qed
qed

lemma par_sem_parallel:
  "par_sem (Parallel C1 chs C2) S = {(ParState s1' s2', tr) |s1 s2 tr1 tr2 tr s1' s2'. 
  (ParState s1 s2) \<in> S \<and> par_big_step C1 s1 tr1 s1' \<and> par_big_step C2 s2 tr2 s2'
  \<and> combine_blocks chs tr1 tr2 tr}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?A"
    then obtain s where "s \<in> S" "par_big_step (Parallel C1 chs C2) s l s'"
      using in_par_sem by auto
    then obtain s1 s2 s1' s2' tr1 tr2 where "ParState s1 s2 \<in> S" "par_big_step C1 s1 tr1 s1'"
    "par_big_step C2 s2 tr2 s2'" "combine_blocks chs tr1 tr2 l" "s' = ParState s1' s2'"
      by (smt (verit, ccfv_SIG) ParallelE)
    then show "(s', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?B"
    then show "(s', l) \<in> ?A"
      using ParallelB in_par_sem by auto
  qed
qed

end
