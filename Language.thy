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

type_synonym ('lvar, 'lval) lstate = "'lvar \<Rightarrow> 'lval"

definition sem :: "proc \<Rightarrow> (('lvar, 'lval) lstate \<times> state \<times> trace) set \<Rightarrow> (('lvar, 'lval) lstate \<times> state \<times> trace) set"
  where "sem C \<Sigma> = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l @ l') | \<sigma>\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p' l l'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> big_step C \<sigma>\<^sub>p l' \<sigma>\<^sub>p'}"

lemma in_sem: 
  "\<phi> \<in> sem C \<Sigma> \<longleftrightarrow> (\<exists>\<sigma>\<^sub>p l l'. (fst \<phi>, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> big_step C \<sigma>\<^sub>p l' (fst (snd \<phi>)) 
  \<and> (snd (snd \<phi>)) = l @ l')" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p' l l' where "\<phi> = (\<sigma>\<^sub>l, \<sigma>\<^sub>p', l @ l')" "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma>"  "big_step C \<sigma>\<^sub>p l' \<sigma>\<^sub>p'"
    using sem_def[of C \<Sigma>] by auto
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
    fix \<phi> assume a0: "\<phi> \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr3 where a1: "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Seq C1 C2) \<sigma>\<^sub>p tr3 (fst (snd \<phi>))" 
    "snd (snd \<phi>) = tr0 @ tr3"
      using in_sem by blast
    then obtain tr1 \<sigma>\<^sub>p' tr2 where "big_step C1 \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "big_step C2 \<sigma>\<^sub>p' tr2 (fst (snd \<phi>))" "tr3 = tr1 @ tr2"
      by (meson seqE)
    with a0 a1 show "\<phi> \<in> ?B"
      by (smt (verit, ccfv_SIG) append.assoc fst_conv mem_Collect_eq sem_def snd_conv)          
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<phi> assume "\<phi> \<in> ?B"
    then obtain \<sigma>\<^sub>p' tr1' tr2 where b0: "(fst \<phi>, \<sigma>\<^sub>p', tr1') \<in> sem C1 S" "big_step C2 \<sigma>\<^sub>p' tr2 (fst (snd \<phi>))" 
                                        "snd (snd \<phi>) = tr1' @ tr2"
      by (meson in_sem)
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> S" "big_step C1 \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "tr1' = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
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
    then obtain \<sigma>\<^sub>p tr0 tr1 where a0: "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> S" "big_step Skip \<sigma>\<^sub>p tr1 (fst (snd \<phi>))" 
    "snd (snd \<phi>) = tr0 @ tr1"
      by (meson in_sem)     
    then have  "tr1 = [] \<and> fst (snd \<phi>) = \<sigma>\<^sub>p"
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
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(fst \<phi>,\<sigma>\<^sub>p,tr0) \<in> S1 \<union> S2" "big_step C \<sigma>\<^sub>p tr1 (fst (snd \<phi>))" 
    "snd (snd \<phi>) = tr0 @ tr1"
      by (meson in_sem)
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
        by (meson UnI1 in_sem)
    next
      case False
      then show ?thesis
        by (metis Un_iff \<open>\<phi> \<in> sem C S1 \<union> sem C S2\<close> in_sem)
    qed
  qed
qed

lemma sem_union_general:
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 where a0: "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> (\<Union>x. f x)" "big_step C \<sigma>\<^sub>p tr1 (fst (snd \<phi>))" 
    "snd (snd \<phi>) = tr0 @ tr1"
      by (metis in_sem)
    then obtain x where "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> f x" by auto
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
      by (meson UNIV_I Union_iff image_iff in_sem)
  qed
qed

lemma sem_monotonic:
  assumes "S \<subseteq> S'"
  shows "sem C S \<subseteq> sem C S'"
  by (metis assms sem_union subset_Un_eq)

lemma subsetTupleI:
  assumes "\<And>\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> A \<Longrightarrow> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> B"
  shows "A \<subseteq> B"
  by (simp add: assms subset_iff)

lemma sem_if:
  "sem (IChoice C1 C2) S = sem C1 S \<union> sem C2 S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l,\<sigma>\<^sub>p',l) \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (IChoice C1 C2) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>\<^sub>l,\<sigma>\<^sub>p',l) \<in> ?B" using ichoiceE UnI1 UnI2 in_sem
      by (metis fst_conv snd_conv)
  qed
  show "?B \<subseteq> ?A"
    using IChoiceB1 IChoiceB2 in_sem
    by (metis (no_types, lifting) Un_subset_iff subsetI)
qed

lemma sem_assume:
  "sem (Assume b) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l,\<sigma>\<^sub>p,l) \<in> S \<and> b \<sigma>\<^sub>p}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A" 
    then obtain \<sigma>\<^sub>p tr0 tr1 where a0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Assume b) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then have "\<sigma>\<^sub>p = \<sigma>\<^sub>p'" "tr1 = [] \<and> b \<sigma>\<^sub>p"
      using AssumeE by blast+
    with a0 show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      by simp     
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume a0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
    then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> S" "b \<sigma>\<^sub>p'"
      by simp_all
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
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
  assumes "(\<sigma>\<^sub>l, \<phi>') \<in> iterate_sem n C S"
  shows "\<exists>\<phi>. (\<sigma>\<^sub>l, \<phi>) \<in> S \<and> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>'"
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
      and "(\<sigma>\<^sub>l, \<phi>) \<in> S"
    shows "\<exists>n. (\<sigma>\<^sub>l, \<phi>') \<in> iterate_sem n C S"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  then show ?case
    using iterate_sem.simps(1) by blast
next
  case (step y z)
  then obtain n where "(\<sigma>\<^sub>l, y) \<in> iterate_sem n C S" by blast
  then show ?case
    using in_sem iterate_sem.simps(2) step.hyps(2)
    by (metis (no_types, lifting) big_step_rel_def split_pairs)
qed

lemma union_iterate_sem_trans:
  "(\<sigma>\<^sub>l, \<phi>') \<in> (\<Union>n. iterate_sem n C S) \<longleftrightarrow> (\<exists>\<phi>. (\<sigma>\<^sub>l, \<phi>) \<in> S \<and> (big_step_rel C)\<^sup>*\<^sup>* \<phi> \<phi>')" (is "?A \<longleftrightarrow> ?B")
  using in_iterate_then_in_trans reciprocal by (meson UNIV_I UN_E UN_I)

lemma sem_while:
  "sem (Rep C) S = (\<Union>n. iterate_sem n C S)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
    then obtain \<sigma>\<^sub>p l where x_def: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S" "(big_step_rel C)\<^sup>*\<^sup>* (\<sigma>\<^sub>p, l) (\<sigma>\<^sub>p', l')"
      using in_closure_then_while in_sem
      by (metis fst_conv prod.collapse snd_conv)   
    then have "big_step_rel (Rep C) (\<sigma>\<^sub>p, l) (\<sigma>\<^sub>p', l')"
      using while_then_reaches by blast
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
      by (metis x_def union_iterate_sem_trans)
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
    then obtain \<sigma>\<^sub>p l where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S" "(big_step_rel C)\<^sup>*\<^sup>* (\<sigma>\<^sub>p, l) (\<sigma>\<^sub>p', l')"
      using union_iterate_sem_trans by (metis prod.collapse)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
      using in_sem while_then_reaches big_step_rel_def by fastforce
  qed
qed

lemma assume_sem:
  "sem (Assume b) S = Set.filter (b \<circ> fst \<circ> snd) S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p l
    assume asm0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?A"
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?B"
      by (metis (mono_tags, lifting) AssumeE append_self_conv comp_eq_dest_lhs fst_eqD 
         in_sem member_filter snd_eqD)
  qed
  show "?B \<subseteq> ?A"
    by (smt (verit, ccfv_SIG) comp_apply fst_conv mem_Collect_eq member_filter sem_assume snd_conv subsetTupleI)
qed

lemma sem_split_general:
  "sem C (\<Union>x. F x) = (\<Union>x. sem C (F x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume a0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem C (\<Union> (range F))"
    then obtain x \<sigma>\<^sub>p tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> F x" "big_step C \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis (no_types, lifting) UN_iff fst_conv in_sem snd_conv)
    with a0 show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> (\<Union>x. sem C (F x))"
      using sem_union_general by blast
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SUP_least Sup_upper sem_monotonic)
qed

lemma sem_assign:
  "sem (Assign x e) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem (Assign x e) S"
    then obtain \<sigma>\<^sub>p where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S" "big_step (Assign x e) \<sigma>\<^sub>p [] \<sigma>\<^sub>p'" "\<sigma>\<^sub>p' = \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p)"
      by (metis (no_types, lifting) assignE fst_eqD in_sem self_append_conv snd_eqD)     
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
    then obtain \<sigma>\<^sub>p where "\<sigma>\<^sub>p' = \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p)" "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S"
      by blast
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
      by (metis append.right_neutral assignB fst_conv in_sem snd_conv)
  qed
qed

lemma sem_havoc:
  "sem (Havoc x) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := v), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain \<sigma>\<^sub>p v where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S" "big_step (Havoc x) \<sigma>\<^sub>p [] \<sigma>\<^sub>p'" "\<sigma>\<^sub>p' = \<sigma>\<^sub>p(x := v)"
      by (metis HavocE append.right_neutral fst_conv in_sem snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
    then obtain \<sigma>\<^sub>p v where "\<sigma>\<^sub>p' = \<sigma>\<^sub>p(x := v)" "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S"
      by blast
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
      using HavocB in_sem by fastforce 
  qed
qed

lemma sem_send:
  "sem (Cm (ch[!]e)) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {}), OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0) \<in> S" "big_step (Cm (ch[!]e)) \<sigma>\<^sub>p' tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis fst_conv in_sem sendE snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      apply (rule_tac sendE[of ch e \<sigma>\<^sub>p' tr1 \<sigma>\<^sub>p'], simp_all) by auto
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
  "sem (Cm (ch[?]var)) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch}), InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d v. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Cm (ch[?]var)) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      apply (rule_tac receiveE[of ch var \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'], simp_all) by auto
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
  "sem (Cont ode b) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> b \<sigma>\<^sub>p} \<union> 
  {(\<sigma>\<^sub>l, p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l p d. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> d > 0 \<and> ODEsol ode p d 
   \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and> p 0 = \<sigma>\<^sub>p}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Cont ode b) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      apply (rule_tac contE[of ode b \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'], simp_all) by auto
  qed
  show "?B \<subseteq> ?A" (is "?C \<union> ?D \<subseteq> ?A")
  proof(rule Un_least)
    show "?C \<subseteq> ?A"
    proof(rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> S \<and> \<not> b \<sigma>\<^sub>p'" 
        by simp
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        by (metis ContB1 append.right_neutral fst_conv in_sem snd_conv)
    qed
    show "?D \<subseteq> ?A"
    proof(rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?D"
      then obtain \<sigma>\<^sub>p l p d where a0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S" "d > 0" "ODEsol ode p d" "\<not>b (p d)" "p 0 = \<sigma>\<^sub>p"
      "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"  "\<sigma>\<^sub>p' = p d" "l' = l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
        by blast
      then have "big_step (Cont ode b) \<sigma>\<^sub>p [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] (p d)"
        by (rule_tac ContB2, simp_all)
      with a0 show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
        by (metis fst_conv in_sem snd_conv)
    qed
  qed
qed

lemma sem_int:
  "sem (Interrupt ode b cs) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ OutBlock ch (e \<sigma>\<^sub>p) # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 i ch e p tr1 \<sigma>\<^sub>p'. 
  (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> i < length cs \<and> cs ! i = (Send ch e, p) \<and> big_step p \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) rdy # OutBlock ch (e (sl d)) # tr1)) 
    |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl i ch e p rdy tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Send ch e, p) \<and> 
   rdy = rdy_of_echoice cs \<and> big_step p (sl d) tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>P', tr0 @ InBlock ch v # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 i ch var v p tr1 \<sigma>\<^sub>P'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and>
   i < length cs \<and> cs ! i = (Receive ch var, p) \<and> big_step p (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>P'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) rdy # InBlock ch v # tr1)) 
    |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl i ch var v p rdy tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> 
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Receive ch var, p) \<and> 
    rdy = rdy_of_echoice cs \<and> big_step p ((sl d)(var := v)) tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> b \<sigma>\<^sub>p} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda> \<tau>. State (sl \<tau>)) rdy]) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl rdy \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> 
   d > 0 \<and> ODEsol ode sl d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> \<not> b (sl d) \<and> sl 0 = \<sigma>\<^sub>p \<and> sl d = \<sigma>\<^sub>p' 
   \<and> rdy = rdy_of_echoice cs}" 
  (is "?A = ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H")
proof
  show "?A \<subseteq> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'"
    "l = tr0 @ tr1"
      by (metis fst_conv in_sem snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H"
    proof (rule_tac interruptE[of ode b cs \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'], simp)
      fix i ch e p2 tr2
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" 
      "l = tr0 @ tr1" "tr1 = OutBlock ch (e \<sigma>\<^sub>p) # tr2" 
      "i < length cs" "cs ! i = (ch[!]e, p2)" 
      "big_step p2 \<sigma>\<^sub>p tr2 \<sigma>\<^sub>p'"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p i ch e p2 tr2
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      "tr1 = WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2" 
      "0 < d" "ODEsol ode p d" "p 0 = \<sigma>\<^sub>p" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" "i < length cs"
      "cs ! i = (ch[!]e, p2)" "big_step p2 (p d) tr2 \<sigma>\<^sub>p'"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?D" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix i ch var p2 v tr2
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1" "tr1 = InBlock ch v # tr2" 
      "i < length cs" "cs ! i = (ch[?]var, p2)" "big_step p2 (\<sigma>\<^sub>p(var := v)) tr2 \<sigma>\<^sub>p'"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?E" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p i ch var p2 v tr2
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" 
      "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      "tr1 = WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2"
      "0 < d" "ODEsol ode p d" "p 0 = \<sigma>\<^sub>p" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)" 
      "i < length cs" "cs ! i = (ch[?]var, p2)" "big_step p2 ((p d)(var := v)) tr2 \<sigma>\<^sub>p'"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?F" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
             "tr1 = []" "\<sigma>\<^sub>p' = \<sigma>\<^sub>p" "\<not> b \<sigma>\<^sub>p"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?G" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    next
      fix d p
      assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "big_step (Interrupt ode b cs) \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      "tr1 = [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)]"
      "0 < d" "ODEsol ode p d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)"
      "\<not> b \<sigma>\<^sub>p'" "p 0 = \<sigma>\<^sub>p" "p d = \<sigma>\<^sub>p'"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?H" by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H" by blast
    qed
  qed
  show "?C \<union> ?D \<union> ?E \<union> ?F \<union> ?G \<union> ?H \<subseteq> ?A"
  proof(rule Un_least)+
    show "?C \<subseteq> ?A"
      using InterruptSendB1 sem_def by fastforce
    show "?D \<subseteq> ?A"
    proof(rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?D"
      then obtain \<sigma>\<^sub>p tr0 d sl i ch e p rdy tr1 where
      "l = tr0 @ WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # OutBlock ch (e (sl d)) # tr1"
      "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "i < length cs" "cs ! i = (ch[!]e, p)" "rdy = rdy_of_echoice cs"
      "big_step p (sl d) tr1 \<sigma>\<^sub>p'"
        by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        using InterruptSendB2[of d ode sl \<sigma>\<^sub>p b i cs ch e p rdy tr1 \<sigma>\<^sub>p'] sem_def
        by fastforce
    qed
    show "?E \<subseteq> ?A"
      using InterruptReceiveB1 sem_def by fastforce
    show "?F \<subseteq> ?A"
    proof(rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?F"
      then obtain \<sigma>\<^sub>p tr0 d sl i ch var v p rdy tr1 where
      "l = tr0 @ WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # InBlock ch v # tr1"
      "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "i < length cs" "cs ! i = (ch[?]var, p)" "rdy = rdy_of_echoice cs"
      "big_step p ((sl d)(var := v)) tr1 \<sigma>\<^sub>p'"
        by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        using InterruptReceiveB2[of d ode sl \<sigma>\<^sub>p b i cs ch var p rdy v tr1 \<sigma>\<^sub>p'] sem_def by fastforce
    qed
    show "?G \<subseteq> ?A"
    proof (rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?G"
      then have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> S" "\<not> b \<sigma>\<^sub>p'" by auto
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        using InterruptB1[of b \<sigma>\<^sub>p' ode cs] in_sem by fastforce
    qed
    show "?H \<subseteq> ?A"
    proof (rule subsetTupleI)
      fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?H"
      then obtain \<sigma>\<^sub>p tr0 d sl rdy where "l = tr0 @ [WaitBlk (ereal d) (\<lambda>\<tau>. State (sl \<tau>)) rdy]"
      "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "\<not> b (sl d)" "sl 0 = \<sigma>\<^sub>p" "sl d = \<sigma>\<^sub>p'" "rdy = rdy_of_echoice cs"
        by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        using InterruptB2[of d ode sl b \<sigma>\<^sub>p \<sigma>\<^sub>p' rdy cs] in_sem by fastforce
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

datatype ('lvar, 'lval) exgstate =
  ExState "('lvar, 'lval) lstate \<times> state"
  | ExParState "('lvar, 'lval) exgstate" "('lvar, 'lval) exgstate"

primrec ex2gstate :: "('lvar, 'lval) exgstate \<Rightarrow> gstate"
  where "ex2gstate (ExState s) = State (snd s)"
  | "ex2gstate (ExParState s1 s2) = ParState (ex2gstate s1) (ex2gstate s2)"

definition par_sem :: "pproc \<Rightarrow> (('lvar, 'lval) lstate \<times> gstate) set \<Rightarrow> (('lvar, 'lval) lstate \<times> gstate \<times> trace) set"
  where "par_sem C S = {(s\<^sub>l, s\<^sub>p', l) |s\<^sub>l s\<^sub>p s\<^sub>p' l. (s\<^sub>l, s\<^sub>p) \<in> S \<and> par_big_step C s\<^sub>p l s\<^sub>p'}"

lemma in_par_sem: 
  "\<phi> \<in> par_sem C S \<longleftrightarrow> (\<exists>s\<^sub>p l. (fst \<phi>, s\<^sub>p) \<in> S \<and> par_big_step C s\<^sub>p l (fst (snd \<phi>)) 
  \<and> (snd (snd \<phi>)) = l)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain s\<^sub>p l where "(fst \<phi>, s\<^sub>p) \<in> S" "par_big_step C s\<^sub>p l (fst (snd \<phi>))"
    using par_sem_def[of C S] by auto 
  then show ?B
    by (smt (verit, best) \<open>\<phi> \<in> par_sem C S\<close> fstI mem_Collect_eq par_sem_def sndI)
next
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) mem_Collect_eq prod.collapse par_sem_def)
qed

lemma par_sem_single: 
  "par_sem (Single C) S = {(s\<^sub>l, State \<sigma>\<^sub>p', l) |s\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p' l. (s\<^sub>l, State \<sigma>\<^sub>p) \<in> S \<and> big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix s\<^sub>l s\<^sub>p' l assume "(s\<^sub>l, s\<^sub>p', l) \<in> ?A"
    then obtain s\<^sub>p where "(s\<^sub>l, s\<^sub>p) \<in> S" "par_big_step (Single C) s\<^sub>p l s\<^sub>p'"
      by (metis fst_conv in_par_sem snd_conv)
    then obtain \<sigma>\<^sub>p \<sigma>\<^sub>p' where "(s\<^sub>l, State \<sigma>\<^sub>p) \<in> S" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'" "s\<^sub>p' = State \<sigma>\<^sub>p'"
      by (metis SingleE)
    then show "(s\<^sub>l, s\<^sub>p', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix s\<^sub>l s\<^sub>p' l assume "(s\<^sub>l, s\<^sub>p', l) \<in> ?B"
    then show "(s\<^sub>l, s\<^sub>p', l) \<in> ?A"
      using SingleB in_par_sem by fastforce
  qed
qed

lemma par_sem_parallel:
  "par_sem (Parallel C1 chs C2) S = {(s\<^sub>l, ParState \<sigma>\<^sub>p\<^sub>1' \<sigma>\<^sub>p\<^sub>2', tr) |s\<^sub>l \<sigma>\<^sub>p\<^sub>1 \<sigma>\<^sub>p\<^sub>2 tr1 tr2 tr \<sigma>\<^sub>p\<^sub>1' \<sigma>\<^sub>p\<^sub>2'. 
  (s\<^sub>l, ParState \<sigma>\<^sub>p\<^sub>1 \<sigma>\<^sub>p\<^sub>2) \<in> S \<and> par_big_step C1 \<sigma>\<^sub>p\<^sub>1 tr1 \<sigma>\<^sub>p\<^sub>1' \<and> par_big_step C2 \<sigma>\<^sub>p\<^sub>2 tr2 \<sigma>\<^sub>p\<^sub>2'
  \<and> combine_blocks chs tr1 tr2 tr}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix s\<^sub>l s\<^sub>p' l assume "(s\<^sub>l, s\<^sub>p', l) \<in> ?A"
    then obtain s\<^sub>p where "(s\<^sub>l, s\<^sub>p) \<in> S" "par_big_step (Parallel C1 chs C2) s\<^sub>p l s\<^sub>p'"
      by (metis fst_conv in_par_sem snd_conv)
    then obtain \<sigma>\<^sub>p\<^sub>1 \<sigma>\<^sub>p\<^sub>2 tr1 tr2 \<sigma>\<^sub>p\<^sub>1' \<sigma>\<^sub>p\<^sub>2' where "(s\<^sub>l, ParState \<sigma>\<^sub>p\<^sub>1 \<sigma>\<^sub>p\<^sub>2) \<in> S" "par_big_step C1 \<sigma>\<^sub>p\<^sub>1 tr1 \<sigma>\<^sub>p\<^sub>1'"
    "par_big_step C2 \<sigma>\<^sub>p\<^sub>2 tr2 \<sigma>\<^sub>p\<^sub>2'" "combine_blocks chs tr1 tr2 l" "s\<^sub>p' = ParState \<sigma>\<^sub>p\<^sub>1' \<sigma>\<^sub>p\<^sub>2'"
      by (smt (verit, ccfv_SIG) ParallelE)
    then show "(s\<^sub>l, s\<^sub>p', l) \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix s\<^sub>l s\<^sub>p' l assume "(s\<^sub>l, s\<^sub>p', l) \<in> ?B"
    then show "(s\<^sub>l, s\<^sub>p', l) \<in> ?A"
      using ParallelB in_par_sem by fastforce
  qed
qed

end
