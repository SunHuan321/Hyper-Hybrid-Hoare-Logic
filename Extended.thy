theory Extended
  imports Language
begin

subsection \<open>Extended Semantics for the single process\<close>

type_synonym ('lvar, 'lval) lstate = "'lvar \<Rightarrow> 'lval"
type_synonym ('lvar, 'lval) exstate = "('lvar, 'lval) lstate \<times> state \<times> trace"

definition lproj :: "('lvar, 'lval) exstate \<Rightarrow> ('lvar, 'lval) lstate" where
  "lproj \<sigma> = fst \<sigma>"

definition pproj :: "('lvar, 'lval) exstate \<Rightarrow> state" where
  "pproj \<sigma> = fst (snd \<sigma>)"

definition tproj :: "('lvar, 'lval) exstate \<Rightarrow> trace" where
  "tproj \<sigma> = snd (snd \<sigma>)"

definition ex2s :: "('lvar, 'lval) exstate \<Rightarrow> state \<times> trace" where
  "ex2s ex = snd ex"

definition sem :: "proc \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> (('lvar, 'lval) exstate) set"
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
    using append.assoc big_step_rel_def converse_rtranclp_into_rtranclp fst_conv
    by (metis proc.inject(8) snd_conv)    
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

lemma sem_wait:
  "sem (Wait d) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> 0 < d \<sigma>\<^sub>p} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk (d \<sigma>\<^sub>p) (\<lambda>_. State \<sigma>\<^sub>p) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. 0 < d \<sigma>\<^sub>p \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
    then obtain tr0 tr1 where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0) \<in> S" "big_step (Wait d) \<sigma>\<^sub>p' tr1 \<sigma>\<^sub>p'" "l = tr0 @ tr1"
      by (metis (no_types, lifting) fst_eqD in_sem snd_eqD waitE)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?B"
      by (rule_tac waitE[of d \<sigma>\<^sub>p' tr1 \<sigma>\<^sub>p'], simp_all)
  qed
  show "?B \<subseteq> ?A" (is "?C \<union> ?D  \<subseteq> ?A")
  proof (rule Un_least)+
    show "?C \<subseteq> ?A"
      using sem_def waitB2
      by (smt (verit, ccfv_SIG) append.right_neutral mem_Collect_eq subsetI)
    show "?D \<subseteq> ?A"
      using sem_def waitB1
      by (smt (verit, best) mem_Collect_eq subsetI)
  qed
qed

lemma sem_send:
  "sem (Cm (ch[!]e)) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {}), OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" 
  (is "?A = ?B")
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
  show "?B \<subseteq> ?A" (is "?C \<union> ?D  \<subseteq> ?A")
  proof (rule Un_least)+
    show "?C \<subseteq> ?A"
      using sem_def sendB1 by fastforce
    show "?D \<subseteq> ?A"     
      using sem_def sendB2 by fastforce
  qed
qed

lemma sem_recv:
  "sem (Cm (ch[?]var)) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch}), InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d v. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}" (is "?A = ?B")
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
  show "?B \<subseteq> ?A" (is "?C \<union> ?D  \<subseteq> ?A")
  proof (rule Un_least)+
    show "?C \<subseteq> ?A"
      using sem_def receiveB1 by fastforce
    show "?D \<subseteq> ?A"
      using sem_def receiveB2 by fastforce
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

lemma sem_interrupt_send1:
  "sem C {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma>} = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ OutBlock ch (e \<sigma>\<^sub>p) # tr1) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> big_step C \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 l where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'" "l' = tr0 @ [OutBlock ch (e \<sigma>\<^sub>p)] @ l"
      by (smt (verit) append.assoc fst_conv in_sem mem_Collect_eq snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
      by auto
  qed
next
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
    then obtain \<sigma>\<^sub>p tr0 l where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'" "l' = tr0 @ [OutBlock ch (e \<sigma>\<^sub>p)] @ l"
      by auto
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
      using in_sem by fastforce
  qed
qed

lemma sem_interrupt_send2:
  "sem C {(\<sigma>\<^sub>l, sl d, l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d sl.
  (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> 0 < d \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))} = 
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))] @ tr1) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and>
  (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> big_step C (sl d) tr1 \<sigma>\<^sub>p'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 l d sl where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p"
    "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)" "big_step C (sl d) l \<sigma>\<^sub>p'" 
    "l' = tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))] @ l"
      by (smt (verit) append.assoc fst_conv in_sem mem_Collect_eq snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
      by auto
  qed
next
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
    then obtain \<sigma>\<^sub>p tr0 d sl l where a: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p" 
    "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)" "big_step C (sl d) l \<sigma>\<^sub>p'" 
    "l' = (tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))]) @ l"
      by auto
    then have "(\<sigma>\<^sub>l, sl d, tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))])
    \<in> {(\<sigma>\<^sub>l, sl d, l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d sl.
       (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> 0 < d \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))}"
      by auto
    with a show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
      by (smt (verit, best) mem_Collect_eq sem_def)      
  qed
qed

lemma sem_interrupt_send:
  "sem C ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> V} \<union>
  {(\<sigma>\<^sub>l, sl d, l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), OutBlock ch (e (sl d))]) |\<sigma>\<^sub>l l d sl.
  (\<sigma>\<^sub>l, sl 0, l) \<in> V \<and> 0 < d \<and> ODEsol ode sl d \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))}) =
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ OutBlock ch (e \<sigma>\<^sub>p) # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> V \<and> big_step C \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (sl d)) # tr1) |\<sigma>\<^sub>l tr0 d sl tr1 \<sigma>\<^sub>p'.
   (\<sigma>\<^sub>l, sl 0, tr0) \<in> V \<and> 0 < d \<and> ODEsol ode sl d \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)) \<and> big_step C (sl d) tr1 \<sigma>\<^sub>p'}"
  (is "sem C (?A \<union> ?B) = ?C \<union> ?D")
proof-
  have a1: "sem C ?A = ?C"
    by (simp add: sem_interrupt_send1)
  have a2: "sem C ?B = ?D"
    using sem_interrupt_send2[of C cs ch e V ode b]
    by auto
  with a1 show ?thesis
    by (simp add: sem_union)
qed

lemma sem_interrupt_recv1:
  "sem C {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma>} = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ InBlock ch v # tr1) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p' v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> big_step C (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>p'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 tr1 v where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "big_step C (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>p'" 
    "l' = tr0 @ [InBlock ch v] @ tr1"
      by (smt (verit) Cons_eq_appendI Pair_inject append.assoc mem_Collect_eq self_append_conv2 sem_def)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
      by auto
  qed
next
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
    then obtain \<sigma>\<^sub>p tr0 tr1 v where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "big_step C (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>p'" 
    "l' = (tr0 @ [InBlock ch v]) @ tr1"
      by auto
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
      using in_sem 
      by (smt (verit, ccfv_threshold) CollectI fst_conv snd_conv)
  qed
qed

lemma sem_interrupt_recv2:
  "sem C {(\<sigma>\<^sub>l, (sl d)(var := v), l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v]) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p l d sl v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> 0 < d \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))} = 
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v] @ tr1) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p' d sl v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and>
  (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> big_step C ((sl d)(var := v)) tr1 \<sigma>\<^sub>p'}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
    then obtain \<sigma>\<^sub>p tr0 l d sl v where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p"
    "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)" "big_step C ((sl d)(var := v)) l \<sigma>\<^sub>p'" 
    "l' = tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v] @ l"
      by (smt (verit) append.assoc fst_conv in_sem mem_Collect_eq snd_conv)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
      by blast
  qed
next
  show "?B \<subseteq> ?A"
  proof(rule subsetTupleI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p' l' 
    assume "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?B"
   then obtain \<sigma>\<^sub>p tr0 l d sl v where a: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma>" "0 < d" "ODEsol ode sl d" "sl 0 = \<sigma>\<^sub>p"
    "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)" "big_step C ((sl d)(var := v)) l \<sigma>\<^sub>p'" 
    "l' = (tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v]) @ l"
      by auto
    then have "(\<sigma>\<^sub>l, (sl d)(var := v), tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs),InBlock ch v])
    \<in> {(\<sigma>\<^sub>l, (sl d)(var := v), l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v]) 
      |\<sigma>\<^sub>l \<sigma>\<^sub>p l d sl v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> 0 < d \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))}"
      by auto
    with a show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l') \<in> ?A"
      by (smt (verit, best) mem_Collect_eq sem_def)      
  qed
qed

lemma sem_interrupt_recv:
  "sem C ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> V} \<union>
  {(\<sigma>\<^sub>l, (sl d)(var := v), l @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v]) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p l d sl v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> V \<and> 0 < d \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t))}) =
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ InBlock ch v # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p' v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> V \<and> big_step C (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>p'} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs), InBlock ch v] @ tr1) 
  |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 tr1 \<sigma>\<^sub>p' d sl v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> V \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and>
  (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> big_step C ((sl d)(var := v)) tr1 \<sigma>\<^sub>p'}"
  (is "sem C (?A \<union> ?B) = ?C \<union> ?D")
proof-
  have a1: "sem C ?A = ?C"
    using sem_interrupt_recv1[of C var ch V] by auto
  have a2: "sem C ?B = ?D"
    using sem_interrupt_recv2[of C var cs ch V ode b] by auto
  with a1 show ?thesis
    by (simp add: sem_union)
qed

lemma sem_int:
  "sem (Interrupt ode b cs) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ OutBlock ch (e \<sigma>\<^sub>p) # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 i ch e p tr1 \<sigma>\<^sub>p'. 
  (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> i < length cs \<and> cs ! i = (Send ch e, p) \<and> big_step p \<sigma>\<^sub>p tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (sl d)) # tr1)) 
    |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl i ch e p tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and>
   (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Send ch e, p) \<and> 
    big_step p (sl d) tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ InBlock ch v # tr1) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 i ch var v p tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and>
   i < length cs \<and> cs ! i = (Receive ch var, p) \<and> big_step p (\<sigma>\<^sub>p(var := v)) tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ (WaitBlk d (\<lambda>\<tau>. State (sl \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr1)) 
    |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl i ch var v p tr1 \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> d > 0 \<and> ODEsol ode sl d \<and> sl 0 = \<sigma>\<^sub>p \<and> 
    (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> i < length cs \<and> cs ! i = (Receive ch var, p) \<and> 
    big_step p ((sl d)(var := v)) tr1 \<sigma>\<^sub>p'} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> b \<sigma>\<^sub>p} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda> \<tau>. State (sl \<tau>)) (rdy_of_echoice cs)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl \<sigma>\<^sub>p'. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S \<and> 
   d > 0 \<and> ODEsol ode sl d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> \<not> b (sl d) \<and> sl 0 = \<sigma>\<^sub>p \<and> sl d = \<sigma>\<^sub>p'}" 
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
      "tr1 = WaitBlk ( d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # OutBlock ch (e (p d)) # tr2" 
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
      "tr1 = WaitBlk ( d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs) # InBlock ch v # tr2"
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
      "tr1 = [WaitBlk ( d) (\<lambda>\<tau>. State (p \<tau>)) (rdy_of_echoice cs)]"
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
      "l = tr0 @ WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # OutBlock ch (e (sl d)) # tr1"
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
      "l = tr0 @ WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) rdy # InBlock ch v # tr1"
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
      then obtain \<sigma>\<^sub>p tr0 d sl rdy where "l = tr0 @ [WaitBlk ( d) (\<lambda>\<tau>. State (sl \<tau>)) rdy]"
      "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> S" "0 < d" "ODEsol ode sl d" "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
      "\<not> b (sl d)" "sl 0 = \<sigma>\<^sub>p" "sl d = \<sigma>\<^sub>p'" "rdy = rdy_of_echoice cs"
        by blast
      then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> ?A"
        using InterruptB2[of d ode sl b \<sigma>\<^sub>p \<sigma>\<^sub>p' rdy cs] in_sem by fastforce
    qed
  qed
qed

lemma sem_int_Nil:
  "sem (Interrupt ode b []) \<Sigma> = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> \<not> b \<sigma>\<^sub>p} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda> \<tau>. State (sl \<tau>)) (rdy_of_echoice [])]) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl \<sigma>\<^sub>p'.
   (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> d > 0 \<and> ODEsol ode sl d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> \<not> b (sl d) \<and> 
   sl 0 = \<sigma>\<^sub>p \<and> sl d = \<sigma>\<^sub>p'}"
  using sem_int[of ode b Nil \<Sigma>] by auto

lemma sem_int_Nil1:
  assumes "cs = []"
  shows "sem (Interrupt ode b cs) \<Sigma> = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> \<Sigma> \<and> \<not> b \<sigma>\<^sub>p} \<union>
   {(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ [WaitBlk d (\<lambda> \<tau>. State (sl \<tau>)) (rdy_of_echoice cs)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p tr0 d sl \<sigma>\<^sub>p'.
   (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> \<Sigma> \<and> d > 0 \<and> ODEsol ode sl d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (sl t)) \<and> \<not> b (sl d) \<and> 
   sl 0 = \<sigma>\<^sub>p \<and> sl d = \<sigma>\<^sub>p'}"
  by (simp add: assms sem_int_Nil)


(*
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
    have b: "d1' =  r"
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
      unfolding PInf b infinity__def
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
*)

subsection \<open>Extended Semantics for the single process\<close>

datatype ('lvar, 'lval) exgstate =
  ExState "('lvar, 'lval) lstate \<times> state"
  | ExParState "('lvar, 'lval) exgstate" "('lvar, 'lval) exgstate"

primrec ex2gstate :: "('lvar, 'lval) exgstate \<Rightarrow> gstate"
  where "ex2gstate (ExState s) = State (snd s)"
  | "ex2gstate (ExParState s1 s2) = ParState (ex2gstate s1) (ex2gstate s2)"

fun ex_logical_same :: "('lvar, 'lval) exgstate \<Rightarrow> ('lvar, 'lval) exgstate \<Rightarrow> bool"
  where "ex_logical_same (ExState s1) (ExState s1') = (fst s1 = fst s1')"
  | "ex_logical_same (ExParState s1 s2) (ExParState s1' s2') = (ex_logical_same s1 s1' \<and> ex_logical_same s2 s2')"
  | "ex_logical_same _ _ = False"

lemma ex_logical_same_refl: 
  "ex_logical_same s s"
proof(induct s)
  case (ExState x)
  then show ?case
    by simp
next
  case (ExParState s1 s2)
  then show ?case 
    by simp
qed

lemma ex_logical_same_comm:
  assumes "ex_logical_same s0 s1"
  shows "ex_logical_same s1 s0"
  using assms
proof(induct s0 arbitrary: s1)
  case (ExState x)
  then show ?case
  proof-
    obtain y where "s1 = ExState y" "fst x = fst y"
      using ExState ex_logical_same.elims(2) by blast
    then show ?case
      by simp
  qed
next
  case (ExParState s01 s02)
  then show ?case
  proof-
    obtain s01' s02' where "s1 = ExParState s01' s02'" "ex_logical_same s01 s01'" "ex_logical_same s02 s02'"
      by (metis ExParState.prems ex_logical_same.elims(2) ex_logical_same.simps(2) ex_logical_same.simps(3))
    then have "ex_logical_same s01' s01" "ex_logical_same s02' s02"
      using ExParState.hyps by blast+
    then show ?thesis
      by (simp add: \<open>s1 = ExParState s01' s02'\<close>)
  qed
qed


lemma ex_logical_same_trans: 
  assumes "ex_logical_same s0 s1"
      and "ex_logical_same s1 s2"
    shows "ex_logical_same s0 s2"
  using assms
proof(induct s0 arbitrary: s1 s2)
  case (ExState x)
  then show ?case
  proof-
    obtain y where "s1 = ExState y" "fst x = fst y"
      using ExState ex_logical_same.elims(2) by blast
    then obtain z where "s2 = ExState z" "fst y = fst z"
      using ExState.prems(2) ex_logical_same.elims(2) by blast
    then show ?thesis
      by (simp add: \<open>fst x = fst y\<close>)
  qed
next
  case (ExParState s01 s02)
  then show ?case
  proof-
    obtain s01' s02' where a0: "s1 = ExParState s01' s02'" "ex_logical_same s01 s01'" "ex_logical_same s02 s02'"
      by (metis ExParState.prems(1) ex_logical_same.simps(2) ex_logical_same.simps(4) ex_logical_same_comm exgstate.exhaust)
    with ExParState.prems(2) obtain s01'' s02'' where a1: "s2 = ExParState s01'' s02''" "ex_logical_same s01' s01''" "ex_logical_same s02' s02''"
      by (metis ex_logical_same.simps(2) ex_logical_same.simps(3) exgstate.exhaust)
    with a0(2) a0(3) ExParState.hyps have "ex_logical_same s01 s01''" "ex_logical_same s02 s02''"
      by auto
    with a1(1) show ?thesis
      by simp
  qed
qed

lemma ex_sem_single: 
  assumes "par_big_step (Single C) (ex2gstate s) l (ex2gstate s')"
  shows "\<exists>\<sigma>\<^sub>l \<sigma>\<^sub>l' \<sigma>\<^sub>p \<sigma>\<^sub>p'. s = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<and> s' = ExState (\<sigma>\<^sub>l', \<sigma>\<^sub>p')"
proof-
  obtain \<sigma>\<^sub>p \<sigma>\<^sub>p' where "ex2gstate s = State \<sigma>\<^sub>p" "ex2gstate s' = State \<sigma>\<^sub>p'"
    by (meson SingleE assms)
  then obtain \<sigma>\<^sub>l \<sigma>\<^sub>l' where "s = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p)" "s' = ExState (\<sigma>\<^sub>l', \<sigma>\<^sub>p')"
    by (metis eq_fst_iff ex2gstate.simps(1) ex2gstate.simps(2) exgstate.exhaust gstate.distinct(1) gstate.inject(1) sndI)
  then show ?thesis by auto
qed

lemma ex_sem_single_logical:
  assumes "par_big_step (Single C) (ex2gstate s) l (ex2gstate s')" "ex_logical_same s s'"
  shows "\<exists>\<sigma>\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p'. s = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<and> s' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')"
  using assms(1) assms(2) ex_sem_single by fastforce

lemma ex_sem_par:
  assumes "par_big_step (Parallel C1 chs C2) (ex2gstate s) l (ex2gstate s')"
  shows "\<exists>s1 s2 s1' s2'. s = ExParState s1 s2 \<and> s' = ExParState s1' s2'"
proof-
  obtain \<sigma>1 \<sigma>2 \<sigma>1' \<sigma>2' where "ex2gstate s = ParState \<sigma>1 \<sigma>2" "ex2gstate s' = ParState \<sigma>1' \<sigma>2'"
    by (smt (verit, best) ParallelE assms)
  then show ?thesis
    by (metis ex2gstate.simps(1) exgstate.exhaust gstate.distinct(1))
qed

lemma ex_sem_par_logical:
  assumes "par_big_step (Parallel C1 chs C2) (ex2gstate s) l (ex2gstate s')" "ex_logical_same s s'"
  shows "\<exists>s1 s2 s1' s2'. s = ExParState s1 s2 \<and> s' = ExParState s1' s2' \<and> ex_logical_same s1 s1' \<and> ex_logical_same s2 s2'"
  using assms(1) assms(2) ex_sem_par by fastforce

definition par_sem :: "pproc \<Rightarrow> (('lvar, 'lval) exgstate set) \<Rightarrow> (('lvar, 'lval) exgstate \<times> trace) set"
  where "par_sem C S = {(s', l) |s s' l. s \<in> S \<and> par_big_step C (ex2gstate s) l (ex2gstate s') \<and> ex_logical_same s s'}"

lemma in_par_sem: 
  "\<phi> \<in> par_sem C S \<longleftrightarrow> (\<exists>s. s \<in> S \<and> par_big_step C (ex2gstate s) (snd \<phi>) (ex2gstate (fst \<phi>)) 
  \<and> ex_logical_same s (fst \<phi>))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain s s' l where "s \<in> S" "par_big_step C (ex2gstate s) l (ex2gstate s')" "ex_logical_same s s'"
    using par_sem_def[of C S] by auto 
  then show ?B
    by (smt (verit, best) \<open>\<phi> \<in> par_sem C S\<close> fstI mem_Collect_eq par_sem_def sndI)
next
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) mem_Collect_eq prod.collapse par_sem_def)
qed

lemma subsetPairI:
  assumes "\<And>l \<sigma>. (l, \<sigma>) \<in> A \<Longrightarrow> (l, \<sigma>) \<in> B"
  shows "A \<subseteq> B"
  by (simp add: assms subrelI)

lemma par_sem_monotonic:
  assumes "S \<subseteq> S'"
  shows "par_sem C S \<subseteq> par_sem C S'"
  by (meson assms in_mono in_par_sem subsetI)

lemma par_sem_single: 
  assumes "S = {ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p) |\<sigma>\<^sub>l \<sigma>\<^sub>p. (\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<in> S'}"
      and "S'' =  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, []) |\<sigma>\<^sub>l \<sigma>\<^sub>p. (\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<in> S'}"
  shows "par_sem (Single C) S = {(ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p'), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem C S''}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?A"
    then obtain s where "s \<in> S" "par_big_step (Single C) (ex2gstate s) l (ex2gstate s')" "ex_logical_same s s'"
      by (metis fst_conv in_par_sem snd_conv)
    with assms(1) obtain \<sigma>\<^sub>p \<sigma>\<^sub>l \<sigma>\<^sub>p' where a0: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<in> S'" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'" "s' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')"
      by (smt (verit, ccfv_threshold) SingleE ex2gstate.simps(1) ex_sem_single_logical 
          exgstate.inject(1) gstate.inject(1) mem_Collect_eq snd_conv)
    with assms(2) have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem C S''"
      by (simp add: sem_def, rule_tac x = "\<sigma>\<^sub>p" in exI, simp)
    with a0 show "(s', l) \<in> ?B"
      by auto
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?B"
    then obtain \<sigma>\<^sub>l  \<sigma>\<^sub>p' where "s' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')" "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem C S''"
      by blast
    then obtain \<sigma>\<^sub>p where "(\<sigma>\<^sub>l, \<sigma>\<^sub>p) \<in> S'" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'"
      by (smt (verit) Pair_inject append_self_conv2 assms(2) mem_Collect_eq sem_def)
    then show "(s', l) \<in> ?A"
      using SingleB in_par_sem assms 
      by (smt (verit) \<open>s' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')\<close> ex2gstate.simps(1) ex_logical_same.simps(1) fst_conv mem_Collect_eq sndI)
  qed
qed

lemma par_sem_parallel:
  "par_sem (Parallel C1 chs C2) {ExParState s1 s2 |s1 s2. s1 \<in> S1 \<and> s2 \<in> S2} = 
  {(ExParState s1 s2, l) |s1 s2 l1 l2 l. 
  (s1, l1) \<in> par_sem C1 S1 \<and> (s2, l2) \<in> par_sem C2 S2 \<and> combine_blocks chs l1 l2 l}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof(rule subsetPairI)
    fix s' l assume a0: "(s', l) \<in> ?A"
    then obtain s where "s \<in> {ExParState s1 s2 |s1 s2. s1 \<in> S1 \<and> s2 \<in> S2}" 
    "par_big_step (Parallel C1 chs C2) (ex2gstate s) l (ex2gstate s')"
      by (metis (no_types, lifting) fst_eqD in_par_sem snd_eqD)
    with a0 obtain s1 s2 l1 l2 s1' s2' where "s1 \<in> S1" "s2 \<in> S2" 
    "par_big_step C1 (ex2gstate s1) l1 (ex2gstate s1')"
    "ex_logical_same s1 s1'" "ex_logical_same s2 s2'" "par_big_step C2 (ex2gstate s2) l2 (ex2gstate s2')"
    "combine_blocks chs l1 l2 l" "s' = ExParState s1' s2'"
      by (smt (verit, ccfv_threshold) ParallelE ex2gstate.simps(2) ex_sem_par_logical exgstate.inject(2) 
          fst_conv gstate.inject(2) in_par_sem mem_Collect_eq snd_conv) 
    then show "(s', l) \<in> ?B"
      by (metis (mono_tags, lifting) CollectI fst_conv in_par_sem snd_conv)
  qed
  show "?B \<subseteq> ?A"
  proof(rule subsetPairI)
    fix s' l assume "(s', l) \<in> ?B"
    then show "(s', l) \<in> ?A"
      using ParallelB in_par_sem 
      by (smt (z3) ex2gstate.simps(2) ex_logical_same.simps(2) fst_conv mem_Collect_eq snd_conv)
  qed
qed

end