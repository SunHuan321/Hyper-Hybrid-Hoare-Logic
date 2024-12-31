theory ProgramHyperproperties
  imports Logic
begin

type_synonym progran_hyperproperty = "(gstate \<times> trace \<times> gstate) set \<Rightarrow> bool"

definition set_of_traces where 
  "set_of_traces C = {(s, l, s') |s s' l. par_big_step C s l s'}"

definition hypersat :: "pproc \<Rightarrow> progran_hyperproperty \<Rightarrow> bool" where
  "hypersat C H \<longleftrightarrow> H {(s, l, s') |s l s'. par_big_step C s l s'}"

definition injective where
  "injective f \<longleftrightarrow> (\<forall>a b. a \<noteq> b \<longrightarrow> f a \<noteq> f b)"

definition copy_p_state where
  "copy_p_state to_pvar to_lval \<sigma> x = to_lval (\<sigma> (to_pvar x))"

definition recover_p_state where
  "recover_p_state to_pval to_lvar l x = to_pval (l (to_lvar x))"

fun copy_p_gstate :: "('lvar \<Rightarrow> var) \<Rightarrow> (real \<Rightarrow> 'lval) \<Rightarrow> ('lvar, 'lval) exgstate \<Rightarrow> ('lvar, 'lval) exgstate" where
  "copy_p_gstate to_pvar to_lval (ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p)) = ExState (copy_p_state to_pvar to_lval \<sigma>\<^sub>p, \<sigma>\<^sub>p)"
| "copy_p_gstate to_pvar to_lval (ExParState s1 s2) = ExParState (copy_p_gstate to_pvar to_lval s1)
                                                                 (copy_p_gstate to_pvar to_lval s2)"

fun recover_p_gstate :: "('lval \<Rightarrow> real) \<Rightarrow> (var \<Rightarrow> 'lvar) \<Rightarrow> ('lvar, 'lval) exgstate \<Rightarrow> gstate" where
  "recover_p_gstate to_pval to_lvar (ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p)) = State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l)"
| "recover_p_gstate to_pval to_lvar (ExParState s1 s2) = ParState (recover_p_gstate to_pval to_lvar s1) 
                                                                   (recover_p_gstate to_pval to_lvar s2)"

lemma copy_p_gstate_same:
 "ex2gstate (copy_p_gstate to_pvar to_lval e) = ex2gstate e"
proof(induct e)
  case (ExState x)
  then show ?case
    by (metis copy_p_gstate.simps(1) ex2gstate.simps(1) split_pairs)
next
  case (ExParState e1 e2)
  then show ?case
    by simp
qed

lemma injective_then_exists_inverse:
  assumes "injective to_lvar"
  shows "\<exists>to_pvar. (\<forall>x. to_pvar (to_lvar x) = x)"
proof -
  let ?to_pvar = "\<lambda>y. SOME x. to_lvar x = y"
  have "\<And>x. ?to_pvar (to_lvar x) = x"
    by (metis (mono_tags, lifting) assms injective_def someI)
  then show ?thesis
    by force
qed

lemma in_set_of_traces_then_in_sem:
  assumes "(ex2gstate e, l, ex2gstate e') \<in> set_of_traces C"
      and "e \<in> S"
      and "ex_logical_same e e'"
    shows "(e', l) \<in> par_sem C S"
  using assms(1) assms(2) assms(3) fst_conv in_par_sem set_of_traces_def by fastforce

lemma recover_from_logical_same:
  assumes "\<exists>e0. e = copy_p_gstate to_pvar to_lval e0"
      and "ex_logical_same e e'"
      and "\<And>x. to_pvar (to_lvar x) = x"
      and "\<And>x. to_pval (to_lval x) = x"
    shows "recover_p_gstate to_pval to_lvar e' = ex2gstate e"
  using assms
proof(induct e arbitrary: e')
  case (ExState x)
  then show ?case
  proof-
    obtain \<sigma>\<^sub>l \<sigma>\<^sub>p where b0: "x = (\<sigma>\<^sub>l, \<sigma>\<^sub>p)"
      by fastforce
    with ExState.prems(2) obtain \<sigma>\<^sub>p' where "e' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')"
      by (metis copy_p_gstate.elims ex_logical_same.simps(1) ex_logical_same.simps(4) exgstate.simps(4) fst_conv)
    from ExState.prems(1) b0 have "\<sigma>\<^sub>l = copy_p_state to_pvar to_lval \<sigma>\<^sub>p"
      by (smt (verit, ccfv_SIG) copy_p_gstate.elims exgstate.distinct(1) exgstate.inject(1) old.prod.inject)
    also have "recover_p_gstate to_pval to_lvar e' = State \<sigma>\<^sub>p"
    proof-
      have "recover_p_state to_pval to_lvar \<sigma>\<^sub>l = \<sigma>\<^sub>p"
      proof (rule ext)
        fix x show "recover_p_state to_pval to_lvar \<sigma>\<^sub>l x = \<sigma>\<^sub>p x"
          by (simp add: calculation assms(3) assms(4) copy_p_state_def recover_p_state_def)
      qed
      then show ?thesis
        by (simp add: \<open>e' = ExState (\<sigma>\<^sub>l, \<sigma>\<^sub>p')\<close>)
    qed
    then show ?thesis
      by (simp add: b0)
  qed
next
  case (ExParState e1 e2)
  then show ?case
  proof-
    obtain e0 where "ExParState e1 e2 = copy_p_gstate to_pvar to_lval e0"
      using ExParState.prems(1) by blast
    then obtain e1' e2' where b0: "e1 = copy_p_gstate to_pvar to_lval e1'" "e2 = copy_p_gstate to_pvar to_lval e2'"
      by (smt (verit, ccfv_SIG) copy_p_gstate.elims exgstate.distinct(1) exgstate.inject(2))  
    from ExParState.prems(2) obtain e1'' e2'' where b1: "e' = ExParState e1'' e2''"
    "ex_logical_same e1 e1''" "ex_logical_same e2 e2''"
      by (metis ex_logical_same.simps(2) ex_logical_same.simps(3) exgstate.exhaust)
    then have "recover_p_gstate to_pval to_lvar e1'' = ex2gstate e1"
              "recover_p_gstate to_pval to_lvar e2'' = ex2gstate e2"
      using ExParState.hyps(1) ExParState.hyps(2) assms(3) assms(4) b0(1)  b0(2) b1(3) by blast+
    then show ?thesis
      by (simp add: b1(1))
  qed
qed

lemma recover_from_logical_gstate:
  assumes "e = copy_p_gstate to_pvar to_lval e0"
      and "ex2gstate e0 = s"
      and "\<And>x. to_pvar (to_lvar x) = x"
      and "\<And>x. to_pval (to_lval x) = x"
    shows "recover_p_gstate to_pval to_lvar e = s"
  by (metis assms(1) assms(2) assms(3) assms(4) copy_p_gstate_same ex_logical_same_refl recover_from_logical_same)

lemma gstate_construct_exstate:
  "\<exists>e. ex2gstate e = s"
proof(induct s)
  case (State x)
  then show ?case
    by (metis ex2gstate.simps(1) fst_conv snd_swap)
next
  case (ParState s1 s2)
  then show ?case
    using ex2gstate.simps(2) by blast
qed

lemma gstate_construct_exstate_pair:
  assumes "par_big_step C s l s'"
      and "ex2gstate e = s"
    shows "\<exists>e'. ex_logical_same e e' \<and> s' = ex2gstate e'"
  using assms
proof(induct e arbitrary: C s l s')
  case (ExState x)
  then show ?case
  proof-
    have "s = State (snd x)"
      using ExState.prems(2) by auto
    then obtain \<sigma>\<^sub>p' where "s' = State \<sigma>\<^sub>p'"
      using ExState.prems(1) par_big_step.simps by blast      
    then have "ex_logical_same (ExState x) (ExState (fst x, \<sigma>\<^sub>p'))"
      by simp
    moreover show ?thesis
      by (metis \<open>s' = State \<sigma>\<^sub>p'\<close> calculation ex2gstate.simps(1) snd_conv)
  qed
next
  case (ExParState e1 e2)
  then show ?case
  proof-
    obtain s1 s2 where "s = ParState s1 s2" "ex2gstate e1 = s1" "ex2gstate e2 = s2"
      using ExParState.prems(2) by auto
    then obtain C1 chs C2 where "C = Parallel C1 chs C2"
      using ExParState.prems(1) par_big_step.simps by blast
    then obtain s1' s2' l1 l2 where "par_big_step C1 s1 l1 s1'" "par_big_step C2 s2 l2 s2'"
      "s' = ParState s1' s2'"
      by (smt (verit, best) ExParState.prems(1) ParallelE \<open>s = ParState s1 s2\<close> gstate.inject(2))
    then obtain e1' e2' where "ex_logical_same e1 e1' \<and> ex2gstate e1' = s1'" 
                              "ex_logical_same e2 e2' \<and> ex2gstate e2' = s2'"
      using ExParState.hyps(1) ExParState.hyps(2) \<open>ex2gstate e1 = s1\<close> \<open>ex2gstate e2 = s2\<close> by blast
    then show ?thesis
      by (metis \<open>s' = ParState s1' s2'\<close> ex2gstate.simps(2) ex_logical_same.simps(2))
  qed
qed

lemma set_of_traces_same:
  assumes "\<And>x. to_pvar (to_lvar x) = x"
      and "\<And>x. to_pval (to_lval x) = x"
      and "S = {copy_p_gstate to_pvar to_lval e |e. True}"
    shows "{(recover_p_gstate to_pval to_lvar e, l, ex2gstate e') |e e' l. (e', l) \<in> par_sem C S
    \<and> ex_logical_same e e'} = set_of_traces C" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix s s' l assume asm0: "(s, l, s') \<in> ?A"
    then obtain e e' where asm1: "(e', l) \<in> par_sem C S" "ex_logical_same e e'" 
   "s = recover_p_gstate to_pval to_lvar e" "s' = ex2gstate e'"
      by blast
    obtain e0 where asm2 :"e0 \<in> S" "par_big_step C (ex2gstate e0) l s'" "ex_logical_same e0 e'"
      using asm1(1) asm1(4) by (metis fst_conv in_par_sem snd_conv)
    with asm1(2) have asm3: "ex_logical_same e0 e"
      using ex_logical_same_comm ex_logical_same_trans by blast
    from asm2(1) assms(3) have "\<exists>e. e0 = copy_p_gstate to_pvar to_lval e" by auto
    with asm3 assms(1) assms(2) asm1(3) have "s = ex2gstate e0"
      using recover_from_logical_same[of e0 to_pvar to_lval e to_lvar to_pval] by blast
    with asm1 (4) asm2 (2) show "(s, l, s') \<in> ?B"
      by (simp add: set_of_traces_def)
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetTupleI)
    fix s s' l assume "(s, l, s') \<in> ?B"
    then have assm0: "par_big_step C s l s'"
      by (simp add: set_of_traces_def)
    obtain e where assm1: "s = recover_p_gstate to_pval to_lvar e" "e \<in> S" "ex2gstate e = s"
(* from s can consturct e' where ex2gstate e' = s, and then e = copy_p_gstate e'*)
      by (metis (mono_tags, lifting) CollectI assms(1) assms(2) assms(3) copy_p_gstate_same 
         gstate_construct_exstate recover_from_logical_gstate)      
    with assm0 obtain e' where assm2: "ex_logical_same e e'"  "s' = ex2gstate e'"
(* proof by induction, but rely on the compilance of s s' *)
      using gstate_construct_exstate_pair by blast
    then have "(e', l) \<in> par_sem C S"
      using \<open>(s, l, s') \<in> set_of_traces C\<close> assm1(2) assm1(3) in_set_of_traces_then_in_sem by blast
    then show "(s, l, s') \<in> ?A"
      using assm1(1) assm2(1) assm2(2) by blast
  qed
qed

theorem proving_hyperproperties:

  fixes to_lvar :: " var \<Rightarrow> 'lvar"
  fixes to_lval :: " real \<Rightarrow> 'lval"

  assumes "injective to_lvar"
      and "injective to_lval"

shows "\<exists>P :: (('lvar, 'lval) exgstate) set \<Rightarrow> bool. 
       \<exists>Q :: (('lvar, 'lval) exgstate \<times> trace) set \<Rightarrow> bool. 
       (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile>\<^sub>P {P} C {Q})"
proof-

  obtain to_pval :: "'lval \<Rightarrow> real" where r1: "\<And>x. to_pval (to_lval x) = x"
    using assms(2) injective_then_exists_inverse by blast

  obtain to_pvar :: "'lvar \<Rightarrow> var" where r2: "\<And>x. to_pvar (to_lvar x) = x"
    using assms(1) injective_then_exists_inverse by blast

  let ?P = "\<lambda>S. S = {copy_p_gstate to_pvar to_lval e |e. True}"
  let ?Q = "\<lambda>S. H {(recover_p_gstate to_pval to_lvar e, l, ex2gstate e') |e e' l. (e', l) \<in> S \<and> ex_logical_same e e'}"

  have "\<And>C. hypersat C H \<longleftrightarrow> \<Turnstile>\<^sub>P {?P} C {?Q}"
  proof
    fix C
    assume "hypersat C H"
    show "\<Turnstile>\<^sub>P {?P} C {?Q}"
    proof (rule par_hyper_hoare_tripleI)
      fix S assume a0: "S = {copy_p_gstate to_pvar to_lval e |e. True}"
      have "{(recover_p_gstate to_pval to_lvar e, l, ex2gstate e') |e e' l. (e', l) \<in> par_sem C S \<and> 
            ex_logical_same e e'} =  set_of_traces C"
        using a0 set_of_traces_same[of to_pvar to_lvar to_pval to_lval]
        r1 r2 by auto
      then show "H {(recover_p_gstate to_pval to_lvar e, l, ex2gstate e') |e e' l. (e', l) \<in> par_sem C S \<and> ex_logical_same e e'}"
        by (smt (verit, best) Collect_cong \<open>hypersat C H\<close> hypersat_def set_of_traces_def)
    qed
  next
    fix C
    let ?S = "{copy_p_gstate to_pvar to_lval e |e. True}"
    assume "\<Turnstile>\<^sub>P {?P} C {?Q}"
    then have "?Q (par_sem C ?S)"
      using par_hyper_hoare_tripleE by blast
    moreover have "{(recover_p_gstate to_pval to_lvar e, l, ex2gstate e') |e e' l. (e', l) \<in> par_sem C ?S 
    \<and> ex_logical_same e e'} = set_of_traces C"
      using r1 r2 set_of_traces_same[of to_pvar to_lvar to_pval to_lval]
      by presburger
    ultimately show "hypersat C H"
      by (smt (verit, best) Collect_cong hypersat_def set_of_traces_def)
  qed
  then show ?thesis
    by blast
qed

definition semify where
  "semify \<Sigma> S = {(s', l) |s' s l. s \<in> S \<and> (ex2gstate s, l, ex2gstate s') \<in> \<Sigma> \<and> ex_logical_same s s'}"

definition hyperprop_hht where
  "hyperprop_hht P Q \<Sigma> \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (semify \<Sigma> S))"

lemma semify_eq_traces: 
  "semify (set_of_traces C) S = par_sem C S"
proof-
  have "\<And>s' l. (s', l) \<in> par_sem C S \<longleftrightarrow> (s', l) \<in> semify (set_of_traces C) S"
  proof-
    fix s' l
    have "(s', l) \<in> par_sem C S \<longleftrightarrow> (\<exists>s. s \<in> S \<and> par_big_step C (ex2gstate s) l (ex2gstate s') 
          \<and> ex_logical_same s s')"
      using in_par_sem[of "(s', l)" C S] by auto
    also have "... \<longleftrightarrow> (\<exists>s. s \<in> S \<and> (ex2gstate s, l, ex2gstate s') \<in> set_of_traces C \<and> ex_logical_same s s')"
      using set_of_traces_def by fastforce
    then show "(s', l) \<in> par_sem C S \<longleftrightarrow> (s', l) \<in> semify (set_of_traces C) S"
      by (simp add: calculation semify_def)
  qed
  then show ?thesis
    by auto
qed

theorem any_hht_hyperprop:
  "\<Turnstile>\<^sub>P {P} C {Q} \<longleftrightarrow> hypersat C (hyperprop_hht P Q)" (is "?A \<longleftrightarrow> ?B")
  by (smt (verit, best) Collect_cong hyperprop_hht_def hypersat_def par_hyper_hoare_triple_def 
      semify_eq_traces set_of_traces_def)







