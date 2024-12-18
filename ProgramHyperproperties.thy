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
  assumes "(s\<^sub>p, l, s\<^sub>p') \<in> set_of_traces C"
      and "(s\<^sub>l, s\<^sub>p) \<in> S"
    shows "(s\<^sub>l, s\<^sub>p', l) \<in> par_sem C S"
  using assms(1) assms(2) in_par_sem set_of_traces_def by fastforce

lemma set_of_single_traces_same:
  assumes "\<And>x. to_pvar (to_lvar x) = x"
      and "\<And>x. to_pval (to_lval x) = x"
      and "S = {(copy_p_state to_pvar to_lval \<sigma>\<^sub>p, State \<sigma>\<^sub>p) |\<sigma>\<^sub>p. True}"
    shows "{(State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l), l, State \<sigma>\<^sub>p') |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S} = set_of_traces (Single C)"
(is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof (rule subsetTupleI)
    fix s\<^sub>p s\<^sub>p' l assume asm0: "(s\<^sub>p, l, s\<^sub>p') \<in> ?A"
    then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p' where asm1: "s\<^sub>p = State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l)" 
    "(\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S" "s\<^sub>p' = State \<sigma>\<^sub>p'"
      by blast
    then obtain \<sigma>\<^sub>p where "(\<sigma>\<^sub>l, State \<sigma>\<^sub>p) \<in> S" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'"
      by (smt (verit, del_insts) SingleE fst_conv gstate.inject(1) in_par_sem snd_conv)     
    then have "\<sigma>\<^sub>l = copy_p_state to_pvar to_lval \<sigma>\<^sub>p"
      using assms(3) by blast
    moreover have "s\<^sub>p = State \<sigma>\<^sub>p"
      sledgehammer
    proof -
      have f1: "\<forall>f fa fb a. copy_p_state fb f fa (a::'a) = (f (fa (fb a::char)::real)::'b)"
        by (simp add: copy_p_state_def)
      have f2: "\<forall>f fa fb c. recover_p_state f fb fa (c::char) = (f (fa (fb c::'a)::'b)::real)"
        by (simp add: recover_p_state_def)
      obtain bb :: "'a \<Rightarrow> 'b" where
        f3: "s\<^sub>p = State (recover_p_state to_pval to_lvar bb) \<and> s\<^sub>p = State (recover_p_state to_pval to_lvar bb)"
        using \<open>\<And>thesis. (\<And>\<sigma>\<^sub>l \<sigma>\<^sub>p'. \<lbrakk>s\<^sub>p = State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l); (\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S; s\<^sub>p' = State \<sigma>\<^sub>p'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by moura
      then have "State (recover_p_state to_pval to_lvar bb) = State (recover_p_state to_pval to_lvar (copy_p_state to_pvar to_lval \<sigma>\<^sub>p))"
        using asm1(1) calculation by argo
      then show ?thesis
        using f3 f2 f1 assms(1) assms(2) by fastforce
    qed
    ultimately show "(s\<^sub>p, l, s\<^sub>p') \<in> ?B"
      by (simp add: SingleB \<open>big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'\<close> \<open>s\<^sub>p' = State \<sigma>\<^sub>p'\<close> set_of_traces_def)
  qed
  show "?B \<subseteq> ?A"
  proof (rule subsetTupleI)
    fix s\<^sub>p s\<^sub>p' l assume asm0: "(s\<^sub>p, l, s\<^sub>p') \<in> ?B"
    then obtain \<sigma>\<^sub>p \<sigma>\<^sub>p' where asm1: "s\<^sub>p = State \<sigma>\<^sub>p" "s\<^sub>p' = State \<sigma>\<^sub>p'" "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'"
      by (smt (verit) Pair_inject SingleE mem_Collect_eq set_of_traces_def)
    let ?\<sigma>\<^sub>l = "copy_p_state to_pvar to_lval \<sigma>\<^sub>p"
    have "(?\<sigma>\<^sub>l, State \<sigma>\<^sub>p) \<in> S"
      using assms(3) by blast
    then have "(?\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S"
      using asm0 asm1 in_set_of_traces_then_in_sem by blast
    moreover have "recover_p_state to_pval to_lvar ?\<sigma>\<^sub>l = \<sigma>\<^sub>p"
    proof -
      have f1: "\<forall>f fa fb a. copy_p_state fb f fa (a::'a) = (f (fa (fb a::char)::real)::'b)"
        by (meson copy_p_state_def)
      have "\<forall>f fa fb c. recover_p_state f fb fa (c::char) = (f (fa (fb c::'a)::'b)::real)"
        by (simp add: recover_p_state_def)
      then show ?thesis
        using f1 assms(1) assms(2) by auto
    qed
    ultimately show "(s\<^sub>p, l, s\<^sub>p') \<in> ?A"
      using asm1(1) asm1(2) by force
    qed
  qed


theorem proving_hyperproperties:

  fixes to_lvar :: " var \<Rightarrow> 'lvar"
  fixes to_lval :: " real \<Rightarrow> 'lval"

  assumes "injective to_lvar"
      and "injective to_lval"

shows "\<exists>P :: (('lvar, 'lval) lstate \<times> gstate) set \<Rightarrow> bool. 
       \<exists>Q :: (('lvar, 'lval) lstate \<times> gstate \<times> trace) set \<Rightarrow> bool. 
       (\<forall>C. hypersat (Single C) H \<longleftrightarrow> \<Turnstile>\<^sub>P {P} (Single C) {Q})"
proof-

  obtain to_pval :: "'lval \<Rightarrow> real" where r1: "\<And>x. to_pval (to_lval x) = x"
    using assms(2) injective_then_exists_inverse by blast

  obtain to_pvar :: "'lvar \<Rightarrow> var" where r2: "\<And>x. to_pvar (to_lvar x) = x"
    using assms(1) injective_then_exists_inverse by blast

  let ?P = "\<lambda>S. S = {(copy_p_state to_pvar to_lval \<sigma>\<^sub>p, State \<sigma>\<^sub>p) |\<sigma>\<^sub>p. True}"
  let ?Q = "\<lambda>S. H {(State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l), l, State \<sigma>\<^sub>p') |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l , State \<sigma>\<^sub>p', l) \<in> S }"

  have "\<And>C. hypersat (Single C) H \<longleftrightarrow> \<Turnstile>\<^sub>P {?P} (Single C) {?Q}"
  proof
    fix C
    assume "hypersat (Single C) H"
    show "\<Turnstile>\<^sub>P {?P} (Single C) {?Q}"
    proof (rule par_hyper_hoare_tripleI)
      fix S assume "S = {(copy_p_state to_pvar to_lval \<sigma>\<^sub>p, State \<sigma>\<^sub>p) |\<sigma>\<^sub>p. True}"
      have "{(State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l), l, State \<sigma>\<^sub>p') |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S} = set_of_traces (Single C)"
        using \<open>S = {(copy_p_state to_pvar to_lval \<sigma>\<^sub>p, State \<sigma>\<^sub>p) |\<sigma>\<^sub>p. True}\<close> set_of_single_traces_same[of to_pvar to_lvar to_pval to_lval]
        r1 r2 by auto
      then show "H {(State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l), l, State \<sigma>\<^sub>p') |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) S}"
        by (smt (verit, best) Collect_cong \<open>hypersat (Single C) H\<close> hypersat_def set_of_traces_def)
    qed
  next
    fix C
    let ?S = "{(copy_p_state to_pvar to_lval \<sigma>\<^sub>p, State \<sigma>\<^sub>p) |\<sigma>\<^sub>p. True }"
    assume "\<Turnstile>\<^sub>P {?P} (Single C) {?Q}"
    then have "?Q (par_sem (Single C) ?S)"
      using par_hyper_hoare_tripleE by blast
    moreover have "{(State (recover_p_state to_pval to_lvar \<sigma>\<^sub>l), l, State \<sigma>\<^sub>p') |\<sigma>\<^sub>l \<sigma>\<^sub>p' l. (\<sigma>\<^sub>l, State \<sigma>\<^sub>p', l) \<in> par_sem (Single C) ?S} = set_of_traces (Single C)"
      using r1 r2 set_of_single_traces_same[of to_pvar to_lvar to_pval to_lval]
      by presburger
    ultimately show "hypersat (Single C) H"
      by (smt (verit, best) Collect_cong hypersat_def set_of_traces_def)
  qed
  then show ?thesis
    by blast
qed

definition semify where
  "semify \<Sigma> S = { (s', l) |s' s l. s \<in> S \<and> (s, l, s') \<in> \<Sigma> }"

definition hyperprop_hht where
  "hyperprop_hht P Q \<Sigma> \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (semify \<Sigma> S))"

lemma semify_eq_traces: 
  "semify (set_of_traces C) S = par_sem C S"
proof-
  have "\<And>s' l. (s', l) \<in> par_sem C S \<longleftrightarrow> (s', l) \<in> semify (set_of_traces C) S"
  proof-
    fix s' l
    have "(s', l) \<in> par_sem C S \<longleftrightarrow> (\<exists>s.  s \<in> S \<and> par_big_step C s l s')"
      by (simp add: in_par_sem)
    also have "... \<longleftrightarrow> (\<exists>s. s \<in> S \<and> (s, l, s') \<in> set_of_traces C)"
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







