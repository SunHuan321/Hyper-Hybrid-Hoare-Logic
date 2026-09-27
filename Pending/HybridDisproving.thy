theory HybridDisproving
  imports H3L_Core.ProgramHyperproperties
begin

subsection \<open>Disproving Hyper-Triples\<close>

definition sat :: "'a hyperassertion \<Rightarrow> bool" where
  "sat P \<longleftrightarrow> (\<exists>S. P S)"

lemma sat_hyperassertionI:
  assumes "P S"
  shows "sat P"
  using assms by (auto simp add: sat_def)

lemma sat_hyperassertionE:
  assumes "sat P"
  obtains S where "P S"
  using assms by (auto simp add: sat_def)

subsection \<open>Hybrid Incorrectness Witnesses\<close>

definition sat_h3l ::
  "(('lvar, 'lval) exstate) hyperassertion \<Rightarrow> proc \<Rightarrow>
   (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "sat_h3l P C S' \<longleftrightarrow> (\<exists>S. P S \<and> S' = sem C S)"

definition par_sat_h3l ::
  "(('lvar, 'lval) exgstate) hyperassertion \<Rightarrow> pproc \<Rightarrow>
   (('lvar, 'lval) exgstate \<times> trace) set \<Rightarrow> bool" where
  "par_sat_h3l P C S' \<longleftrightarrow> (\<exists>S. P S \<and> S' = par_sem C S)"

definition hybrid_disproving_triple ::
  "(('lvar, 'lval) exstate) hyperassertion \<Rightarrow> proc \<Rightarrow>
   (('lvar, 'lval) exstate) hyperassertion \<Rightarrow> bool" where
  "hybrid_disproving_triple P C Q \<longleftrightarrow> (\<exists>S. P S \<and> Q (sem C S))"

definition par_hybrid_disproving_triple ::
  "(('lvar, 'lval) exgstate) hyperassertion \<Rightarrow> pproc \<Rightarrow>
   (('lvar, 'lval) exgstate \<times> trace) hyperassertion \<Rightarrow> bool" where
  "par_hybrid_disproving_triple P C Q \<longleftrightarrow> (\<exists>S. P S \<and> Q (par_sem C S))"

lemma hybrid_disproving_tripleI:
  assumes "P S"
      and "Q (sem C S)"
    shows "hybrid_disproving_triple P C Q"
  using assms by (auto simp add: hybrid_disproving_triple_def)

lemma hybrid_disproving_tripleE:
  assumes "hybrid_disproving_triple P C Q"
  obtains S where "P S" "Q (sem C S)"
  using assms by (auto simp add: hybrid_disproving_triple_def)

lemma par_hybrid_disproving_tripleI:
  assumes "P S"
      and "Q (par_sem C S)"
    shows "par_hybrid_disproving_triple P C Q"
  using assms by (auto simp add: par_hybrid_disproving_triple_def)

lemma par_hybrid_disproving_tripleE:
  assumes "par_hybrid_disproving_triple P C Q"
  obtains S where "P S" "Q (par_sem C S)"
  using assms by (auto simp add: par_hybrid_disproving_triple_def)

lemma hybrid_disproving_triple_sat_h3l:
  "hybrid_disproving_triple P C Q \<longleftrightarrow> (\<exists>S'. sat_h3l P C S' \<and> Q S')"
  by (auto simp add: hybrid_disproving_triple_def sat_h3l_def)

lemma par_hybrid_disproving_triple_sat_h3l:
  "par_hybrid_disproving_triple P C Q \<longleftrightarrow> (\<exists>S'. par_sat_h3l P C S' \<and> Q S')"
  by (auto simp add: par_hybrid_disproving_triple_def par_sat_h3l_def)

theorem hybrid_disproving_triple_iff_not_hht:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> hybrid_disproving_triple P C (\<lambda>S. \<not> Q S)"
  unfolding hyper_hoare_triple_def hybrid_disproving_triple_def
  by auto

theorem par_hybrid_disproving_triple_iff_not_hht:
  "\<not> \<Turnstile>\<^sub>P {P} C {Q} \<longleftrightarrow> par_hybrid_disproving_triple P C (\<lambda>S. \<not> Q S)"
  unfolding par_hyper_hoare_triple_def par_hybrid_disproving_triple_def
  by auto

lemma hybrid_disproving_triple_hht:
  "hybrid_disproving_triple P C Q \<longleftrightarrow>
   (\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {Q})"
proof
  assume "hybrid_disproving_triple P C Q"
  then obtain S where asm0: "P S" "Q (sem C S)"
    unfolding hybrid_disproving_triple_def by auto
  let ?P = "\<lambda>S'. S = S'"
  have "sat ?P"
    unfolding sat_def by auto
  moreover have "hyper_entails ?P P"
    using asm0(1) unfolding hyper_entails_def by auto
  moreover have "\<Turnstile> {?P} C {Q}"
    using asm0(2) unfolding hyper_hoare_triple_def by auto
  ultimately show "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {Q}"
    by auto
next
  assume "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {Q}"
  then obtain P' where asm0: "sat P'" "hyper_entails P' P" "\<Turnstile> {P'} C {Q}"
    by auto
  then obtain S where "P' S"
    unfolding sat_def by auto
  then have "P S"
    using asm0(2) unfolding hyper_entails_def by auto
  moreover have "Q (sem C S)"
    using \<open>P' S\<close> asm0(3) unfolding hyper_hoare_triple_def by auto
  ultimately show "hybrid_disproving_triple P C Q"
    unfolding hybrid_disproving_triple_def by auto
qed

lemma par_hybrid_disproving_triple_hht:
  "par_hybrid_disproving_triple P C Q \<longleftrightarrow>
   (\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {Q})"
proof
  assume "par_hybrid_disproving_triple P C Q"
  then obtain S where asm0: "P S" "Q (par_sem C S)"
    unfolding par_hybrid_disproving_triple_def by auto
  let ?P = "\<lambda>S'. S = S'"
  have "sat ?P"
    unfolding sat_def by auto
  moreover have "hyper_entails ?P P"
    using asm0(1) unfolding hyper_entails_def by auto
  moreover have "\<Turnstile>\<^sub>P {?P} C {Q}"
    using asm0(2) unfolding par_hyper_hoare_triple_def by auto
  ultimately show "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {Q}"
    by auto
next
  assume "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {Q}"
  then obtain P' where asm0: "sat P'" "hyper_entails P' P" "\<Turnstile>\<^sub>P {P'} C {Q}"
    by auto
  then obtain S where "P' S"
    unfolding sat_def by auto
  then have "P S"
    using asm0(2) unfolding hyper_entails_def by auto
  moreover have "Q (par_sem C S)"
    using \<open>P' S\<close> asm0(3) unfolding par_hyper_hoare_triple_def by auto
  ultimately show "par_hybrid_disproving_triple P C Q"
    unfolding par_hybrid_disproving_triple_def by auto
qed

theorem disproving_triple:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow>
   (\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})"
proof
  assume "\<not> \<Turnstile> {P} C {Q}"
  then obtain S where asm0: "P S" "\<not> Q (sem C S)"
    unfolding hyper_hoare_triple_def by auto
  let ?P = "\<lambda>S'. S = S'"
  have "sat ?P"
    unfolding sat_def by auto
  moreover have "hyper_entails ?P P"
    using asm0(1) unfolding hyper_entails_def by auto
  moreover have "\<Turnstile> {?P} C {\<lambda>S. \<not> Q S}"
    using asm0(2) unfolding hyper_hoare_triple_def by auto
  ultimately show "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S}"
    by auto
next
  assume "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S}"
  then obtain P' where asm0: "sat P'" "hyper_entails P' P" "\<Turnstile> {P'} C {\<lambda>S. \<not> Q S}"
    by auto
  then obtain S where "P' S"
    unfolding sat_def by auto
  then have "P S"
    using asm0(2) unfolding hyper_entails_def by auto
  moreover have "\<not> Q (sem C S)"
    using \<open>P' S\<close> asm0(3) unfolding hyper_hoare_triple_def by auto
  ultimately show "\<not> \<Turnstile> {P} C {Q}"
    unfolding hyper_hoare_triple_def by auto
qed

theorem par_disproving_triple:
  "\<not> \<Turnstile>\<^sub>P {P} C {Q} \<longleftrightarrow>
   (\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {\<lambda>S. \<not> Q S})"
proof
  assume "\<not> \<Turnstile>\<^sub>P {P} C {Q}"
  then obtain S where asm0: "P S" "\<not> Q (par_sem C S)"
    unfolding par_hyper_hoare_triple_def by auto
  let ?P = "\<lambda>S'. S = S'"
  have "sat ?P"
    unfolding sat_def by auto
  moreover have "hyper_entails ?P P"
    using asm0(1) unfolding hyper_entails_def by auto
  moreover have "\<Turnstile>\<^sub>P {?P} C {\<lambda>S. \<not> Q S}"
    using asm0(2) unfolding par_hyper_hoare_triple_def by auto
  ultimately show "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {\<lambda>S. \<not> Q S}"
    by auto
next
  assume "\<exists>P'. sat P' \<and> hyper_entails P' P \<and> \<Turnstile>\<^sub>P {P'} C {\<lambda>S. \<not> Q S}"
  then obtain P' where asm0: "sat P'" "hyper_entails P' P" "\<Turnstile>\<^sub>P {P'} C {\<lambda>S. \<not> Q S}"
    by auto
  then obtain S where "P' S"
    unfolding sat_def by auto
  then have "P S"
    using asm0(2) unfolding hyper_entails_def by auto
  moreover have "\<not> Q (par_sem C S)"
    using \<open>P' S\<close> asm0(3) unfolding par_hyper_hoare_triple_def by auto
  ultimately show "\<not> \<Turnstile>\<^sub>P {P} C {Q}"
    unfolding par_hyper_hoare_triple_def by auto
qed

theorem par_disproves_hyperprop_hht:
  assumes "par_hybrid_disproving_triple P C (\<lambda>S. \<not> Q S)"
  shows "\<not> hypersat C (hyperprop_hht P Q)"
proof -
  have "\<not> \<Turnstile>\<^sub>P {P} C {Q}"
    using assms
    unfolding par_hybrid_disproving_triple_def par_hyper_hoare_triple_def
    by auto
  then show ?thesis
    using any_hht_hyperprop[of P C Q] by simp
qed

subsection \<open>Incorrectness Logic Encodings\<close>

definition seq_IL where
  "seq_IL P C Q \<longleftrightarrow> Q \<subseteq> sem C P"

theorem seq_IL_encoding:
  "seq_IL P C Q \<longleftrightarrow> \<Turnstile> {under_approx P} C {under_approx Q}"
proof
  assume "\<Turnstile> {under_approx P} C {under_approx Q}"
  then have "under_approx Q (sem C P)"
    by (simp add: hyper_hoare_triple_def under_approx_def)
  then show "seq_IL P C Q"
    by (simp add: seq_IL_def under_approx_def)
next
  assume "seq_IL P C Q"
  then have Q_sub: "Q \<subseteq> sem C P"
    unfolding seq_IL_def by simp
  show "\<Turnstile> {under_approx P} C {under_approx Q}"
  proof (rule hyper_hoare_tripleI)
    fix S
    assume "under_approx P S"
    then have "P \<subseteq> S"
      unfolding under_approx_def by simp
    then have "sem C P \<subseteq> sem C S"
      by (rule sem_monotonic)
    with Q_sub show "under_approx Q (sem C S)"
      unfolding under_approx_def by auto
  qed
qed

lemma seq_IL_witness:
  assumes "seq_IL P C Q"
      and "\<phi>' \<in> Q"
  obtains \<phi> tr where "\<phi> \<in> P"
      and "lproj \<phi> = lproj \<phi>'"
      and "big_step C (pproj \<phi>) tr (pproj \<phi>')"
      and "tproj \<phi>' = tproj \<phi> @ tr"
proof -
  have "\<phi>' \<in> sem C P"
    using assms unfolding seq_IL_def by auto
  then obtain \<sigma>\<^sub>p tr0 tr where
    asm0: "(fst \<phi>', \<sigma>\<^sub>p, tr0) \<in> P"
          "big_step C \<sigma>\<^sub>p tr (fst (snd \<phi>'))"
          "snd (snd \<phi>') = tr0 @ tr"
    unfolding in_sem by auto
  let ?\<phi> = "(fst \<phi>', \<sigma>\<^sub>p, tr0)"
  show ?thesis
    by (rule that[of ?\<phi> tr])
       (use asm0 in \<open>simp_all add: lproj_def pproj_def tproj_def\<close>)
qed

definition par_IL where
  "par_IL P C Q \<longleftrightarrow> Q \<subseteq> par_sem C P"

theorem par_IL_encoding:
  "par_IL P C Q \<longleftrightarrow> \<Turnstile>\<^sub>P {under_approx P} C {under_approx Q}"
proof
  assume "\<Turnstile>\<^sub>P {under_approx P} C {under_approx Q}"
  then have "under_approx Q (par_sem C P)"
    by (simp add: par_hyper_hoare_triple_def under_approx_def)
  then show "par_IL P C Q"
    by (simp add: par_IL_def under_approx_def)
next
  assume "par_IL P C Q"
  then have Q_sub: "Q \<subseteq> par_sem C P"
    unfolding par_IL_def by simp
  show "\<Turnstile>\<^sub>P {under_approx P} C {under_approx Q}"
    unfolding par_hyper_hoare_triple_def
  proof (rule allI, rule impI)
    fix S
    assume "under_approx P S"
    then have "P \<subseteq> S"
      unfolding under_approx_def by simp
    then have "par_sem C P \<subseteq> par_sem C S"
      by (rule par_sem_monotonic)
    with Q_sub show "under_approx Q (par_sem C S)"
      unfolding under_approx_def by auto
  qed
qed

lemma par_IL_witness:
  assumes "par_IL P C Q"
      and "\<phi>' \<in> Q"
  obtains \<phi> where "\<phi> \<in> P"
      and "par_big_step C (ex2gstate \<phi>) (snd \<phi>') (ex2gstate (fst \<phi>'))"
      and "ex_logical_same \<phi> (fst \<phi>')"
proof -
  have "\<phi>' \<in> par_sem C P"
    using assms unfolding par_IL_def by auto
  then obtain \<phi> where
    asm0: "\<phi> \<in> P"
          "par_big_step C (ex2gstate \<phi>) (snd \<phi>') (ex2gstate (fst \<phi>'))"
          "ex_logical_same \<phi> (fst \<phi>')"
    unfolding in_par_sem by auto
  then show ?thesis
    using that by auto
qed

lemma skip_disproving_example:
  assumes "P S"
      and "\<not> Q S"
    shows "hybrid_disproving_triple P Skip (\<lambda>S. \<not> Q S)"
proof (rule hybrid_disproving_tripleI[where S=S])
  show "P S"
    using assms(1) .
  show "(\<lambda>S. \<not> Q S) (sem Skip S)"
    using assms(2) by (simp add: sem_skip)
qed

subsection \<open>A Timed Hybrid Incorrectness Example\<close>

definition empty_trace_hyperassertion ::
  "(('lvar, 'lval) exstate) hyperassertion" where
  "empty_trace_hyperassertion S \<longleftrightarrow> (\<forall>\<phi>\<in>S. tproj \<phi> = [])"

lemma wait_disproving_empty_trace_example:
  fixes \<sigma>\<^sub>l :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>p :: state
  shows "hybrid_disproving_triple
    (\<lambda>S. S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, [])})
    (Wait (\<lambda>_. 1))
    (\<lambda>S. \<not> empty_trace_hyperassertion S)"
proof -
  let ?S = "{(\<sigma>\<^sub>l, \<sigma>\<^sub>p, [])}"
  let ?tr = "[WaitBlk 1 (\<lambda>_. State \<sigma>\<^sub>p) ({}, {})]"
  let ?\<phi>' = "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, ?tr)"
  have wait_step: "big_step (Wait (\<lambda>_. 1)) \<sigma>\<^sub>p ?tr \<sigma>\<^sub>p"
    by (rule waitB1) simp
  have phi_in: "?\<phi>' \<in> sem (Wait (\<lambda>_. 1)) ?S"
    using wait_step by (auto simp add: in_sem)
  have "\<exists>\<phi>\<in>sem (Wait (\<lambda>_. 1)) ?S. tproj \<phi> \<noteq> []"
    by (rule bexI[of _ ?\<phi>'])
       (use phi_in in \<open>simp_all add: tproj_def\<close>)
  then have "\<not> empty_trace_hyperassertion (sem (Wait (\<lambda>_. 1)) ?S)"
    unfolding empty_trace_hyperassertion_def by blast
  then show ?thesis
    unfolding hybrid_disproving_triple_def by auto
qed

lemma wait_refutes_empty_trace_hht_example:
  fixes \<sigma>\<^sub>l :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>p :: state
  shows "\<not> \<Turnstile>
    {(\<lambda>S. S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, [])})}
    (Wait (\<lambda>_. 1))
    {empty_trace_hyperassertion}"
  using wait_disproving_empty_trace_example[of \<sigma>\<^sub>l \<sigma>\<^sub>p]
  by (simp add: hybrid_disproving_triple_iff_not_hht)

subsection \<open>A Concurrent Timed Incorrectness Example\<close>

definition par_empty_trace_hyperassertion ::
  "(('lvar, 'lval) exgstate \<times> trace) hyperassertion" where
  "par_empty_trace_hyperassertion S \<longleftrightarrow> (\<forall>\<phi>\<in>S. snd \<phi> = [])"

lemma par_wait_disproving_empty_trace_example:
  fixes \<sigma>\<^sub>l\<^sub>1 :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>l\<^sub>2 :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>p\<^sub>1 :: state
    and \<sigma>\<^sub>p\<^sub>2 :: state
  shows "par_hybrid_disproving_triple
    (\<lambda>S. S = {ExParState (ExState (\<sigma>\<^sub>l\<^sub>1, \<sigma>\<^sub>p\<^sub>1)) (ExState (\<sigma>\<^sub>l\<^sub>2, \<sigma>\<^sub>p\<^sub>2))})
    (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1))))
    (\<lambda>S. \<not> par_empty_trace_hyperassertion S)"
proof -
  let ?s1 = "ExState (\<sigma>\<^sub>l\<^sub>1, \<sigma>\<^sub>p\<^sub>1)"
  let ?s2 = "ExState (\<sigma>\<^sub>l\<^sub>2, \<sigma>\<^sub>p\<^sub>2)"
  let ?s = "ExParState ?s1 ?s2"
  let ?S = "{?s}"
  let ?tr1 = "[WaitBlk 1 (\<lambda>_. State \<sigma>\<^sub>p\<^sub>1) ({}, {})]"
  let ?tr2 = "[WaitBlk 1 (\<lambda>_. State \<sigma>\<^sub>p\<^sub>2) ({}, {})]"
  let ?tr = "[WaitBlk 1 (\<lambda>_. ParState (State \<sigma>\<^sub>p\<^sub>1) (State \<sigma>\<^sub>p\<^sub>2)) ({}, {})]"
  have step1: "par_big_step (Single (Wait (\<lambda>_. 1))) (State \<sigma>\<^sub>p\<^sub>1) ?tr1 (State \<sigma>\<^sub>p\<^sub>1)"
    by (rule SingleB, rule waitB1, simp)
  have step2: "par_big_step (Single (Wait (\<lambda>_. 1))) (State \<sigma>\<^sub>p\<^sub>2) ?tr2 (State \<sigma>\<^sub>p\<^sub>2)"
    by (rule SingleB, rule waitB1, simp)
  have combined: "combine_blocks {} ?tr1 ?tr2 ?tr"
  proof -
    have "combine_blocks {} [] [] []"
      by (rule combine_blocks_empty)
    then show ?thesis
      by (rule combine_blocks_wait1) simp_all
  qed
  have par_step:
    "par_big_step
      (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1))))
      (ex2gstate ?s) ?tr (ex2gstate ?s)"
    using ParallelB[OF step1 step2 combined] by simp
  have phi_in:
    "(?s, ?tr) \<in> par_sem
      (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1)))) ?S"
    using par_step ex_logical_same_refl
    by (auto simp add: in_par_sem)
  have "\<exists>\<phi>\<in>par_sem
      (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1)))) ?S.
      snd \<phi> \<noteq> []"
    by (rule bexI[of _ "(?s, ?tr)"])
       (use phi_in in simp_all)
  then have "\<not> par_empty_trace_hyperassertion
      (par_sem (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1)))) ?S)"
    unfolding par_empty_trace_hyperassertion_def by blast
  then show ?thesis
    unfolding par_hybrid_disproving_triple_def by auto
qed

lemma par_wait_refutes_empty_trace_hht_example:
  fixes \<sigma>\<^sub>l\<^sub>1 :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>l\<^sub>2 :: "'lvar \<Rightarrow> 'lval"
    and \<sigma>\<^sub>p\<^sub>1 :: state
    and \<sigma>\<^sub>p\<^sub>2 :: state
  shows "\<not> \<Turnstile>\<^sub>P
    {(\<lambda>S. S = {ExParState (ExState (\<sigma>\<^sub>l\<^sub>1, \<sigma>\<^sub>p\<^sub>1)) (ExState (\<sigma>\<^sub>l\<^sub>2, \<sigma>\<^sub>p\<^sub>2))})}
    (Parallel (Single (Wait (\<lambda>_. 1))) {} (Single (Wait (\<lambda>_. 1))))
    {par_empty_trace_hyperassertion}"
  using par_wait_disproving_empty_trace_example[of \<sigma>\<^sub>l\<^sub>1 \<sigma>\<^sub>p\<^sub>1 \<sigma>\<^sub>l\<^sub>2 \<sigma>\<^sub>p\<^sub>2]
  by (simp add: par_hybrid_disproving_triple_iff_not_hht)

end
