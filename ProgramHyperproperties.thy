theory ProgramHyperproperties
  imports Logic
begin

type_synonym progran_hyperproperty = "(gstate \<times> trace \<times> gstate) set \<Rightarrow> bool"

definition set_of_traces where 
  "set_of_traces C = {(s, l, s') |s s' l. par_big_step C s l s'}"

definition hypersat :: "pproc \<Rightarrow> progran_hyperproperty \<Rightarrow> bool" where
  "hypersat C H \<longleftrightarrow> H {(s, l, s') |s l s'. par_big_step C s l s'}"

theorem proving_hyperproperties:
  "\<exists>P Q. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile>\<^sub>P {P} C {Q})"
proof-
  let ?P = "\<lambda>S. S = {s :: gstate |s. True}"
  let ?Q = "\<lambda>S. H {(s, l ,s') |s s' l. (s', l) \<in> S}"

  have "\<And>C. hypersat C H \<longleftrightarrow> \<Turnstile>\<^sub>P {?P} C {?Q}"
  proof
    fix C
    assume "hypersat C H"
    show "\<Turnstile>\<^sub>P {?P} C {?Q}"
    proof (rule par_hyper_hoare_tripleI)

        

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







