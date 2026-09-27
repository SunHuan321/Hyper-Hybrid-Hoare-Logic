theory HybridHyperpropertyClasses
  imports H3L_Core.ProgramHyperproperties HybridDisproving
begin

subsection \<open>Trace-Aware Hyperproperty Classes\<close>

type_synonym hybrid_execution = "gstate \<times> trace \<times> gstate"
type_synonym hybrid_hyperproperty = "hybrid_execution hyperassertion"

definition final_state_lift where
  "final_state_lift H S \<longleftrightarrow> H {(s, s') |s tr s'. (s, tr, s') \<in> S}"

definition trace_projection_lift where
  "trace_projection_lift H S \<longleftrightarrow> H {tr |s tr s'. (s, tr, s') \<in> S}"

lemma hypersat_unfold:
  "hypersat C H \<longleftrightarrow> H (set_of_traces C)"
proof -
  have "{(s, l, s') |s l s'. par_big_step C s l s'} = set_of_traces C"
    unfolding set_of_traces_def by blast
  then show ?thesis
    by (simp add: hypersat_def)
qed

definition max_k where
  "max_k k S \<longleftrightarrow> finite S \<and> card S \<le> k"

definition hypersafety where
  "hypersafety P \<longleftrightarrow> (\<forall>S. \<not> P S \<longrightarrow> (\<forall>S'. S \<subseteq> S' \<longrightarrow> \<not> P S'))"

definition k_hypersafety where
  "k_hypersafety k P \<longleftrightarrow>
    (\<forall>S. \<not> P S \<longrightarrow>
      (\<exists>S'. S' \<subseteq> S \<and> max_k k S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> P S'')))"

definition hyperliveness where
  "hyperliveness P \<longleftrightarrow> (\<forall>S. \<exists>S'. S \<subseteq> S' \<and> P S')"

lemma k_hypersafetyI:
  assumes "\<And>S. \<not> P S \<Longrightarrow> \<exists>S'. S' \<subseteq> S \<and> max_k k S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> P S'')"
  shows "k_hypersafety k P"
  by (simp add: assms k_hypersafety_def)

lemma hypersafetyI:
  assumes "\<And>S S'. \<not> P S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> \<not> P S'"
  shows "hypersafety P"
  by (metis assms hypersafety_def)

lemma hyperlivenessI:
  assumes "\<And>S. \<exists>S'. S \<subseteq> S' \<and> P S'"
  shows "hyperliveness P"
  using assms hyperliveness_def by blast

lemma k_hypersafe_is_hypersafe:
  assumes "k_hypersafety k P"
  shows "hypersafety P"
  by (metis (full_types) assms dual_order.trans hypersafety_def k_hypersafety_def)

lemma one_safety_equiv:
  assumes "sat H"
  shows "k_hypersafety 1 H \<longleftrightarrow> (\<exists>P. \<forall>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. P \<tau>))"
proof
  assume "\<exists>P. \<forall>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. P \<tau>)"
  then obtain P where asm0: "\<And>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. P \<tau>)"
    by auto
  show "k_hypersafety 1 H"
  proof (rule k_hypersafetyI)
    fix S
    assume "\<not> H S"
    then obtain \<tau> where "\<tau> \<in> S" "\<not> P \<tau>"
      using asm0 by blast
    let ?S = "{\<tau>}"
    have "?S \<subseteq> S \<and> max_k 1 ?S \<and> (\<forall>S''. ?S \<subseteq> S'' \<longrightarrow> \<not> H S'')"
      using \<open>\<not> P \<tau>\<close> \<open>\<tau> \<in> S\<close> asm0 max_k_def by fastforce
    then show "\<exists>S'\<subseteq>S. max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S'')"
      by blast
  qed
next
  assume asm0: "k_hypersafety 1 H"
  let ?P = "\<lambda>\<tau>. H {\<tau>}"
  have "\<And>S. H S \<longleftrightarrow> (\<forall>\<tau> \<in> S. ?P \<tau>)"
  proof
    fix S
    assume "H S"
    then show "\<forall>\<tau>\<in>S. ?P \<tau>"
      using asm0 hypersafety_def k_hypersafe_is_hypersafe by auto
  next
    fix S
    assume asm1: "\<forall>\<tau>\<in>S. ?P \<tau>"
    show "H S"
    proof (rule ccontr)
      assume "\<not> H S"
      then obtain S' where S'_def: "S' \<subseteq> S" "max_k 1 S'" "\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> H S''"
        by (metis asm0 k_hypersafety_def)
      show False
      proof (cases "S' = {}")
        case True
        then show ?thesis
          by (metis S'_def(3) assms empty_subsetI sat_def)
      next
        case False
        then obtain \<tau> where "\<tau> \<in> S'"
          by blast
        have "finite S'" "card S' \<le> 1"
          using S'_def(2) by (auto simp add: max_k_def)
        moreover have "card S' > 0"
          using False calculation(1) by (simp add: card_gt_0_iff)
        ultimately have "card S' = 1"
          by simp
        then have "S' = {\<tau>}"
          using \<open>\<tau> \<in> S'\<close> card_1_singletonE by auto
        then show ?thesis
          using S'_def asm1 by fastforce
      qed
    qed
  qed
  then show "\<exists>P. \<forall>S. H S \<longleftrightarrow> (\<forall>\<tau>\<in>S. P \<tau>)"
    by blast
qed

definition hoarify where
  "hoarify P Q S \<longleftrightarrow> (\<forall>p \<in> S. fst p \<in> P \<longrightarrow> snd p \<in> Q)"

lemma hoarify_hypersafety:
  "hypersafety (hoarify P Q)"
  by (metis (no_types, opaque_lifting) hoarify_def hypersafetyI subsetD)

theorem hypersafety_1_hoare_logic:
  "k_hypersafety 1 (hoarify P Q)"
proof (rule k_hypersafetyI)
  fix S
  assume "\<not> hoarify P Q S"
  then obtain \<tau> where "\<tau> \<in> S" "fst \<tau> \<in> P" "snd \<tau> \<notin> Q"
    using hoarify_def by blast
  let ?S = "{\<tau>}"
  have "?S \<subseteq> S \<and> max_k 1 ?S \<and> (\<forall>S''. ?S \<subseteq> S'' \<longrightarrow> \<not> hoarify P Q S'')"
    using \<open>\<tau> \<in> S\<close> \<open>fst \<tau> \<in> P\<close> \<open>snd \<tau> \<notin> Q\<close>
    by (auto simp add: hoarify_def max_k_def)
  then show "\<exists>S'\<subseteq>S. max_k 1 S' \<and> (\<forall>S''. S' \<subseteq> S'' \<longrightarrow> \<not> hoarify P Q S'')"
    by meson
qed

definition incorrectnessify where
  "incorrectnessify P Q S \<longleftrightarrow> (\<forall>\<sigma>' \<in> Q. \<exists>\<sigma> \<in> P. (\<sigma>, \<sigma>') \<in> S)"

lemma incorrectnessify_liveness:
  assumes "P \<noteq> {}"
  shows "hyperliveness (incorrectnessify P Q)"
proof (rule hyperlivenessI)
  fix S
  obtain \<sigma> where "\<sigma> \<in> P"
    using assms by blast
  let ?S = "S \<union> {(\<sigma>, \<sigma>') |\<sigma>'. \<sigma>' \<in> Q}"
  have "incorrectnessify P Q ?S"
    using \<open>\<sigma> \<in> P\<close> incorrectnessify_def by force
  then show "\<exists>S'. S \<subseteq> S' \<and> incorrectnessify P Q S'"
    using sup.cobounded1 by blast
qed

definition real_incorrectnessify where
  "real_incorrectnessify P Q S \<longleftrightarrow> (\<forall>\<sigma> \<in> P. \<exists>\<sigma>' \<in> Q. (\<sigma>, \<sigma>') \<in> S)"

lemma real_incorrectnessify_liveness:
  assumes "Q \<noteq> {}"
  shows "hyperliveness (real_incorrectnessify P Q)"
  by (metis UNIV_I assms equals0I hyperliveness_def real_incorrectnessify_def subsetI)

definition gni_hyperassertion :: "'n \<Rightarrow> 'n \<Rightarrow> ('n \<Rightarrow> 'v) hyperassertion" where
  "gni_hyperassertion h l S \<longleftrightarrow> (\<forall>\<sigma> \<in> S. \<forall>v. \<exists>\<sigma>' \<in> S. \<sigma>' h = v \<and> \<sigma> l = \<sigma>' l)"

end
