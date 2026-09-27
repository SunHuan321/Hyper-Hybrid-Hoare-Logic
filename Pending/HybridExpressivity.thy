theory HybridExpressivity
  imports HybridHyperpropertyClasses
begin

subsection \<open>Sequential Hybrid Executions\<close>

definition seq_step where
  "seq_step C \<phi> \<phi>' \<longleftrightarrow>
    lproj \<phi> = lproj \<phi>' \<and>
    (\<exists>tr. big_step C (pproj \<phi>) tr (pproj \<phi>') \<and> tproj \<phi>' = tproj \<phi> @ tr)"

lemma in_sem_iff_seq_step:
  "\<phi>' \<in> sem C S \<longleftrightarrow> (\<exists>\<phi>\<in>S. seq_step C \<phi> \<phi>')"
  unfolding sem_def seq_step_def lproj_def pproj_def tproj_def
  by force

lemma seq_step_lupdate:
  assumes "seq_step C \<phi> \<phi>'"
  shows "seq_step C ((lproj \<phi>)(x := v), pproj \<phi>, tproj \<phi>)
                   ((lproj \<phi>')(x := v), pproj \<phi>', tproj \<phi>')"
  using assms
  unfolding seq_step_def lproj_def pproj_def tproj_def by auto

subsection \<open>Cartesian Hoare Logic\<close>

definition k_sem where
  "k_sem C states states' \<longleftrightarrow> (\<forall>i. seq_step C (states i) (states' i))"

lemma k_semI:
  assumes "\<And>i. seq_step C (states i) (states' i)"
  shows "k_sem C states states'"
  by (simp add: assms k_sem_def)

lemma k_semE:
  assumes "k_sem C states states'"
  shows "seq_step C (states i) (states' i)"
  using assms k_sem_def by fastforce

definition CHL where
  "CHL P C Q \<longleftrightarrow> (\<forall>states. states \<in> P \<longrightarrow> (\<forall>states'. k_sem C states states' \<longrightarrow> states' \<in> Q))"

lemma CHLI:
  assumes "\<And>states states'. states \<in> P \<Longrightarrow> k_sem C states states' \<Longrightarrow> states' \<in> Q"
  shows "CHL P C Q"
  by (simp add: assms CHL_def)

lemma CHLE:
  assumes "CHL P C Q"
      and "states \<in> P"
      and "k_sem C states states'"
    shows "states' \<in> Q"
  using assms CHL_def by blast

definition differ_only_by where
  "differ_only_by a b x \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> a y = b y)"

lemma diff_by_update:
  "differ_only_by (a(x := v)) a x"
  by (simp add: differ_only_by_def)

lemma diff_by_update_right:
  "differ_only_by a (a(x := v)) x"
  by (simp add: differ_only_by_def)

definition not_free_var_of where
  "not_free_var_of P x \<longleftrightarrow>
    (\<forall>states states'. states \<in> P \<and>
      (\<forall>i. differ_only_by (lproj (states i)) (lproj (states' i)) x \<and>
           pproj (states i) = pproj (states' i) \<and>
           tproj (states i) = tproj (states' i))
      \<longrightarrow> states' \<in> P)"

lemma not_free_var_ofE:
  assumes "not_free_var_of P x"
      and "states \<in> P"
      and "\<And>i. differ_only_by (lproj (states i)) (lproj (states' i)) x"
      and "\<And>i. pproj (states i) = pproj (states' i)"
      and "\<And>i. tproj (states i) = tproj (states' i)"
    shows "states' \<in> P"
  using assms not_free_var_of_def by metis

definition encode_CHL where
  "encode_CHL from_index x P S \<longleftrightarrow>
    (\<forall>states. (\<forall>i. states i \<in> S \<and> lproj (states i) x = from_index i) \<longrightarrow> states \<in> P)"

lemma encode_CHLI:
  assumes "\<And>states. (\<forall>i. states i \<in> S \<and> lproj (states i) x = from_index i) \<Longrightarrow> states \<in> P"
  shows "encode_CHL from_index x P S"
  using assms encode_CHL_def by blast

lemma encode_CHLE:
  assumes "encode_CHL from_index x P S"
      and "\<And>i. states i \<in> S"
      and "\<And>i. lproj (states i) x = from_index i"
    shows "states \<in> P"
  using assms encode_CHL_def by blast

theorem encoding_CHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_index"
  shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_index x P} C {encode_CHL from_index x Q}"
proof
  assume chl: "CHL P C Q"
  show "\<Turnstile> {encode_CHL from_index x P} C {encode_CHL from_index x Q}"
  proof (rule hyper_hoare_tripleI)
    fix S
    assume encP: "encode_CHL from_index x P S"
    show "encode_CHL from_index x Q (sem C S)"
    proof (rule encode_CHLI)
      fix states'
      assume asm: "\<forall>i. states' i \<in> sem C S \<and> lproj (states' i) x = from_index i"
      let ?states = "\<lambda>i. SOME \<phi>. \<phi> \<in> S \<and> seq_step C \<phi> (states' i)"
      have pre: "\<And>i. ?states i \<in> S \<and> seq_step C (?states i) (states' i)"
      proof -
        fix i
        have "\<exists>\<phi>. \<phi> \<in> S \<and> seq_step C \<phi> (states' i)"
          using asm in_sem_iff_seq_step by blast
        then show "?states i \<in> S \<and> seq_step C (?states i) (states' i)"
          by (rule someI_ex)
      qed
      have "?states \<in> P"
      proof (rule encode_CHLE[OF encP])
        fix i
        show "?states i \<in> S"
          using pre by blast
        show "lproj (?states i) x = from_index i"
          using asm pre[of i] unfolding seq_step_def by auto
      qed
      moreover have "k_sem C ?states states'"
        using pre by (simp add: k_sem_def)
      ultimately show "states' \<in> Q"
        using CHLE chl by blast
    qed
  qed
next
  assume hht: "\<Turnstile> {encode_CHL from_index x P} C {encode_CHL from_index x Q}"
  show "CHL P C Q"
  proof (rule CHLI)
    fix states states'
    assume asm: "states \<in> P" "k_sem C states states'"
    let ?states = "\<lambda>i. ((lproj (states i))(x := from_index i), pproj (states i), tproj (states i))"
    let ?states' = "\<lambda>i. ((lproj (states' i))(x := from_index i), pproj (states' i), tproj (states' i))"
    let ?S = "range ?states"
    have encP: "encode_CHL from_index x P ?S"
    proof (rule encode_CHLI)
      fix f
      assume f_def: "\<forall>i. f i \<in> ?S \<and> lproj (f i) x = from_index i"
      have "f = ?states"
      proof (rule ext)
        fix i
        obtain j where j_def: "f i = ?states j"
          using f_def by blast
        then have "lproj (f i) x = from_index j"
          by (simp add: lproj_def)
        then have "from_index j = from_index i"
          using f_def by simp
        then have "j = i"
          using assms(3) injective_def by blast
        then show "f i = ?states i"
          using j_def by simp
      qed
      moreover have "?states \<in> P"
      proof (rule not_free_var_ofE[OF assms(1) asm(1)])
        fix i
        show "differ_only_by (lproj (states i)) (lproj (?states i)) x"
          by (simp add: differ_only_by_def lproj_def)
        show "pproj (states i) = pproj (?states i)"
          by (simp add: pproj_def)
        show "tproj (states i) = tproj (?states i)"
          by (simp add: tproj_def)
      qed
      ultimately show "f \<in> P"
        by simp
    qed
    have encQ: "encode_CHL from_index x Q (sem C ?S)"
      using hht encP by (rule hyper_hoare_tripleE)
    have "?states' \<in> Q"
    proof (rule encode_CHLE[OF encQ])
      fix i
      have "seq_step C (?states i) (?states' i)"
        using k_semE[OF asm(2), of i] seq_step_lupdate by blast
      moreover have "?states i \<in> ?S"
        by simp
      ultimately show "?states' i \<in> sem C ?S"
        using in_sem_iff_seq_step by blast
      show "lproj (?states' i) x = from_index i"
        by (simp add: lproj_def)
    qed
    then show "states' \<in> Q"
    proof (rule not_free_var_ofE[OF assms(2)])
      fix i
      show "differ_only_by (lproj (?states' i)) (lproj (states' i)) x"
        by (simp add: diff_by_update lproj_def)
      show "pproj (?states' i) = pproj (states' i)"
        by (simp add: pproj_def)
      show "tproj (?states' i) = tproj (states' i)"
        by (simp add: tproj_def)
    qed
  qed
qed

subsection \<open>Forward Underapproximation\<close>

definition FU where
  "FU P C Q \<longleftrightarrow> (\<forall>\<phi> \<in> P. \<exists>\<phi>' \<in> Q. seq_step C \<phi> \<phi>')"

lemma FUI:
  assumes "\<And>\<phi>. \<phi> \<in> P \<Longrightarrow> \<exists>\<phi>' \<in> Q. seq_step C \<phi> \<phi>'"
  shows "FU P C Q"
  by (simp add: assms FU_def)

definition encode_FU where
  "encode_FU P S \<longleftrightarrow> P \<inter> S \<noteq> {}"

theorem encoding_FU:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}"
proof
  assume hht: "\<Turnstile> {encode_FU P} C {encode_FU Q}"
  show "FU P C Q"
  proof (rule FUI)
    fix \<phi>
    assume "\<phi> \<in> P"
    then have encP: "encode_FU P {\<phi>}"
      by (simp add: encode_FU_def)
    have "encode_FU Q (sem C {\<phi>})"
      using hht encP by (rule hyper_hoare_tripleE)
    then obtain \<phi>' where "\<phi>' \<in> Q" "\<phi>' \<in> sem C {\<phi>}"
      by (auto simp add: encode_FU_def)
    then show "\<exists>\<phi>'\<in>Q. seq_step C \<phi> \<phi>'"
      using in_sem_iff_seq_step by blast
  qed
next
  assume fu: "FU P C Q"
  show "\<Turnstile> {encode_FU P} C {encode_FU Q}"
  proof (rule hyper_hoare_tripleI)
    fix S
    assume "encode_FU P S"
    then obtain \<phi> where "\<phi> \<in> P" "\<phi> \<in> S"
      by (auto simp add: encode_FU_def)
    then obtain \<phi>' where "\<phi>' \<in> Q" "seq_step C \<phi> \<phi>'"
      using fu FU_def by blast
    then have "\<phi>' \<in> sem C S"
      using \<open>\<phi> \<in> S\<close> in_sem_iff_seq_step by blast
    then show "encode_FU Q (sem C S)"
      using \<open>\<phi>' \<in> Q\<close> by (auto simp add: encode_FU_def)
  qed
qed

subsection \<open>k-Incorrectness Logic / RIL\<close>

definition RIL where
  "RIL P C Q \<longleftrightarrow> (\<forall>states' \<in> Q. \<exists>states \<in> P. k_sem C states states')"

definition k_sem_image where
  "k_sem_image C P = {states'. \<exists>states \<in> P. k_sem C states states'}"

lemma RIL_iff_subset:
  "RIL P C Q \<longleftrightarrow> Q \<subseteq> k_sem_image C P"
  by (auto simp add: RIL_def k_sem_image_def)

text \<open>
The full HHL encodings for RIL/RFU/RUE require packing whole indexed executions into
logical variables and then proving trace-aware unpacking lemmas.  The definitions above
are the semantic target for that later encoding layer.
\<close>

end
