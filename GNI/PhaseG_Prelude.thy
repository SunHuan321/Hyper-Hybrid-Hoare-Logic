theory PhaseG_Prelude
  imports H3L_Semantics.Extended
begin

section \<open>Self-contained prelude for Phase G development\<close>

text \<open>
\<^bold>\<open>Purpose.\<close>  Phase G (GNI) is developed against the \<^emph>\<open>existing\<close>
\<^session>\<open>H3L_Semantics\<close> heap only, so that progress does not depend on the
still-unbuilt H3L_Core session.  Everything below is copied verbatim from
\<^theory_text>\<open>Core.Logic\<close> and \<^theory_text>\<open>HybridLoops\<close>; when Core is
healthy again, this prelude is replaced by those imports and the Phase G
proofs are unchanged.
\<close>

subsection \<open>Hyper assertions and triples (from \<^theory_text>\<open>Logic\<close>)\<close>

type_synonym 'a hyperassertion = "('a set \<Rightarrow> bool)"

definition conj where
  "conj P Q S \<longleftrightarrow> P S \<and> Q S"

definition hyper_hoare_triple ("\<Turnstile> {_} _ {_}" [51,0,0] 81) where
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (sem C S))"

lemma hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem C S)"
  shows "\<Turnstile> {P} C {Q}"
  using assms by (simp add: hyper_hoare_triple_def)

lemma hyper_hoare_tripleE:
  assumes "\<Turnstile> {P} C {Q}"
      and "P S"
  shows "Q (sem C S)"
  using assms(1) assms(2) hyper_hoare_triple_def
  by metis

lemma seq_rule:
  assumes "\<Turnstile> {P} C1 {R}"
    and "\<Turnstile> {R} C2 {Q}"
  shows "\<Turnstile> {P} Seq C1 C2 {Q}"
  using assms(1) assms(2) hyper_hoare_triple_def sem_seq
  by metis

subsection \<open>Guarded control flow (from \<^theory_text>\<open>HybridLoops\<close>)\<close>

definition lnot :: "fform \<Rightarrow> fform" where
  "lnot b \<sigma> \<longleftrightarrow> \<not> b \<sigma>"

definition while_cond :: "fform \<Rightarrow> proc \<Rightarrow> proc" where
  "while_cond b C = (Rep (Assume b; C)); Assume (lnot b)"

definition low_exp where
  "low_exp b S \<longleftrightarrow> (\<forall>\<phi>\<in>S. \<forall>\<phi>'\<in>S. b (pproj \<phi>) = b (pproj \<phi>'))"

definition holds_forall where
  "holds_forall b S \<longleftrightarrow> (\<forall>\<phi>\<in>S. b (pproj \<phi>))"

lemma holds_forall_empty:
  "holds_forall b {}"
  by (simp add: holds_forall_def)

lemma sem_assume_low_exp:
  assumes "holds_forall b S"
  shows "sem (Assume b) S = S"
    and "sem (Assume (lnot b)) S = {}"
  using assms
  by (fastforce simp add: sem_assume holds_forall_def lnot_def pproj_def)+

lemma sem_empty [simp]:
  "sem C {} = {}"
  by (auto simp add: sem_def)

lemma sem_assume_low_exp_seq:
  assumes "holds_forall b S"
  shows "sem (Assume b; C) S = sem C S"
    and "sem (Assume (lnot b); C) S = {}"
  using assms by (simp_all add: sem_assume_low_exp sem_seq)

end
