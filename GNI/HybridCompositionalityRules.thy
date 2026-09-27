theory HybridCompositionalityRules
  imports PhaseG_Prelude HybridLoopRules
begin

section \<open>Compositionality rules ported from HHL\<close>

text \<open>
Practical rules that let you reason at the assertion level without unfolding
sem/big_step.  Ported from HHL's \<^theory_text>\<open>Compositionality.thy\<close> and
\<^theory_text>\<open>Logic.thy\<close> to our extended states (logical state, program
state, trace).

The file was recreated after its contents were lost; the rules below are the
same ports as before:

  \<^item> \<^term>\<open>rule_Or\<close>, \<^term>\<open>rule_Forall\<close>, \<^term>\<open>rule_Exists\<close> --
    connective glue over indexed families of assertions;
  \<^item> \<^term>\<open>consequence_rule_comp\<close>, \<^term>\<open>skip_rule\<close>;
  \<^item> \<^term>\<open>rule_lframe_single\<close> -- HHL's logical frame rule: on our
    exstates it is easy, because \<^const>\<open>sem\<close> preserves the logical
    component of every extended state by construction;
  \<^item> \<^term>\<open>loop_exit\<close> -- a while whose guard is false everywhere
    immediately exits.
\<close>


subsection \<open>Disjunction, quantification, consequence\<close>

definition disj where
  "disj P Q S \<longleftrightarrow> (P S \<or> Q S)"

theorem rule_Or:
  assumes "\<Turnstile> {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
  shows "\<Turnstile> {disj P P'} C {disj Q Q'}"
  using assms unfolding disj_def hyper_hoare_triple_def by blast

definition hforall where
  "hforall P S \<longleftrightarrow> (\<forall>x. P x S)"

theorem rule_Forall:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {hforall P} C {hforall Q}"
  using assms unfolding hforall_def hyper_hoare_triple_def by blast

definition hexists where
  "hexists P S \<longleftrightarrow> (\<exists>x. P x S)"

theorem rule_Exists:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {hexists P} C {hexists Q}"
  using assms unfolding hexists_def hyper_hoare_triple_def by blast

definition entails where
  "entails P Q \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q S)"

theorem consequence_rule_comp:
  assumes "entails P P'"
      and "entails Q' Q"
      and "\<Turnstile> {P'} C {Q'}"
  shows "\<Turnstile> {P} C {Q}"
  using assms unfolding entails_def hyper_hoare_triple_def by blast

theorem skip_rule:
  "\<Turnstile> {P} Skip {P}"
  unfolding hyper_hoare_triple_def by (simp add: sem_skip)


subsection \<open>Logical frame rule (HHL port)\<close>

text \<open>
Every state of \<^term>\<open>sem C S\<close> inherits its logical component from some
state of \<^term>\<open>S\<close>; hence any assertion that talks only about logical
states is invariant under any command.
\<close>

lemma sem_lproj_src:
  assumes "\<phi> \<in> sem C S"
  shows "\<exists>src \<in> S. lproj \<phi> = lproj src"
proof -
  from assms obtain \<sigma>\<^sub>p l l' where src: "(fst \<phi>, \<sigma>\<^sub>p, l) \<in> S"
    by (auto simp: in_sem)
  show ?thesis
    unfolding lproj_def
    by (rule_tac x = "(fst \<phi>, \<sigma>\<^sub>p, l)" in bexI, simp, fact src)
qed

theorem rule_lframe_single:
  fixes P :: "('lvar \<Rightarrow> 'lval) \<Rightarrow> bool"
  shows "hyper_hoare_triple (\<lambda>S. \<forall>\<phi>\<in>S. P (lproj \<phi>)) C
              (\<lambda>S. \<forall>\<phi>\<in>S. P (lproj \<phi>))"
proof (rule hyper_hoare_tripleI)
  fix S assume a0: "\<forall>\<phi>\<in>S. P (lproj \<phi>)"
  show "\<forall>\<phi>'\<in>sem C S. P (lproj \<phi>')"
  proof
    fix \<phi>' assume m: "\<phi>' \<in> sem C S"
    from sem_lproj_src [OF m] obtain src where
      s: "src \<in> S" "lproj \<phi>' = lproj src" by blast
    with a0 show "P (lproj \<phi>')" by simp
  qed
qed


subsection \<open>Loop exit rule\<close>

lemma lnot_lnot [simp]:
  "lnot (lnot b) = b"
  by (rule ext) (simp add: lnot_def)

text \<open>
If \<^term>\<open>P\<close> implies that the guard is false on all states, the loop body
is never entered and the while immediately exits.
\<close>

theorem loop_exit:
  assumes hb: "\<And>S. P S \<Longrightarrow> holds_forall (lnot b) S"
  shows "\<Turnstile> {P} (while_cond b C) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume a: "P S"
  then have nb: "holds_forall (lnot b) S" by (rule hb)
  have lb: "sem (Assume b) S = {}"
    using nb sem_assume_low_exp(2) [of "lnot b" S] by simp
  have f0: "sem (Assume b; C) S = {}"
    using lb by (simp add: sem_seq)
  have it0: "iterate_sem 0 (Assume b; C) S = S" by simp
  have its: "\<And>n. iterate_sem (Suc n) (Assume b; C) S = {}"
  proof -
    fix n
    show "iterate_sem (Suc n) (Assume b; C) S = {}"
    proof (induct n)
      case 0 show ?case using f0 by simp
    next
      case (Suc n) thus ?case by simp
    qed
  qed
  have rp: "sem (Rep (Assume b; C)) S = S"
  proof -
    have "sem (Rep (Assume b; C)) S = (\<Union>n. iterate_sem n (Assume b; C) S)"
      by (rule sem_while)
    also have "\<dots> = S"
    proof
      show "(\<Union>n. iterate_sem n (Assume b; C) S) \<subseteq> S"
      proof
        fix x assume xu: "x \<in> (\<Union>n. iterate_sem n (Assume b; C) S)"
        then obtain n where xn: "x \<in> iterate_sem n (Assume b; C) S" by blast
        show "x \<in> S"
        proof (cases n)
          case 0
          then have "x \<in> iterate_sem 0 (Assume b; C) S" using xn by simp
          with it0 show ?thesis by simp
        next
          case (Suc k)
          then have "x \<in> iterate_sem (Suc k) (Assume b; C) S" using xn by simp
          with its show ?thesis by simp
        qed
      qed
    next
      show "S \<subseteq> (\<Union>n. iterate_sem n (Assume b; C) S)"
      proof
        fix x assume "x \<in> S"
        with it0 have "x \<in> iterate_sem 0 (Assume b; C) S" by simp
        then show "x \<in> (\<Union>n. iterate_sem n (Assume b; C) S)" by blast
      qed
    qed
    finally show ?thesis .
  qed
  have "sem (while_cond b C) S = sem (Assume (lnot b)) S"
    by (simp add: while_cond_def sem_seq rp)
  also have "\<dots> = S"
    using nb unfolding sem_assume holds_forall_def lnot_def pproj_def by auto
  finally show "P (sem (while_cond b C) S)" using a by simp
qed

end
