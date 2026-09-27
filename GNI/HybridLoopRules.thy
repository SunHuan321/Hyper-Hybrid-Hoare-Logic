theory HybridLoopRules
  imports PhaseG_Prelude
begin

section \<open>Loop and compositionality rule kit for Phase G (ported from HHL)\<close>

text \<open>
Rule kit for \<open>\<forall>\<exists>\<close>-shape reasoning (GNI, opacity), ported from Hyper
Hoare Logic's \<^theory_text>\<open>Compositionality.thy\<close> and \<^theory_text>\<open>Loops.thy\<close>:

  \<^item> \<^term>\<open>rule_And\<close>, \<^term>\<open>rule_BigUnion\<close> -- logical/connective glue;
  \<^item> \<^term>\<open>rule_linking\<close> -- HHL's key linking rule, on our exstates:
    from single-execution triples conclude set-level \<open>\<forall>\<phi>'\<close> triples;
  \<^item> \<^term>\<open>while_exists\<close> -- zero-round witness-existence loop rule
    for a state that already satisfies the exit guard;
  \<^item> \<^term>\<open>rep_invariant_param\<close> -- union-closure loop rule for
    \<open>\<forall>\<exists>\<close> invariants that are not per-state.

Skipped for now (documented in the plan): HHL's \<open>rule_LFilter\<close> and the
filter-commute machinery behind the fully general GNI-composition (Fig.~13
of HHL); a weaker observation-preserving composition is in
\<^theory_text>\<open>PhaseG_GNI\<close>.
\<close>


subsection \<open>Basic assertion combinators\<close>

definition in_set :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "in_set \<phi> S \<longleftrightarrow> \<phi> \<in> S"

definition not_empty :: "'a set \<Rightarrow> bool" where
  "not_empty S \<longleftrightarrow> S \<noteq> {}"

theorem rule_And:
  assumes "\<Turnstile> {P1} C {Q1}" "\<Turnstile> {P2} C {Q2}"
  shows "\<Turnstile> {conj P1 P2} C {conj Q1 Q2}"
proof (rule hyper_hoare_tripleI)
  fix S assume a: "conj P1 P2 S"
  then have p1: "P1 S" and p2: "P2 S" by (simp_all add: conj_def)
  from assms(1) p1 have "Q1 (sem C S)" by (rule hyper_hoare_tripleE)
  moreover from assms(2) p2 have "Q2 (sem C S)" by (rule hyper_hoare_tripleE)
  ultimately show "conj Q1 Q2 (sem C S)" by (simp add: conj_def)
qed

definition general_union :: "'a hyperassertion \<Rightarrow> 'a hyperassertion" where
  "general_union P S \<longleftrightarrow> (\<exists>F. S = \<Union> F \<and> (\<forall>S' \<in> F. P S'))"

lemma general_unionI:
  assumes "S = \<Union> F" "\<And>S'. S' \<in> F \<Longrightarrow> P S'"
  shows "general_union P S"
  using assms unfolding general_union_def by blast

theorem rule_BigUnion:
  assumes inv: "\<Turnstile> {P} C {P}"
  shows "\<Turnstile> {general_union P} C {general_union P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "general_union P S"
  then obtain F where S: "S = \<Union> F" and F: "\<forall>S' \<in> F. P S'"
    unfolding general_union_def by blast
  have eq: "sem C S = \<Union> {sem C S' |S'. S' \<in> F}"
  proof
    show "sem C S \<subseteq> \<Union> {sem C S' |S'. S' \<in> F}"
    proof
      fix \<phi> assume "\<phi> \<in> sem C S"
      then obtain \<sigma>\<^sub>p l l' where src: "(fst \<phi>, \<sigma>\<^sub>p, l) \<in> S"
        "big_step C \<sigma>\<^sub>p l' (fst (snd \<phi>))" "snd (snd \<phi>) = l @ l'"
        using in_sem [THEN iffD1] by blast
      then obtain S' where sinF: "S' \<in> F" and sinS': "(fst \<phi>, \<sigma>\<^sub>p, l) \<in> S'" using S by blast
      have memS': "\<phi> \<in> sem C S'"
        by (rule in_sem [THEN iffD2])
           (rule exI [where x = "\<sigma>\<^sub>p"], rule exI [where x = "l"], rule exI [where x = "l'"],
            simp add: sinS' src(2) src(3))
      show "\<phi> \<in> \<Union> {sem C S' |S'. S' \<in> F}"
        using sinF memS' by blast
    qed
    show "\<Union> {sem C S' |S'. S' \<in> F} \<subseteq> sem C S"
    proof (rule Union_least)
      fix X assume "X \<in> {sem C S' |S'. S' \<in> F}"
      then obtain S' where xin: "S' \<in> F" and XS': "X = sem C S'" by blast
      from xin have sub: "S' \<subseteq> S" using S by blast
      from sub have "sem C S' \<subseteq> sem C S" by (rule sem_monotonic)
      with XS' show "X \<subseteq> sem C S" by simp
    qed
  qed
  have memF: "\<forall>S'' \<in> {sem C S' |S'. S' \<in> F}. P S''"
  proof
    fix X assume "X \<in> {sem C S' |S'. S' \<in> F}"
    then obtain S' where xin: "S' \<in> F" and XS': "X = sem C S'" by blast
    from xin F have "P S'" by blast
    then have "P (sem C S')" by (rule hyper_hoare_tripleE [OF inv])
    with XS' show "P X" by simp
  qed
  show "general_union P (sem C S)"
  proof (rule general_unionI [where F = "{sem C S' |S'. S' \<in> F}"])
    show "sem C S = \<Union> {sem C S' |S'. S' \<in> F}" using eq .
    fix X assume "X \<in> {sem C S' |S'. S' \<in> F}"
    with memF show "P X" by blast
  qed
qed


subsection \<open>Linking rule (HHL port)\<close>

text \<open>A set-level postcondition follows by applying the source predicate to
 each contributing execution and checking the corresponding target in the
 complete output set.\<close>

theorem rule_linking:
  fixes P Q :: "('lvar, 'lval) exstate \<Rightarrow> ('lvar, 'lval) exstate set \<Rightarrow> bool"
    and C :: proc
  assumes step: "\<And>S sl sp tr0 sp' tr1.
      (sl, sp, tr0) \<in> S \<Longrightarrow> P (sl, sp, tr0) S \<Longrightarrow>
      big_step C sp tr1 sp' \<Longrightarrow>
      Q (sl, sp', tr0 @ tr1) (sem C S)"
  shows "hyper_hoare_triple (\<lambda>S. \<forall>\<phi>\<in>S. P \<phi> S) C
      (\<lambda>S. \<forall>\<phi>\<in>S. Q \<phi> S)"
proof (rule hyper_hoare_tripleI)
  fix S assume pre: "\<forall>\<phi>\<in>S. P \<phi> S"
  show "\<forall>\<phi>\<in>sem C S. Q \<phi> (sem C S)"
  proof (rule ballI)
    fix \<phi> assume mem: "\<phi> \<in> sem C S"
    then obtain sp tr0 tr1 where src: "(fst \<phi>, sp, tr0) \<in> S"
      "big_step C sp tr1 (fst (snd \<phi>))" "snd (snd \<phi>) = tr0 @ tr1"
      using in_sem [THEN iffD1] by blast
    have psrc: "P (fst \<phi>, sp, tr0) S" using pre src(1) by blast
    have q: "Q (fst \<phi>, fst (snd \<phi>), tr0 @ tr1) (sem C S)"
      by (rule step[OF src(1) psrc src(2)])
    have eq: "(fst \<phi>, fst (snd \<phi>), tr0 @ tr1) = \<phi>"
      using src(3) by (metis prod.collapse)
    from q show "Q \<phi> (sem C S)" using eq by simp
  qed
qed

subsection \<open>Witness-existence loop rule (HHL port)\<close>

lemma false_state_in_while_cond:
  assumes "\<phi> \<in> S" "\<not> b (pproj \<phi>)"
  shows "\<phi> \<in> sem (while_cond b C) S"
proof -
  have z: "\<phi> \<in> iterate_sem 0 (Assume b; C) S" using assms(1) by simp
  then have "sem (Rep (Assume b; C)) S = (\<Union>n. iterate_sem n (Assume b; C) S)"
    by (simp add: sem_while)
  with z have r: "\<phi> \<in> sem (Rep (Assume b; C)) S" by blast
  obtain \<sigma>\<^sub>l \<sigma>\<^sub>p l where pd: "\<phi> = (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l)"
    by (metis prod.collapse surjective_pairing)
  have nb: "\<not> b (pproj (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l))" using assms(2) by (simp add: pd)
  have fin: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> sem (Assume (lnot b)) (sem (Rep (Assume b; C)) S)"
    using r[unfolded pd] nb by (simp add: sem_assume lnot_def pproj_def)
  then show ?thesis
    unfolding while_cond_def pd by (simp add: sem_seq)
qed

theorem while_exists:
  fixes P Q :: "('lvar, 'lval) exstate \<Rightarrow> ('lvar, 'lval) exstate set \<Rightarrow> bool"
    and b :: fform and C :: proc
  assumes per_witness: "\<And>\<phi>. hyper_hoare_triple (P \<phi>) (while_cond b C) (Q \<phi>)"
  shows "hyper_hoare_triple
    (\<lambda>S. \<exists>\<phi>\<in>S. \<not> b (pproj \<phi>) \<and> P \<phi> S)
    (while_cond b C)
    (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S)"
proof (rule hyper_hoare_tripleI)
  fix S assume pre: "\<exists>\<phi>\<in>S. \<not> b (pproj \<phi>) \<and> P \<phi> S"
  then obtain \<phi> where mem: "\<phi> \<in> S" and exit: "\<not> b (pproj \<phi>)"
    and p: "P \<phi> S" by blast
  have q: "Q \<phi> (sem (while_cond b C) S)"
    by (rule hyper_hoare_tripleE[OF per_witness p])
  have "\<phi> \<in> sem (while_cond b C) S"
    using mem exit by (metis false_state_in_while_cond)
  with q show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
    by blast
qed

subsection \<open>Well-founded exit witness\<close>

lemma iterate_sem_mono:
  assumes sub: "A \<subseteq> B"
  shows "iterate_sem n C A \<subseteq> iterate_sem n C B"
proof (induct n)
  case 0
  then show ?case using sub by simp
next
  case (Suc n)
  have "sem C (iterate_sem n C A) \<subseteq> sem C (iterate_sem n C B)"
    by (rule sem_monotonic[OF Suc.hyps])
  then show ?case by simp
qed

lemma iterate_sem_after_one:
  "iterate_sem n C (sem C S) = iterate_sem (Suc n) C S"
  by (induct n) simp_all

theorem while_exists_wf:
  fixes Inv :: "('lvar, 'lval) exstate \<Rightarrow> bool"
    and rank :: "('lvar, 'lval) exstate \<Rightarrow> nat"
  assumes start: "\<exists>\<phi>\<in>S. Inv \<phi>"
    and progress: "\<And>\<phi>. Inv \<phi> \<Longrightarrow> b (pproj \<phi>) \<Longrightarrow>
      \<exists>\<psi>\<in>sem (Assume b; C) {\<phi>}. Inv \<psi> \<and> rank \<psi> < rank \<phi>"
  shows "\<exists>\<psi>\<in>sem (while_cond b C) S. Inv \<psi> \<and> \<not> b (pproj \<psi>)"
proof -
  have reach: "\<And>n \<phi>. rank \<phi> = n \<Longrightarrow> Inv \<phi> \<Longrightarrow>
      \<exists>m \<psi>. \<psi> \<in> iterate_sem m (Assume b; C) {\<phi>} \<and>
        Inv \<psi> \<and> \<not> b (pproj \<psi>)"
  proof -
    fix n
    show "\<And>\<phi>. rank \<phi> = n \<Longrightarrow> Inv \<phi> \<Longrightarrow>
      \<exists>m \<psi>. \<psi> \<in> iterate_sem m (Assume b; C) {\<phi>} \<and>
        Inv \<psi> \<and> \<not> b (pproj \<psi>)"
    proof (induct n rule: less_induct)
      case (less n)
      show ?case
      proof (cases "b (pproj \<phi>)")
        case False
        then show ?thesis using less.prems by (rule_tac x=0 in exI, rule_tac x="\<phi>" in exI) simp
      next
        case True
        from progress[OF less.prems(2) True] obtain w where
          step: "w \<in> sem (Assume b; C) {\<phi>}"
          and inv: "Inv w" and drop: "rank w < rank \<phi>" by blast
        from less.hyps[of "rank w" w] less.prems(1) drop inv
        obtain m \<psi> where hit: "\<psi> \<in> iterate_sem m (Assume b; C) {w}"
          and pinv: "Inv \<psi>" and exit: "\<not> b (pproj \<psi>)" by blast
        have sub: "{w} \<subseteq> sem (Assume b; C) {\<phi>}" using step by blast
        have "\<psi> \<in> iterate_sem m (Assume b; C) (sem (Assume b; C) {\<phi>})"
          using hit iterate_sem_mono[OF sub] by blast
        then have "\<psi> \<in> iterate_sem (Suc m) (Assume b; C) {\<phi>}"
          by (simp add: iterate_sem_after_one)
        with pinv exit show ?thesis by blast
      qed
    qed
  qed
  from start obtain \<phi> where mem: "\<phi> \<in> S" and inv: "Inv \<phi>" by blast
  from reach[OF refl inv] obtain n \<psi> where
    hit: "\<psi> \<in> iterate_sem n (Assume b; C) {\<phi>}"
    and pinv: "Inv \<psi>" and exit: "\<not> b (pproj \<psi>)" by blast
  have sub: "{\<phi>} \<subseteq> S" using mem by blast
  have "\<psi> \<in> iterate_sem n (Assume b; C) S"
    using hit iterate_sem_mono[OF sub] by blast
  then have rep: "\<psi> \<in> sem (Rep (Assume b; C)) S"
    by (auto simp: sem_while)
  have fin: "\<psi> \<in> sem (Assume (lnot b)) (sem (Rep (Assume b; C)) S)"
    using rep exit by (cases \<psi>) (auto simp: sem_assume lnot_def pproj_def)
  have "\<psi> \<in> sem (while_cond b C) S"
    using fin by (simp add: while_cond_def sem_seq)
  with pinv exit show ?thesis by blast
qed


subsection \<open>Union-closure loop rule for \<open>\<forall>\<exists>\<close> invariants\<close>

theorem rep_invariant_param:
  assumes step: "\<And>S c. P c S \<Longrightarrow> P c (sem C S)"
      and uc: "\<And>c F. (\<forall>S' \<in> F. P c S') \<Longrightarrow> P c (\<Union> F)"
      and p0: "P c S"
  shows "P c (sem (Rep C) S)"
proof -
  have tail: "\<And>n. P c (iterate_sem n C S)"
  proof -
    fix n
    show "P c (iterate_sem n C S)"
    proof (induct n)
      case 0 show ?case using p0 by simp
    next
      case (Suc n)
      have "iterate_sem (Suc n) C S = sem C (iterate_sem n C S)" by simp
      also have "P c \<dots>" using step Suc by simp
      finally show ?case .
    qed
  qed
  have "P c (\<Union> (range (\<lambda>n. iterate_sem n C S)))"
  proof (rule uc)
    show "\<forall>S' \<in> range (\<lambda>n. iterate_sem n C S). P c S'"
    proof (rule ballI)
      fix S' assume "S' \<in> range (\<lambda>n. iterate_sem n C S)"
      then obtain n where Sn: "S' = iterate_sem n C S" by auto
      then show "P c S'" using tail by blast
    qed
  qed
  then show ?thesis by (simp add: sem_while)
qed

subsection \<open>Live witness coverage across loop rounds\<close>

text \<open>The fixed target sets record the high inputs and low observations
that must remain reachable. The relation may_complete records a live prefix
that can still produce a target observation. This is a set-level invariant:
each target pair needs a witness, but no single state satisfies the whole
assertion.\<close>

definition witness_cover ::
  "('s \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'obs \<Rightarrow> bool) \<Rightarrow>
   'h set \<Rightarrow> 'obs set \<Rightarrow> 's set \<Rightarrow> bool" where
  "witness_cover high may_complete H Obs S \<longleftrightarrow>
    (\<forall>h\<in>H. \<forall>obs\<in>Obs. \<exists>s\<in>S. high s = h \<and> may_complete s obs)"

lemma witness_cover_union_nonempty:
  assumes ne: "F \<noteq> {}"
    and cov: "\<And>T. T \<in> F \<Longrightarrow> witness_cover high may_complete H Obs T"
  shows "witness_cover high may_complete H Obs (\<Union> F)"
proof (unfold witness_cover_def, intro ballI)
  fix h assume h: "h \<in> H"
  fix obs assume obs: "obs \<in> Obs"
  obtain T where TF: "T \<in> F" using ne by blast
  from cov[OF TF, unfolded witness_cover_def] h obs
  obtain s where s: "s \<in> T" "high s = h" "may_complete s obs"
    by blast
  show "\<exists>s\<in>\<Union> F. high s = h \<and> may_complete s obs"
    using TF s by blast
qed

theorem rep_invariant_param_nonempty:
  assumes step: "\<And>S c. P c S \<Longrightarrow> P c (sem C S)"
    and uc: "\<And>c F. F \<noteq> {} \<Longrightarrow> (\<forall>S'\<in>F. P c S') \<Longrightarrow> P c (\<Union> F)"
    and p0: "P c S"
  shows "P c (sem (Rep C) S)"
proof -
  have rounds: "\<And>n. P c (iterate_sem n C S)"
  proof -
    fix n
    show "P c (iterate_sem n C S)"
    proof (induct n)
      case 0 show ?case using p0 by simp
    next
      case (Suc n)
      then show ?case using step by simp
    qed
  qed
  let ?F = "range (\<lambda>n. iterate_sem n C S)"
  have "P c (\<Union> ?F)"
    by (rule uc) (use rounds in auto)
  then show ?thesis by (simp add: sem_while)
qed

theorem rep_witness_cover:
  assumes base: "witness_cover high may_complete H Obs S"
    and step: "\<And>T. witness_cover high may_complete H Obs T \<Longrightarrow>
      witness_cover high may_complete H Obs (sem C T)"
  shows "witness_cover high may_complete H Obs (sem (Rep C) S)"
proof (rule rep_invariant_param_nonempty
    [where P = "\<lambda>_. witness_cover high may_complete H Obs" and c = "()"])
  fix T c assume "witness_cover high may_complete H Obs T"
  then show "witness_cover high may_complete H Obs (sem C T)" by (rule step)
next
  fix c F assume ne: "F \<noteq> {}"
    and cov: "\<forall>T\<in>F. witness_cover high may_complete H Obs T"
  show "witness_cover high may_complete H Obs (\<Union> F)"
    by (rule witness_cover_union_nonempty[OF ne]) (use cov in auto)
next
  show "witness_cover high may_complete H Obs S" by (rule base)
qed

lemma witness_cover_exit_filter:
  assumes cov: "witness_cover high may_complete H Obs S"
    and exit: "\<And>s obs. s \<in> S \<Longrightarrow> may_complete s obs \<Longrightarrow> done s"
  shows "witness_cover high may_complete H Obs {s\<in>S. done s}"
proof (unfold witness_cover_def, intro ballI)
  fix h assume h: "h \<in> H"
  fix obs assume obs: "obs \<in> Obs"
  from cov[unfolded witness_cover_def] h obs
  obtain s where s: "s \<in> S" "high s = h" "may_complete s obs"
    by blast
  show "\<exists>s\<in>{s\<in>S. done s}. high s = h \<and> may_complete s obs"
    using s exit[OF s(1) s(3)] by blast
qed

end
