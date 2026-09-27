theory HybridCompositionality
  imports HybridDerivedRules H3L_Loops.HybridLoops
begin

section \<open>Compositionality seed, HHL loop-rule ports, and a looping GNI proof\<close>

text \<open>
This theory migrates the practically useful layers of the two predecessor
frameworks into H3L:

  \<^item> from HHL's \<^theory_text>\<open>Compositionality.thy\<close>: conjunction and big-union rules
    (the seed of the compositionality layer; linking, filters and frames
    remain future work);
  \<^item> from HHL's \<^theory_text>\<open>Loops.thy\<close>: the witness-existence loop rule
    \<^term>\<open>while_exists\<close>, needed for \<open>\<forall>\<exists>\<close>-shape postconditions
    (GNI, opacity);
  \<^item> a union-closure loop rule \<^term>\<open>rep_invariant_param\<close> for
    \<open>\<forall>\<exists>\<close> invariants that are not per-state (the natural-partition
    rule \<^term>\<open>RepH\<close> cannot express these directly);
  \<^item> a worked example: generalized noninterference for a looping hybrid
    program with a high variable re-havoced in every iteration.
\<close>


subsection \<open>Conjunction and big union\<close>

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

text \<open>Any inductive hyper-invariant lifts to arbitrary unions of runs.\<close>

theorem rule_general_union:
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
        by (meson in_sem)
      then obtain S' where "S' \<in> F" "(fst \<phi>, \<sigma>\<^sub>p, l) \<in> S'" using S by blast
      with src show "\<phi> \<in> \<Union> {sem C S' |S'. S' \<in> F}" using in_sem by blast
    qed
    show "\<Union> {sem C S' |S'. S' \<in> F} \<subseteq> sem C S"
      unfolding S
      by (metis Union_least Union_upper sem_monotonic)
  qed
  have "\<forall>S'' \<in> {sem C S' |S'. S' \<in> F}. P S''"
    using F inv hyper_hoare_tripleE by blast
  with eq show "general_union P (sem C S)"
    unfolding general_union_def by (metis Union_iff mem_Collect_eq)
qed


subsection \<open>HHL port: witness-existence loop rule\<close>

lemma false_state_in_while_cond:
  assumes "\<phi> \<in> S" "\<not> b (pproj \<phi>)"
  shows "\<phi> \<in> sem (while_cond b C) S"
proof -
  have "\<phi> \<in> sem (Rep (Assume b; C)) S"
    using assms(1) sem_while[of "Assume b; C" S] by auto
  then show ?thesis using assms(2)
    by (auto simp: while_cond_def sem_seq sem_assume)
qed

text \<open>
Port of HHL's \<open>while_exists\<close>: from a family of triples indexed by a
witness \<^term>\<open>\<phi>\<close>, obtain an existential postcondition over the output
set.  This is the \<open>\<exists>\<close>-half of \<open>\<forall>\<exists>\<close> reasoning for loops.
\<close>

theorem while_exists:
  assumes "\<And>\<phi>. \<Turnstile> { P \<phi> } while_cond b C { Q \<phi> }"
  shows "\<Turnstile> { (\<lambda>S. \<exists>\<phi> \<in> S. \<not> b (pproj \<phi>) \<and> P \<phi> S) }
       while_cond b C
      { (\<lambda>S. \<exists>\<phi> \<in> S. Q \<phi> S) }"
proof (rule hyper_hoare_tripleI)
  fix S assume "\<exists>\<phi>\<in>S. \<not> b (pproj \<phi>) \<and> P \<phi> S"
  then obtain \<phi> where asm0: "\<phi>\<in>S" "\<not> b (pproj \<phi>) \<and> P \<phi> S" by blast
  then have "Q \<phi> (sem (while_cond b C) S)"
    using assms hyper_hoare_tripleE by blast
  then show "\<exists>\<phi>\<in>sem (while_cond b C) S. Q \<phi> (sem (while_cond b C) S)"
    using asm0 false_state_in_while_cond by blast
qed


subsection \<open>A union-closure loop rule for \<open>\<forall>\<exists>\<close> invariants\<close>

text \<open>
\<^term>\<open>RepH\<close> needs an indexed per-iteration family; hyperproperties such
as GNI are \<^emph>\<open>not\<close> per-state assertions, so that shape does not fit.
The rule below takes an invariant family \<^term>\<open>P c\<close> indexed by a
parameter \<^term>\<open>c\<close> (e.g.\ the common low value) that is preserved by
the body and whose conjunction with union-closure holds along all
unrollings.
\<close>

theorem rep_invariant_param:
  assumes step: "\<And>S c. P c S \<Longrightarrow> P c (sem C S)"
      and uc: "\<And>c F. (\<forall>S' \<in> F. P c S') \<Longrightarrow> P c (\<Union> F)"
      and p0: "P c S"
  shows "P c (sem (Rep C) S)"
proof -
  have "\<And>n. P c (iterate_sem n C S)"
  proof (induct n)
    case 0 show ?case using p0 by simp
  next
    case (Suc n)
    have "iterate_sem (Suc n) C S = sem C (iterate_sem n C S)" by simp
    also have "P c \<dots>" using step Suc by simp
    finally show ?case .
  qed
  then have "P c (\<Union> (range (\<lambda>n. iterate_sem n C S)))"
    by (rule uc) blast
  then show ?thesis by (simp add: sem_while)
qed


subsection \<open>Exemplar: lifting gGHL's ODE rule family through \<^term>\<open>hl_bridge\<close>\<close>

text \<open>
The whole gGHL rule family in \<^theory_text>\<open>hhl/ComplementlemmaHHL\<close>
(\<^term>\<open>Valid_inv_s_ge\<close>, \<^term>\<open>Valid_inv_tr_le\<close>, barriers, differential
cuts, ...) lifts by exactly the pattern below: wrap the HHL statement with
\<^term>\<open>hl_lift\<close> and apply \<^term>\<open>hl_bridge\<close>.  We spell out one
representative; the rest are mechanical.
\<close>

corollary h3l_Valid_inv':
  fixes inv :: "state \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' (x)) (at x within UNIV)"
      and "\<forall>s. b s \<longrightarrow> g' (state2vec s) (ODE2Vec ode s) = 0"
  shows "\<Turnstile> {hl_lift (\<lambda>s tr. inv s = r \<and> P tr \<and> b s)}
     Cont ode b
    {hl_lift (\<lambda>s tr. (P @\<^sub>t ode_inv_assn (\<lambda>s. inv s = r)) tr)}"
  by (rule hl_bridge, rule ContinuousInvHHL.Valid_inv'[OF assms])


subsection \<open>Worked example: looping generalized noninterference\<close>

definition HH :: var where "HH = CHR ''h''"
definition LL :: var where "LL = CHR ''l''"

lemma HH_LL_neq [simp]: "HH \<noteq> LL" "LL \<noteq> HH"
  unfolding HH_def LL_def by auto

definition gni_set :: "var \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni_set l h S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. \<exists>\<phi> \<in> S.
       pproj \<phi> h = pproj \<phi>1 h \<and> pproj \<phi> l = pproj \<phi>2 l)"

lemma gni_set_union_closed:
  assumes "\<And>S'. S' \<in> F \<Longrightarrow> gni_set l h S'"
  shows "gni_set l h (\<Union> F)"
  using assms unfolding gni_set_def by blast

text \<open>Havoc of the high variable both \<^emph>\<open>establishes\<close> and preserves GNI:
for any two outcomes, the run that shares the second's source and received
the first's high value is a masking witness.\<close>

lemma havoc_establishes_gni:
  assumes hl: "h \<noteq> l"
  shows "gni_set l h (sem (Havoc h) S)"
proof -
  have rw: "sem (Havoc h) S = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(h := v), tr) |\<sigma>\<^sub>l \<sigma>\<^sub>p v tr. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr) \<in> S}"
    by (rule sem_havoc)
  show ?thesis unfolding gni_set_def rw
  proof (intro ballI)
    fix \<phi>1 \<phi>2
    assume asm12: "\<phi>1 \<in> {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(h := v), tr) |\<sigma>\<^sub>l \<sigma>\<^sub>p v tr. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr) \<in> S}"
                 "\<phi>2 \<in> {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(h := v), tr) |\<sigma>\<^sub>l \<sigma>\<^sub>p v tr. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr) \<in> S}"
    then obtain a1 b1 t1 v1 where p1: "\<phi>1 = (a1, b1(h := v1), t1)" "(a1, b1, t1) \<in> S" by blast
    from asm12(2) obtain a2 b2 t2 v2 where p2: "\<phi>2 = (a2, b2(h := v2), t2)" "(a2, b2, t2) \<in> S" by blast
    show "\<exists>\<phi> \<in> {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(h := v), tr) |\<sigma>\<^sub>l \<sigma>\<^sub>p v tr. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr) \<in> S}.
             pproj \<phi> h = pproj \<phi>1 h \<and> pproj \<phi> l = pproj \<phi>2 l"
      using p1 p2 hl by (rule_tac x = "(a2, b2(h := v1), t2)" in bexI, auto simp: pproj_def)
  qed
qed

lemma havoc_common_low:
  assumes hl: "h \<noteq> l" and c: "\<forall>\<phi>\<in>S. pproj \<phi> l = c"
  shows "\<forall>\<phi>\<in>sem (Havoc h) S. pproj \<phi> l = c"
  using c unfolding sem_havoc by (auto simp: pproj_def fun_upd_other hl)

theorem gni_loop_example:
  "\<Turnstile> {\<lambda>S. \<exists>c. \<forall>\<phi>\<in>S. pproj \<phi> LL = c}
      (Havoc HH; Rep (Havoc HH))
   {\<lambda>S. gni_set LL HH S}"
proof (rule seq_rule)
  show "\<Turnstile> {\<lambda>S. \<exists>c. \<forall>\<phi>\<in>S. pproj \<phi> LL = c} Havoc HH
          {\<lambda>S. \<exists>c. (\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S}"
  proof (rule hyper_hoare_tripleI)
    fix S assume "\<exists>c. \<forall>\<phi>\<in>S. pproj \<phi> LL = c"
    then obtain c where c: "\<forall>\<phi>\<in>S. pproj \<phi> LL = c" by blast
    show "\<exists>c. (\<forall>\<phi>\<in>sem (Havoc HH) S. pproj \<phi> LL = c) \<and> gni_set LL HH (sem (Havoc HH) S)"
      using havoc_common_low[OF HH_LL_neq(1) c] havoc_establishes_gni[OF HH_LL_neq(1), of S]
      by blast
  qed
next
  show "\<Turnstile> {\<lambda>S. \<exists>c. (\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S} Rep (Havoc HH)
          {\<lambda>S. \<exists>c. (\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S}"
  proof (rule hyper_hoare_tripleI)
    fix S assume "\<exists>c. (\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S"
    then obtain c where cS: "(\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S" by blast
    have main: "(\<forall>\<phi>\<in>sem (Rep (Havoc HH)) S. pproj \<phi> LL = c)
          \<and> gni_set LL HH (sem (Rep (Havoc HH)) S)"
    proof (rule rep_invariant_param
            [where C = "Havoc HH"
              and P = "\<lambda>c S. (\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S"])
      fix S c assume a: "(\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S"
      then show "(\<forall>\<phi>\<in>sem (Havoc HH) S. pproj \<phi> LL = c) \<and> gni_set LL HH (sem (Havoc HH) S)"
        using havoc_common_low[OF HH_LL_neq(1)] havoc_establishes_gni[OF HH_LL_neq(1), of S] by blast
    next
      fix c F assume "\<forall>S'\<in>F. (\<forall>\<phi>\<in>S'. pproj \<phi> LL = c) \<and> gni_set LL HH S'"
      then show "(\<forall>\<phi>\<in>\<Union> F. pproj \<phi> LL = c) \<and> gni_set LL HH (\<Union> F)"
        using gni_set_union_closed[of LL HH F] by blast
    next
      show "(\<forall>\<phi>\<in>S. pproj \<phi> LL = c) \<and> gni_set LL HH S" using cS .
    qed
    then show "\<exists>c. (\<forall>\<phi>\<in>sem (Rep (Havoc HH)) S. pproj \<phi> LL = c)
          \<and> gni_set LL HH (sem (Rep (Havoc HH)) S)" by blast
  qed
qed

end
