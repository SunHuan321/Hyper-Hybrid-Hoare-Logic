theory PhaseG_GNI_v2
  imports HybridCompositionalityRules
begin

section \<open>Phase G v2: GNI proved via compositionality rules\<close>

text \<open>
Rewritten proof using the compositionality rule layer instead of unfolding
sem/big_step.  Only two atomic lemmas about Havoc touch semantics.
\<close>


subsection \<open>GNI definitions\<close>

definition HH2 :: var where "HH2 = CHR ''h''"
definition LL2 :: var where "LL2 = CHR ''l''"

lemma HH2_LL2_neq [simp]: "HH2 \<noteq> LL2" "LL2 \<noteq> HH2"
  unfolding HH2_def LL2_def by auto

definition gni :: "var \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni l h S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. \<exists>\<phi> \<in> S.
       pproj \<phi> h = pproj \<phi>1 h \<and> pproj \<phi> l = pproj \<phi>2 l)"

definition low_const :: "var \<Rightarrow> real \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "low_const l c S \<longleftrightarrow> (\<forall>\<phi>\<in>S. pproj \<phi> l = c)"

definition low_agree :: "var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "low_agree l S \<longleftrightarrow> (\<exists>c. low_const l c S)"


subsection \<open>Atomic lemma 1: Havoc preserves low (one sem-level proof)\<close>

lemma havoc_preserves_low:
  assumes hl: "h \<noteq> l"
  shows "hyper_hoare_triple (low_const l c) (Havoc h) (low_const l c)"
proof (rule hyper_hoare_tripleI)
  fix S assume a0: "low_const l c S"
  show "low_const l c (sem (Havoc h) S)"
    using a0 hl not_sym [OF hl] unfolding low_const_def sem_havoc
    by (auto simp: pproj_def fun_upd_other)
qed


subsection \<open>Atomic lemma 2: Havoc establishes GNI (one sem-level proof)\<close>

lemma havoc_establishes_gni:
  assumes hl: "h \<noteq> l"
  shows "hyper_hoare_triple (\<lambda>S. True) (Havoc h) (gni l h)"
proof (rule hyper_hoare_tripleI)
  fix S assume a0: "True"
  show "gni l h (sem (Havoc h) S)"
  proof (unfold gni_def, (rule ballI)+)
    fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> sem (Havoc h) S" and m2: "\<phi>2 \<in> sem (Havoc h) S"
    from m1 obtain a1 b1 t1 v1 where p1: "\<phi>1 = (a1, b1(h := v1), t1)" "(a1, b1, t1) \<in> S"
      unfolding sem_havoc by blast
    from m2 obtain a2 b2 t2 v2 where p2: "\<phi>2 = (a2, b2(h := v2), t2)" "(a2, b2, t2) \<in> S"
      unfolding sem_havoc by blast
    have wmem: "(a2, b2(h := v1), t2) \<in> sem (Havoc h) S"
      using p2(2) unfolding sem_havoc by blast
    have wh: "pproj (a2, b2(h := v1), t2) h = pproj \<phi>1 h"
      by (simp add: p1(1) pproj_def)
    have wl: "pproj (a2, b2(h := v1), t2) l = pproj \<phi>2 l"
      by (simp add: p2(1) pproj_def fun_upd_other hl [THEN not_sym])
    show "\<exists>\<phi> \<in> sem (Havoc h) S. pproj \<phi> h = pproj \<phi>1 h \<and> pproj \<phi> l = pproj \<phi>2 l"
      by (rule_tac x = "(a2, b2(h := v1), t2)" in bexI, simp add: wh wl, fact wmem)
  qed
qed


subsection \<open>Compositionality: combine havoc facts\<close>

theorem havoc_step:
  assumes hl: "h \<noteq> l"
  shows "hyper_hoare_triple (low_const l c) (Havoc h)
              (conj (low_const l c) (gni l h))"
proof (rule hyper_hoare_tripleI)
  fix S assume a0: "low_const l c S"
  from havoc_preserves_low [OF hl] a0
  have h1: "low_const l c (sem (Havoc h) S)"
    unfolding hyper_hoare_triple_def by blast
  from havoc_establishes_gni [OF hl]
  have h2: "gni l h (sem (Havoc h) S)"
    unfolding hyper_hoare_triple_def by blast
  from h1 h2 show "conj (low_const l c) (gni l h) (sem (Havoc h) S)"
    by (simp add: conj_def)
qed


subsection \<open>Union closure of the invariant\<close>

lemma gni_low_union_closed:
  fixes c :: real
  assumes hyp: "\<And>S'. S' \<in> F \<Longrightarrow> conj (low_const l c) (gni l h) S'"
  shows "conj (low_const l c) (gni l h) (\<Union> F)"
proof (unfold conj_def, rule conjI)
  show "low_const l c (\<Union> F)"
  proof (unfold low_const_def, rule ballI)
    fix \<phi> assume m: "\<phi> \<in> \<Union> F"
    then show "pproj \<phi> l = c"
    proof (rule UnionE)
      fix X assume xin: "\<phi> \<in> X" and XF: "X \<in> F"
      from hyp [OF XF] have "low_const l c X" by (simp add: conj_def)
      with xin show "pproj \<phi> l = c" by (simp add: low_const_def)
    qed
  qed
next
  show "gni l h (\<Union> F)"
  proof (unfold gni_def, (rule ballI)+)
    fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> \<Union> F" and m2: "\<phi>2 \<in> \<Union> F"
    from m1 obtain S1 where s1: "S1 \<in> F" "\<phi>1 \<in> S1" by blast
    from m2 obtain S2 where s2: "S2 \<in> F" "\<phi>2 \<in> S2" by blast
    from hyp [OF s1(1)] have g1: "gni l h S1" by (simp add: conj_def)
    from g1 [unfolded gni_def, rule_format, OF s1(2) s1(2)]
    obtain \<phi> where w: "\<phi> \<in> S1" "pproj \<phi> h = pproj \<phi>1 h"
      "pproj \<phi> l = pproj \<phi>1 l" by blast
    from hyp [OF s1(1)] have lc1: "\<forall>\<phi>\<in>S1. pproj \<phi> l = c"
      by (simp add: conj_def low_const_def)
    from hyp [OF s2(1)] have lc2: "\<forall>\<phi>\<in>S2. pproj \<phi> l = c"
      by (simp add: conj_def low_const_def)
    have "pproj \<phi> l = pproj \<phi>2 l"
      using w(3) lc1 lc2 s1(2) s2(2) by simp
    with w s1(1) show "\<exists>\<phi>\<in>\<Union> F. pproj \<phi> h = pproj \<phi>1 h \<and> pproj \<phi> l = pproj \<phi>2 l"
      by blast
  qed
qed


subsection \<open>Main theorem: pure compositionality-level\<close>

theorem gni_loop_v2:
  shows "hyper_hoare_triple (low_agree LL2)
              (Seq (Havoc HH2) (Rep (Havoc HH2)))
              (gni LL2 HH2)"
proof (rule hyper_hoare_tripleI)
  fix S assume pre: "low_agree LL2 S"
  then obtain c where c: "low_const LL2 c S"
    by (auto simp: low_agree_def)
  have step1: "conj (low_const LL2 c) (gni LL2 HH2) (sem (Havoc HH2) S)"
    using havoc_step [OF HH2_LL2_neq(1)] c
    unfolding hyper_hoare_triple_def by blast
  have step2: "conj (low_const LL2 c) (gni LL2 HH2)
                  (sem (Rep (Havoc HH2)) (sem (Havoc HH2) S))"
  proof (rule rep_invariant_param
          [where C = "Havoc HH2"
            and P = "\<lambda>c S. conj (low_const LL2 c) (gni LL2 HH2) S"])
    fix T c' assume a: "conj (low_const LL2 c') (gni LL2 HH2) T"
    then show "conj (low_const LL2 c') (gni LL2 HH2) (sem (Havoc HH2) T)"
      using havoc_step [OF HH2_LL2_neq(1)]
      unfolding hyper_hoare_triple_def conj_def by blast
  next
    fix c' F assume hF: "\<forall>S'\<in>F. conj (low_const LL2 c') (gni LL2 HH2) S'"
    show "conj (low_const LL2 c') (gni LL2 HH2) (\<Union> F)"
    proof (rule gni_low_union_closed)
      fix S' assume "S' \<in> F"
      with hF show "conj (low_const LL2 c') (gni LL2 HH2) S'" by blast
    qed
  next
    show "conj (low_const LL2 c) (gni LL2 HH2) (sem (Havoc HH2) S)"
      using step1 .
  qed
  show "gni LL2 HH2 (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    unfolding sem_seq using step2 by (simp add: conj_def)
qed

end
