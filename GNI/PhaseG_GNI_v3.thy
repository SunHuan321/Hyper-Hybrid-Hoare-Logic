theory PhaseG_GNI_v3
  imports PhaseG_GNI_v2
begin

section \<open>Phase G v3: corrected final-state GNI\<close>

text \<open>
Corrected GNI assertion following the review roadmap (\<^emph>\<open>2026-09-25\<close>,
\<^bold>\<open>\<S>2\<close>).  Two findings about the earlier definitions:

  \<^item> v2's \<^term>\<open>gni LL2 HH2\<close> crosses only FINAL program values.  A
    program that first leaks the high input into the low variable and then
    re-randomises the high variable (\<^emph>\<open>l ::= h; h ::= *\<close>)
    satisfies it: the laundering program is accepted, see
    \<^theory_text>\<open>laundered_gni_v2_holds\<close>.

  \<^item> The label-only crossing of the removed \<^theory_text>\<open>PhaseG_GNI_IO\<close>
    (for all \<open>\<phi>1 \<phi>2\<close> with equal low labels there is \<open>\<phi>3\<close> with
    crossed labels) is trivially true: take \<open>\<phi>3 = \<phi>1\<close>.  Recorded as
    \<^theory_text>\<open>label_crossing_trivial\<close>.  As a postcondition it says
    nothing; the fix is to keep the labels but ADD the low output conjunct.

\<^bold>\<open>gni_final\<close> below reads the high INPUT from the logical labels
(preserved by \<^const>\<open>sem\<close>, so it cannot be laundered by later commands)
and requires a third execution with \<open>\<phi>1\<close>'s recorded high input,
\<open>\<phi>2\<close>'s recorded low input, and \<open>\<phi>2\<close>'s low OUTPUT.  The
low-output conjunct blocks the trivial witness and is exactly what the
leaking program violates: from \<open>\<phi>1\<close>'s high input, no execution
reaches \<open>\<phi>2\<close>'s low output.
\<close>


subsection \<open>The corrected assertion\<close>

definition gni_final :: "'lvar \<Rightarrow> 'lvar \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni_final hi lo l S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. lproj \<phi>1 lo = lproj \<phi>2 lo \<longrightarrow>
      (\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
        \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
        \<and> pproj \<phi>3 l = pproj \<phi>2 l))"

lemma label_crossing_trivial:
  "(\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. lproj \<phi>1 lo = lproj \<phi>2 lo \<longrightarrow>
      (\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi \<and> lproj \<phi>3 lo = lproj \<phi>2 lo))"
  by blast


subsection \<open>Semantics helpers\<close>

lemma sem_assign_memI:
  assumes "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S"
  shows "(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p), l) \<in> sem (Assign x e) S"
  using assms unfolding sem_assign by blast

lemma sem_assign_memE:
  assumes "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', l) \<in> sem (Assign x e) S"
  shows "\<exists>\<sigma>\<^sub>p. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<sigma>\<^sub>p' = \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p)"
  using assms unfolding sem_assign by auto

lemma sem_rep_subset:
  "S \<subseteq> sem (Rep C) S"
proof -
  have z: "(\<lambda>n. iterate_sem n C S) 0 = S" by simp
  then have "S \<in> range (\<lambda>n. iterate_sem n C S)" by (metis rangeI)
  then have "S \<subseteq> \<Union> (range (\<lambda>n. iterate_sem n C S))" by (rule Union_upper)
  then show ?thesis by (simp add: sem_while)
qed


subsection \<open>Counterexample: the leaking program is rejected\<close>

definition HI :: char where "HI = CHR ''i''"
definition LO :: char where "LO = CHR ''o''"

lemma HI_LO_neq [simp]: "HI \<noteq> LO" "LO \<noteq> HI"
  unfolding HI_def LO_def by auto

text \<open>
Initial set: two executions with the same low program variable (both 0) and
the same logical low label (both 0), but different high inputs.  The logical
label \<^const>\<open>HI\<close> records the high input, as the logical component is
preserved by \<^const>\<open>sem\<close>.
\<close>

definition leak_init1 :: "(char, real) exstate" where
  "leak_init1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1), [])"

definition leak_init2 :: "(char, real) exstate" where
  "leak_init2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2), [])"

definition S_leak :: "(char, real) exstate set" where
  "S_leak = {leak_init1, leak_init2}"

definition C_leak :: proc where
  "C_leak = LL2 ::= (\<lambda>\<sigma>. \<sigma> HH2)"

definition leak_run1 :: "(char, real) exstate" where
  "leak_run1 = ((\<lambda>_. 0)(HI := 1), ((\<lambda>_. 0)(HH2 := 1))(LL2 := 1), [])"

definition leak_run2 :: "(char, real) exstate" where
  "leak_run2 = ((\<lambda>_. 0)(HI := 2), ((\<lambda>_. 0)(HH2 := 2))(LL2 := 2), [])"

lemma S_leak_low_const:
  "low_const LL2 0 S_leak"
  by (auto simp: low_const_def S_leak_def leak_init1_def leak_init2_def pproj_def)

lemma S_leak_low_agree:
  "low_agree LL2 S_leak"
  unfolding low_agree_def using S_leak_low_const by blast

lemma leak_run1_mem:
  "leak_run1 \<in> sem C_leak S_leak"
proof -
  have val: "(\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init1)) = 1"
    by (simp add: leak_init1_def)
  have src: "(fst leak_init1, fst (snd leak_init1), snd (snd leak_init1)) \<in> S_leak"
    by (simp add: S_leak_def)
  have "leak_run1 = (fst leak_init1,
           (fst (snd leak_init1))(LL2 := (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init1))),
           snd (snd leak_init1))"
    by (simp add: leak_run1_def leak_init1_def val)
  moreover have "(fst leak_init1,
           (fst (snd leak_init1))(LL2 := (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init1))),
           snd (snd leak_init1)) \<in> sem C_leak S_leak"
    unfolding C_leak_def by (rule sem_assign_memI [OF src])
  ultimately show ?thesis by simp
qed

lemma leak_run2_mem:
  "leak_run2 \<in> sem C_leak S_leak"
proof -
  have val: "(\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init2)) = 2"
    by (simp add: leak_init2_def)
  have src: "(fst leak_init2, fst (snd leak_init2), snd (snd leak_init2)) \<in> S_leak"
    by (simp add: S_leak_def)
  have "leak_run2 = (fst leak_init2,
           (fst (snd leak_init2))(LL2 := (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init2))),
           snd (snd leak_init2))"
    by (simp add: leak_run2_def leak_init2_def val)
  moreover have "(fst leak_init2,
           (fst (snd leak_init2))(LL2 := (\<lambda>\<sigma>. \<sigma> HH2) (fst (snd leak_init2))),
           snd (snd leak_init2)) \<in> sem C_leak S_leak"
    unfolding C_leak_def by (rule sem_assign_memI [OF src])
  ultimately show ?thesis by simp
qed

lemma leak_mem_cases:
  assumes m: "\<phi> \<in> sem C_leak S_leak"
  shows "\<phi> = leak_run1 \<or> \<phi> = leak_run2"
proof -
  obtain a b t where pd: "\<phi> = (a, b, t)" by (metis prod.exhaust)
  from m pd obtain bp where src: "(a, bp, t) \<in> S_leak"
    and upd: "b = bp(LL2 := (\<lambda>\<sigma>. \<sigma> HH2) bp)"
    unfolding C_leak_def by (auto dest: sem_assign_memE)
  from src have c: "(a, bp, t) = leak_init1 \<or> (a, bp, t) = leak_init2"
    by (auto simp: S_leak_def)
  then show ?thesis using upd pd
    by (auto simp: leak_run1_def leak_run2_def leak_init1_def leak_init2_def)
qed

lemma gni_final_leak_fails:
  "\<not> gni_final HI LO LL2 (sem C_leak S_leak)"
proof
  assume g: "gni_final HI LO LL2 (sem C_leak S_leak)"
  have loeq: "lproj leak_run1 LO = lproj leak_run2 LO"
    by (simp add: leak_run1_def leak_run2_def lproj_def)
  from g [unfolded gni_final_def, rule_format,
          OF leak_run1_mem leak_run2_mem loeq]
  obtain \<phi>3 where w3: "\<phi>3 \<in> sem C_leak S_leak"
    "lproj \<phi>3 HI = lproj leak_run1 HI"
    "lproj \<phi>3 LO = lproj leak_run2 LO"
    "pproj \<phi>3 LL2 = pproj leak_run2 LL2" by blast
  from leak_mem_cases [OF w3(1)] show False
  proof
    assume "\<phi>3 = leak_run1"
    with w3(4) show False
      by (simp add: leak_run1_def leak_run2_def pproj_def)
  next
    assume "\<phi>3 = leak_run2"
    with w3(2) show False
      by (simp add: leak_run1_def leak_run2_def lproj_def)
  qed
qed

theorem leak_program_refuted:
  "\<not> hyper_hoare_triple (low_agree LL2) C_leak
       (gni_final HI LO LL2 :: ((char, real) exstate) set \<Rightarrow> bool)"
proof (rule notI)
  assume tr: "hyper_hoare_triple (low_agree LL2) C_leak
       (gni_final HI LO LL2 :: ((char, real) exstate) set \<Rightarrow> bool)"
  hence "gni_final HI LO LL2 (sem C_leak S_leak)"
    using S_leak_low_agree unfolding hyper_hoare_triple_def by blast
  thus False using gni_final_leak_fails by simp
qed


subsection \<open>Separation: v2's gni accepts the laundering program\<close>

definition C_launder :: proc where
  "C_launder = Seq C_leak (Havoc HH2)"

lemma clobbered_cases:
  assumes m: "\<phi> \<in> sem C_launder S_leak"
  shows "\<exists>b t v. (fst \<phi>, b, t) \<in> {leak_run1, leak_run2}
          \<and> \<phi> = (fst \<phi>, b(HH2 := v), t)"
proof -
  from m have m': "\<phi> \<in> sem (Havoc HH2) (sem C_leak S_leak)"
    by (simp add: C_launder_def sem_seq)
  then obtain a b t v where eq: "\<phi> = (a, b(HH2 := v), t)"
    and mem: "(a, b, t) \<in> sem C_leak S_leak"
    unfolding sem_havoc by blast
  from leak_mem_cases [OF mem] have "(a, b, t) = leak_run1 \<or> (a, b, t) = leak_run2" .
  then have memf: "(fst \<phi>, b, t) \<in> {leak_run1, leak_run2}" using eq by auto
  have eqf: "\<phi> = (fst \<phi>, b(HH2 := v), t)" using eq by simp
  show ?thesis using memf eqf by blast
qed

theorem laundered_gni_v2_holds:
  "gni LL2 HH2 (sem C_launder S_leak)"
proof (unfold gni_def, (rule ballI)+)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> sem C_launder S_leak"
     and m2: "\<phi>2 \<in> sem C_launder S_leak"
  from clobbered_cases [OF m1] obtain b1 t1 v1 where
    s1: "(fst \<phi>1, b1, t1) \<in> {leak_run1, leak_run2}"
        "\<phi>1 = (fst \<phi>1, b1(HH2 := v1), t1)" by blast
  from clobbered_cases [OF m2] obtain b2 t2 v2 where
    s2: "(fst \<phi>2, b2, t2) \<in> {leak_run1, leak_run2}"
        "\<phi>2 = (fst \<phi>2, b2(HH2 := v2), t2)" by blast
  have wmem: "(fst \<phi>2, b2(HH2 := v1), t2) \<in> sem C_launder S_leak"
  proof -
    have "(fst \<phi>2, b2, t2) \<in> sem C_leak S_leak"
      using s2(1) leak_run1_mem leak_run2_mem by auto
    then have "(fst \<phi>2, b2(HH2 := v1), t2) \<in> sem (Havoc HH2) (sem C_leak S_leak)"
      unfolding sem_havoc by blast
    then show ?thesis by (simp add: C_launder_def sem_seq)
  qed
  have e1: "pproj \<phi>1 = b1(HH2 := v1)" using s1(2)
    by (metis pproj_def fst_conv snd_conv)
  have e2: "pproj \<phi>2 = b2(HH2 := v2)" using s2(2)
    by (metis pproj_def fst_conv snd_conv)
  have wh: "pproj (fst \<phi>2, b2(HH2 := v1), t2) HH2 = pproj \<phi>1 HH2"
    using e1 by (simp add: pproj_def)
  have wl: "pproj (fst \<phi>2, b2(HH2 := v1), t2) LL2 = pproj \<phi>2 LL2"
    using e2 by (simp add: pproj_def HH2_LL2_neq(2))
  have key: "\<exists>\<phi> \<in> sem C_launder S_leak.
          pproj \<phi> HH2 = pproj \<phi>1 HH2 \<and> pproj \<phi> LL2 = pproj \<phi>2 LL2"
    apply (rule_tac x = "(fst \<phi>2, b2(HH2 := v1), t2)" in bexI)
     apply (rule conjI [OF wh wl])
    apply (rule wmem)
    done
  show "\<exists>\<phi> \<in> sem C_launder S_leak.
          pproj \<phi> HH2 = pproj \<phi>1 HH2 \<and> pproj \<phi> LL2 = pproj \<phi>2 LL2"
    by (rule key)
qed


subsection \<open>The laundering program is rejected by gni_final\<close>

theorem laundered_gni_final_fails:
  "\<not> gni_final HI LO LL2 (sem C_launder S_leak)"
proof -
  let ?T = "sem C_launder S_leak"
  define w1 :: "(char, real) exstate" where
    "w1 = ((\<lambda>_. 0)(HI := 1), (((\<lambda>_. 0)(HH2 := 1))(LL2 := 1))(HH2 := 5), [])"
  define w2 :: "(char, real) exstate" where
    "w2 = ((\<lambda>_. 0)(HI := 2), (((\<lambda>_. 0)(HH2 := 2))(LL2 := 2))(HH2 := 7), [])"
  have w1eq: "w1 = (fst leak_run1, (pproj leak_run1)(HH2 := 5), tproj leak_run1)"
    by (simp add: w1_def leak_run1_def pproj_def tproj_def)
  have w2eq: "w2 = (fst leak_run2, (pproj leak_run2)(HH2 := 7), tproj leak_run2)"
    by (simp add: w2_def leak_run2_def pproj_def tproj_def)
  have r1eq: "(fst leak_run1, pproj leak_run1, tproj leak_run1) = leak_run1"
    by (simp add: leak_run1_def pproj_def tproj_def)
  have src1: "(fst leak_run1, pproj leak_run1, tproj leak_run1) \<in> sem C_leak S_leak"
    using r1eq leak_run1_mem by simp
  have r2eq: "(fst leak_run2, pproj leak_run2, tproj leak_run2) = leak_run2"
    by (simp add: leak_run2_def pproj_def tproj_def)
  have src2: "(fst leak_run2, pproj leak_run2, tproj leak_run2) \<in> sem C_leak S_leak"
    using r2eq leak_run2_mem by simp
  have "(fst leak_run1, (pproj leak_run1)(HH2 := 5), tproj leak_run1)
          \<in> sem (Havoc HH2) (sem C_leak S_leak)"
    using src1 unfolding sem_havoc by blast
  then have w1mem: "w1 \<in> ?T"
    unfolding w1eq by (simp add: C_launder_def sem_seq)
  have "(fst leak_run2, (pproj leak_run2)(HH2 := 7), tproj leak_run2)
          \<in> sem (Havoc HH2) (sem C_leak S_leak)"
    using src2 unfolding sem_havoc by blast
  then have w2mem: "w2 \<in> ?T"
    unfolding w2eq by (simp add: C_launder_def sem_seq)
  have loeq: "lproj w1 LO = lproj w2 LO"
    by (simp add: w1_def w2_def lproj_def)
  show ?thesis
  proof
    assume g: "gni_final HI LO LL2 ?T"
    from g [unfolded gni_final_def, rule_format, OF w1mem w2mem loeq]
    obtain \<phi>3 where w3: "\<phi>3 \<in> ?T"
      "lproj \<phi>3 HI = lproj w1 HI"
      "lproj \<phi>3 LO = lproj w2 LO"
      "pproj \<phi>3 LL2 = pproj w2 LL2" by blast
    from clobbered_cases [OF w3(1)] obtain b t v where
      src: "(fst \<phi>3, b, t) \<in> {leak_run1, leak_run2}"
      and eq3: "\<phi>3 = (fst \<phi>3, b(HH2 := v), t)" by blast
    from src consider (r1) "(fst \<phi>3, b, t) = leak_run1"
                  | (r2) "(fst \<phi>3, b, t) = leak_run2"
      by auto
    then show False
    proof cases
      case r1
      then have hb: "b = ((\<lambda>_. 0)(HH2 := 1))(LL2 := 1)"
        by (simp add: leak_run1_def)
      have p3: "pproj \<phi>3 = b(HH2 := v)" using eq3
        by (metis pproj_def fst_conv snd_conv)
      from w3(4) p3 have "(b(HH2 := v)) LL2 = pproj w2 LL2" by simp
      then show False using hb by (simp add: w2_def pproj_def)
    next
      case r2
      then have hf: "fst \<phi>3 = (\<lambda>_. 0)(HI := 2)"
        by (simp add: leak_run2_def)
      with w3(2) show False by (simp add: lproj_def w1_def)
    qed
  qed
qed


subsection \<open>Positive example: the havoc loop satisfies gni_final\<close>

text \<open>
Same toy program as v2.  The witness for the pair \<open>(\<phi>1, \<phi>2)\<close> is a
run that starts from \<open>\<phi>1\<close>'s own initial state -- hence carries
\<open>\<phi>1\<close>'s recorded high input -- and simply leaves the low program
variable untouched; low-preservation carries the low output.
\<close>

lemma gni_final_havoc_rep_set:
  assumes c: "low_const LL2 c (S :: ((char, real) exstate) set)"
  shows "gni_final HI LO LL2 (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
proof (unfold gni_final_def, rule ballI, rule ballI, rule impI)
  have h1: "low_const LL2 c (sem (Havoc HH2) S)"
    using havoc_preserves_low [OF HH2_LL2_neq(1)] c
    unfolding hyper_hoare_triple_def by blast
  have h2: "low_const LL2 c (sem (Rep (Havoc HH2)) (sem (Havoc HH2) S))"
  proof (rule rep_invariant_param
          [where C = "Havoc HH2" and P = "\<lambda>c S. low_const LL2 c S"])
    fix T c' assume a: "low_const LL2 c' T"
    show "low_const LL2 c' (sem (Havoc HH2) T)"
      using havoc_preserves_low [OF HH2_LL2_neq(1)] a
      unfolding hyper_hoare_triple_def by blast
  next
    fix c' F assume hF: "\<forall>S'\<in>F. low_const LL2 c' S'"
    show "low_const LL2 c' (\<Union> F)" using hF unfolding low_const_def by blast
  next
    show "low_const LL2 c (sem (Havoc HH2) S)" using h1 .
  qed
  have low_inv: "low_const LL2 c (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    unfolding sem_seq using h2 .
  fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
       and m2: "\<phi>2 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
       and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
    from sem_lproj_src [OF m1] obtain src1 where
      src1: "src1 \<in> S" "lproj \<phi>1 = lproj src1" by blast
    obtain a q tr where sq: "src1 = (a, q, tr)" by (metis prod.exhaust)
    with src1(1) have qmem: "(a, q, tr) \<in> S" by simp
    have wstep: "(a, q(HH2 := 0), tr) \<in> sem (Havoc HH2) S"
      using qmem unfolding sem_havoc by blast
    have wrep: "(a, q(HH2 := 0), tr) \<in> sem (Rep (Havoc HH2)) (sem (Havoc HH2) S)"
      using wstep sem_rep_subset by blast
    have wmem: "(a, q(HH2 := 0), tr) \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S"
      unfolding sem_seq using wrep .
    have l1: "lproj \<phi>1 = a" using src1(2) sq by (simp add: lproj_def)
    have whi: "lproj (a, q(HH2 := 0), tr) HI = lproj \<phi>1 HI"
      by (metis l1 lproj_def fst_conv)
    have wlo: "lproj (a, q(HH2 := 0), tr) LO = lproj \<phi>2 LO"
      using l1 loeq by (metis lproj_def fst_conv)
    have wlow: "pproj (a, q(HH2 := 0), tr) LL2 = pproj \<phi>2 LL2"
    proof -
      have "pproj (a, q(HH2 := 0), tr) LL2 = q LL2"
        by (simp add: pproj_def)
      also have "\<dots> = c"
        using c [unfolded low_const_def, rule_format, OF qmem]
        by (simp add: pproj_def)
      finally have pe: "pproj (a, q(HH2 := 0), tr) LL2 = c" .
      have pe2: "pproj \<phi>2 LL2 = c" using m2 low_inv by (simp add: low_const_def)
      from pe pe2 show ?thesis by simp
    qed
    have key: "\<exists>\<phi>3 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S.
             lproj \<phi>3 HI = lproj \<phi>1 HI \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
             \<and> pproj \<phi>3 LL2 = pproj \<phi>2 LL2"
      apply (rule_tac x = "(a, q(HH2 := 0), tr)" in bexI)
       apply (rule conjI [OF whi conjI [OF wlo wlow]])
      apply (rule wmem)
      done
    show "\<exists>\<phi>3 \<in> sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S.
             lproj \<phi>3 HI = lproj \<phi>1 HI \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
             \<and> pproj \<phi>3 LL2 = pproj \<phi>2 LL2"
    apply (rule key)
    done
qed

theorem gni_final_havoc_rep:
  "hyper_hoare_triple (low_agree LL2 :: ((char, real) exstate) set \<Rightarrow> bool)
       (Seq (Havoc HH2) (Rep (Havoc HH2)))
       (gni_final HI LO LL2)"
proof (rule hyper_hoare_tripleI)
  fix S :: "(char, real) exstate set"
  assume pre: "low_agree LL2 S"
  then obtain c where c: "low_const LL2 c S" by (auto simp: low_agree_def)
  from c show "gni_final HI LO LL2 (sem (Seq (Havoc HH2) (Rep (Havoc HH2))) S)"
    by (rule gni_final_havoc_rep_set)
qed

end
