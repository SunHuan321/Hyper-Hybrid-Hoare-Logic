theory PhaseG_Syntactic
  imports PhaseG_GNI_hybrid
begin

(* Assignment substitution is restricted to assertions whose state slots
   are bound.  This keeps the concrete assignment semantics intact. *)

section \<open>Syntactic weakest preconditions for Assign and Assume\<close>

text \<open>
Acceptance item 5 (HHL \<^bold>\<open>\<S>4\<close> port): replace the \<open>ASem\<close>-escaped
wp wrappers by real recursive syntactic transforms and prove them correct.

The assertion syntax is the copy from
\<^theory_text>\<open>Core/HybridSyntacticAssertions\<close> (Core is not on the session heap),
extended by two minimal constructors:

  \<^item> \<^term>\<open>EPState st e\<close>: read the whole program-state expression \<open>e\<close>
    at state slot \<open>st\<close> -- needed because our \<open>exp\<close> is a shallow embedding
    (an arbitrary state function), so assigned values cannot be re-expressed
    through single-variable reads;
  \<^item> \<^term>\<open>AFilter b A\<close>: guard filtering, giving a fully syntactic
    transform for \<^const>\<open>Assume\<close>.

\<^bold>\<open>Havoc is treated in PhaseG_Havoc_Syntax.\<close> A single-value
quantifier reading of havoc is unsound: for
\<open>A = \<forall>\<phi>1 \<phi>2. \<phi>1 x = \<phi>2 x\<close> the post-set of \<open>havoc x\<close> mixes all
values per state (so \<open>A\<close> fails), while quantifying one fresh value
uniformly would validate \<open>A\<close>.  A sound \<^term>\<open>havocS\<close> needs HHL's
per-state arbitrary-choice construction; the separate theory proves it
for a fragment that allows nested state quantifiers.
\<close>


subsection \<open>Syntax and semantics (copied, with EPState and AFilter)\<close>

type_synonym syn_state = "(var, real) exstate"

datatype hexp =
  EPVar nat var
| ELVar nat var
| EQVar nat
| EConst real
| ETraceLen nat
| EBinop hexp "real \<Rightarrow> real \<Rightarrow> real" hexp
| EFun "real \<Rightarrow> real" hexp
| EPState nat exp

datatype hassertion =
  AConst bool
| AComp hexp "real \<Rightarrow> real \<Rightarrow> bool" hexp
| ATrace nat "trace \<Rightarrow> bool"
| ATraceRel nat nat "trace \<Rightarrow> trace \<Rightarrow> bool"
| ASem "syn_state set \<Rightarrow> bool"
| AForallState hassertion
| AExistsState hassertion
| AForall hassertion
| AExists hassertion
| AAnd hassertion hassertion
| AOr hassertion hassertion
| ANot hassertion
| ATogether hassertion hassertion
| AFilter fform hassertion

fun interp_hexp :: "real list \<Rightarrow> syn_state list \<Rightarrow> hexp \<Rightarrow> real" where
  "interp_hexp vals states (EPVar st x) = pproj (states ! st) x"
| "interp_hexp vals states (ELVar st x) = lproj (states ! st) x"
| "interp_hexp vals states (EQVar x) = vals ! x"
| "interp_hexp vals states (EConst v) = v"
| "interp_hexp vals states (ETraceLen st) = real (length (tproj (states ! st)))"
| "interp_hexp vals states (EBinop e1 op e2) =
    op (interp_hexp vals states e1) (interp_hexp vals states e2)"
| "interp_hexp vals states (EFun f e) = f (interp_hexp vals states e)"
| "interp_hexp vals states (EPState st e) = e (pproj (states ! st))"

fun sat_hassertion :: "real list \<Rightarrow> syn_state list \<Rightarrow> hassertion \<Rightarrow> syn_state set \<Rightarrow> bool" where
  "sat_hassertion vals states (AConst b) S \<longleftrightarrow> b"
| "sat_hassertion vals states (AComp e1 cmp e2) S \<longleftrightarrow>
    cmp (interp_hexp vals states e1) (interp_hexp vals states e2)"
| "sat_hassertion vals states (ATrace st P) S \<longleftrightarrow> P (tproj (states ! st))"
| "sat_hassertion vals states (ATraceRel st1 st2 R) S \<longleftrightarrow>
    R (tproj (states ! st1)) (tproj (states ! st2))"
| "sat_hassertion vals states (ASem P) S \<longleftrightarrow> P S"
| "sat_hassertion vals states (AForallState A) S \<longleftrightarrow>
    (\<forall>\<phi>\<in>S. sat_hassertion vals (\<phi> # states) A S)"
| "sat_hassertion vals states (AExistsState A) S \<longleftrightarrow>
    (\<exists>\<phi>\<in>S. sat_hassertion vals (\<phi> # states) A S)"
| "sat_hassertion vals states (AForall A) S \<longleftrightarrow>
    (\<forall>v. sat_hassertion (v # vals) states A S)"
| "sat_hassertion vals states (AExists A) S \<longleftrightarrow>
    (\<exists>v. sat_hassertion (v # vals) states A S)"
| "sat_hassertion vals states (AAnd A B) S \<longleftrightarrow>
    sat_hassertion vals states A S \<and> sat_hassertion vals states B S"
| "sat_hassertion vals states (AOr A B) S \<longleftrightarrow>
    sat_hassertion vals states A S \<or> sat_hassertion vals states B S"
| "sat_hassertion vals states (ANot A) S \<longleftrightarrow>
    \<not> sat_hassertion vals states A S"
| "sat_hassertion vals states (ATogether A1 A2) S \<longleftrightarrow>
    (\<exists>S1 S2. S = S1 \<union> S2 \<and> sat_hassertion vals states A1 S1
      \<and> sat_hassertion vals states A2 S2)"
| "sat_hassertion vals states (AFilter b A) S \<longleftrightarrow>
    sat_hassertion vals states A {\<phi>\<in>S. b (pproj \<phi>)}"

definition denote :: "hassertion \<Rightarrow> syn_state hyperassertion" where
  "denote A S \<longleftrightarrow> sat_hassertion [] [] A S"

fun wf_hexp :: "nat \<Rightarrow> hexp \<Rightarrow> bool" where
  "wf_hexp n (EPVar st x) = (st < n)"
| "wf_hexp n (ELVar st x) = (st < n)"
| "wf_hexp n (EQVar x) = True"
| "wf_hexp n (EConst v) = True"
| "wf_hexp n (ETraceLen st) = (st < n)"
| "wf_hexp n (EBinop a f b) = (wf_hexp n a \<and> wf_hexp n b)"
| "wf_hexp n (EFun f a) = wf_hexp n a"
| "wf_hexp n (EPState st e) = (st < n)"

fun wf_hassertion :: "nat \<Rightarrow> hassertion \<Rightarrow> bool" where
  "wf_hassertion n (AConst b) = True"
| "wf_hassertion n (AComp a cmp b) = (wf_hexp n a \<and> wf_hexp n b)"
| "wf_hassertion n (ATrace st P) = (st < n)"
| "wf_hassertion n (ATraceRel st1 st2 R) = (st1 < n \<and> st2 < n)"
| "wf_hassertion n (ASem P) = True"
| "wf_hassertion n (AForallState A) = wf_hassertion (Suc n) A"
| "wf_hassertion n (AExistsState A) = wf_hassertion (Suc n) A"
| "wf_hassertion n (AForall A) = wf_hassertion n A"
| "wf_hassertion n (AExists A) = wf_hassertion n A"
| "wf_hassertion n (AAnd A B) = (wf_hassertion n A \<and> wf_hassertion n B)"
| "wf_hassertion n (AOr A B) = (wf_hassertion n A \<and> wf_hassertion n B)"
| "wf_hassertion n (ANot A) = wf_hassertion n A"
| "wf_hassertion n (ATogether A1 A2) =
    (wf_hassertion n A1 \<and> wf_hassertion n A2)"
| "wf_hassertion n (AFilter b A) = wf_hassertion n A"


subsection \<open>Fragments\<close>

fun pure_frag :: "hassertion \<Rightarrow> bool" where
  "pure_frag (ASem P) = False"
| "pure_frag (AForallState A) = False"
| "pure_frag (AExistsState A) = False"
| "pure_frag (AConst b) = True"
| "pure_frag (AComp e c f) = True"
| "pure_frag (ATrace st P) = True"
| "pure_frag (ATraceRel st1 st2 R) = False"
| "pure_frag (AForall A) = pure_frag A"
| "pure_frag (AExists A) = pure_frag A"
| "pure_frag (AAnd A B) = (pure_frag A \<and> pure_frag B)"
| "pure_frag (AOr A B) = (pure_frag A \<and> pure_frag B)"
| "pure_frag (ANot A) = pure_frag A"
| "pure_frag (ATogether A1 A2) = (pure_frag A1 \<and> pure_frag A2)"
| "pure_frag (AFilter b A) = pure_frag A"

fun no_asem :: "hassertion \<Rightarrow> bool" where
  "no_asem (ASem P) = False"
| "no_asem (AConst b) = True"
| "no_asem (AComp e c f) = True"
| "no_asem (ATrace st P) = True"
| "no_asem (ATraceRel st1 st2 R) = True"
| "no_asem (AForallState A) = no_asem A"
| "no_asem (AExistsState A) = no_asem A"
| "no_asem (AForall A) = no_asem A"
| "no_asem (AExists A) = no_asem A"
| "no_asem (AAnd A B) = (no_asem A \<and> no_asem B)"
| "no_asem (AOr A B) = (no_asem A \<and> no_asem B)"
| "no_asem (ANot A) = no_asem A"
| "no_asem (ATogether A1 A2) = (no_asem A1 \<and> no_asem A2)"
| "no_asem (AFilter b A) = no_asem A"

lemma pure_imp_no_asem: "pure_frag A \<Longrightarrow> no_asem A"
  by (induction A) auto


subsection \<open>Assign: substitution transform\<close>

definition assign_st :: "var \<Rightarrow> exp \<Rightarrow> syn_state \<Rightarrow> syn_state" where
  "assign_st x e \<phi> = (lproj \<phi>, (pproj \<phi>)(x := e (pproj \<phi>)), tproj \<phi>)"

fun sub_assign :: "var \<Rightarrow> exp \<Rightarrow> hexp \<Rightarrow> hexp" where
  "sub_assign x e (EPVar st y) = (if y = x then EPState st e else EPVar st y)"
| "sub_assign x e (EBinop a f b) = EBinop (sub_assign x e a) f (sub_assign x e b)"
| "sub_assign x e (EFun f a) = EFun f (sub_assign x e a)"
| "sub_assign x e (EPState st q) = EPState st (\<lambda>s. q (s(x := e s)))"
| "sub_assign x e E = E"

lemma interp_sub_assign:
  assumes wf: "wf_hexp (length states) E"
  shows "interp_hexp vals (map (assign_st x e) states) E =
    interp_hexp vals states (sub_assign x e E)"
using wf proof (induction E arbitrary: states)
  case (EPVar st y)
  then show ?case by (simp add: assign_st_def pproj_def nth_map)
next
  case (EPState st q)
  then show ?case by (simp add: assign_st_def pproj_def nth_map)
qed (auto simp: assign_st_def pproj_def lproj_def tproj_def nth_map)

fun assignS :: "var \<Rightarrow> exp \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "assignS x e (AConst b) = AConst b"
| "assignS x e (AComp a cmp b) = AComp (sub_assign x e a) cmp (sub_assign x e b)"
| "assignS x e (ATrace st P) = ATrace st P"
| "assignS x e (ATraceRel st1 st2 R) = ATraceRel st1 st2 R"
| "assignS x e (AForallState A) = AForallState (assignS x e A)"
| "assignS x e (AExistsState A) = AExistsState (assignS x e A)"
| "assignS x e (AForall A) = AForall (assignS x e A)"
| "assignS x e (AExists A) = AExists (assignS x e A)"
| "assignS x e (AAnd A B) = AAnd (assignS x e A) (assignS x e B)"
| "assignS x e (AOr A B) = AOr (assignS x e A) (assignS x e B)"
| "assignS x e (ANot A) = ANot (assignS x e A)"
| "assignS x e (ATogether A1 A2) =
    ATogether (assignS x e A1) (assignS x e A2)"
| "assignS x e (AFilter b A) =
    AFilter (\<lambda>s. b (s(x := e s))) (assignS x e A)"
| "assignS x e (ASem P) = ASem P"

lemma sem_assign_image:
  "sem (Assign x e) S = assign_st x e ` S"
  by (auto simp: sem_assign assign_st_def lproj_def pproj_def tproj_def image_iff
      split: prod.splits) (metis fst_conv snd_conv)

lemma assign_image_filter:
  "assign_st x e ` {\<phi> \<in> S. b ((pproj \<phi>)(x := e (pproj \<phi>)))} =
    {\<psi> \<in> assign_st x e ` S. b (pproj \<psi>)}"
  by (auto simp: assign_st_def pproj_def image_iff)

lemma tproj_assign_st [simp]:
  "tproj (assign_st x e \<phi>) = tproj \<phi>"
  by (simp add: assign_st_def tproj_def)

lemma sat_assignS:
  assumes na: "no_asem A" and wf: "wf_hassertion (length states) A"
  shows "sat_hassertion vals states (assignS x e A) S
       = sat_hassertion vals (map (assign_st x e) states) A (assign_st x e ` S)"
  using na wf
proof (induction A arbitrary: states S vals)
  case (AComp a cmp b)
  then show ?case by (simp add: interp_sub_assign)
next
  case (ATrace st P)
  then show ?case by (simp add: assign_st_def tproj_def nth_map)
next
  case (AForallState A)
  then show ?case by (auto simp: image_iff)
next
  case (AExistsState A)
  then show ?case by (auto simp: image_iff)
next
  case (AFilter b A)
  then show ?case by (simp add: assign_image_filter)
next
  case (ATogether A1 A2)
  let ?f = "assign_st x e"
  show ?case
  proof (simp only: assignS.simps sat_hassertion.simps, rule iffI)
    assume exS: "\<exists>S1 S2. S = S1 \<union> S2 \<and>
        sat_hassertion vals states (assignS x e A1) S1 \<and>
        sat_hassertion vals states (assignS x e A2) S2"
    then obtain S1 S2 where splitS: "S = S1 \<union> S2"
      and raw1: "sat_hassertion vals states (assignS x e A1) S1"
      and raw2: "sat_hassertion vals states (assignS x e A2) S2" by blast
    have n1: "no_asem A1" and n2: "no_asem A2"
      using ATogether.prems(1) by simp_all
    have w1: "wf_hassertion (length states) A1"
      and w2: "wf_hassertion (length states) A2"
      using ATogether.prems(2) by simp_all
    have E1: "sat_hassertion vals (map ?f states) A1 (?f ` S1)"
      using ATogether.IH(1)[OF n1 w1] raw1 by simp
    have E2: "sat_hassertion vals (map ?f states) A2 (?f ` S2)"
      using ATogether.IH(2)[OF n2 w2] raw2 by simp
    show "\<exists>T1 T2. ?f ` S = T1 \<union> T2 \<and>
        sat_hassertion vals (map ?f states) A1 T1 \<and>
        sat_hassertion vals (map ?f states) A2 T2"
      apply (rule_tac x = "?f ` S1" in exI)
      apply (rule_tac x = "?f ` S2" in exI)
      using splitS(1) E1 E2 by (simp add: image_Un)
  next
    assume exT: "\<exists>T1 T2. ?f ` S = T1 \<union> T2 \<and>
        sat_hassertion vals (map ?f states) A1 T1 \<and>
        sat_hassertion vals (map ?f states) A2 T2"
    then obtain T1 T2 where
      splitT: "?f ` S = T1 \<union> T2" and
      s1: "sat_hassertion vals (map ?f states) A1 T1" and
      s2: "sat_hassertion vals (map ?f states) A2 T2" by blast
    define P1 where "P1 = {\<phi>. \<phi> \<in> S \<and> ?f \<phi> \<in> T1}"
    define P2 where "P2 = {\<phi>. \<phi> \<in> S \<and> ?f \<phi> \<in> T2}"
    have PU: "S = P1 \<union> P2"
    proof
      show "S \<subseteq> P1 \<union> P2"
      proof
        fix \<phi> assume \<phi>S: "\<phi> \<in> S"
        then have "?f \<phi> \<in> ?f ` S" by blast
        with splitT(1) consider "?f \<phi> \<in> T1" | "?f \<phi> \<in> T2" by auto
        then show "\<phi> \<in> P1 \<union> P2"
          using \<phi>S by (cases; auto simp: P1_def P2_def)
      qed
    qed (auto simp: P1_def P2_def)
    have I1: "sat_hassertion vals (map ?f states) A1 (?f ` P1)"
    proof -
      have "?f ` P1 = T1"
      proof
        show "?f ` P1 \<subseteq> T1" by (auto simp: P1_def)
        show "T1 \<subseteq> ?f ` P1"
        proof
          fix \<psi> assume "\<psi> \<in> T1"
          then have "\<psi> \<in> ?f ` S" using splitT(1) by blast
          then obtain \<phi> where "\<phi> \<in> S" "?f \<phi> = \<psi>" by blast
          with \<open>\<psi> \<in> T1\<close> have "\<phi> \<in> P1" by (auto simp: P1_def)
          with \<open>?f \<phi> = \<psi>\<close> show "\<psi> \<in> ?f ` P1" by blast
        qed
      qed
      with s1 show ?thesis by simp
    qed
    have I2: "sat_hassertion vals (map ?f states) A2 (?f ` P2)"
    proof -
      have "?f ` P2 = T2"
      proof
        show "?f ` P2 \<subseteq> T2" by (auto simp: P2_def)
        show "T2 \<subseteq> ?f ` P2"
        proof
          fix \<psi> assume "\<psi> \<in> T2"
          then have "\<psi> \<in> ?f ` S" using splitT(1) by blast
          then obtain \<phi> where "\<phi> \<in> S" "?f \<phi> = \<psi>" by blast
          with \<open>\<psi> \<in> T2\<close> have "\<phi> \<in> P2" by (auto simp: P2_def)
          with \<open>?f \<phi> = \<psi>\<close> show "\<psi> \<in> ?f ` P2" by blast
        qed
      qed
      with s2 show ?thesis by simp
    qed
    have n1: "no_asem A1" and n2: "no_asem A2"
      using ATogether.prems(1) by simp_all
    have w1: "wf_hassertion (length states) A1"
      and w2: "wf_hassertion (length states) A2"
      using ATogether.prems(2) by simp_all
    have E1: "sat_hassertion vals states (assignS x e A1) P1"
      using ATogether.IH(1)[OF n1 w1] I1 by simp
    have E2: "sat_hassertion vals states (assignS x e A2) P2"
      using ATogether.IH(2)[OF n2 w2] I2 by simp
    from PU E1 E2
    show "\<exists>S1 S2. S = S1 \<union> S2 \<and>
        sat_hassertion vals states (assignS x e A1) S1 \<and>
        sat_hassertion vals states (assignS x e A2) S2" by blast
  qed
qed auto

theorem denote_assignS:
  assumes na: "no_asem A" and wf: "wf_hassertion 0 A"
  shows "denote (assignS x e A) S = denote A (sem (Assign x e) S)"
proof -
  have "sat_hassertion [] [] (assignS x e A) S
              = sat_hassertion [] (map (assign_st x e) []) A (assign_st x e ` S)"
    using sat_assignS[OF na] wf by simp
  then show ?thesis unfolding denote_def sem_assign_image by simp
qed

theorem assignS_rule:
  assumes na: "no_asem A" and wf: "wf_hassertion 0 A"
  shows "\<Turnstile> {denote (assignS x e A)} Assign x e {denote A}"
proof (unfold hyper_hoare_triple_def, rule allI, rule impI)
  fix S :: "(char, real) exstate set"
  assume h: "denote (assignS x e A) S"
  show "denote A (sem (Assign x e) S)"
    using h denote_assignS[OF na wf] by simp
qed


subsection \<open>Assume: filter transform\<close>

fun assumeS :: "fform \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "assumeS b (AConst c) = AConst c"
| "assumeS b (AComp e cmp f) = AComp e cmp f"
| "assumeS b (ATrace st P) = ATrace st P"
| "assumeS b (ATraceRel st1 st2 R) = ATraceRel st1 st2 R"
| "assumeS b (AForallState A) = AForallState (assumeS b A)"
| "assumeS b (AExistsState A) = AExistsState (assumeS b A)"
| "assumeS b (AForall A) = AForall (assumeS b A)"
| "assumeS b (AExists A) = AExists (assumeS b A)"
| "assumeS b (AAnd A B) = AAnd (assumeS b A) (assumeS b B)"
| "assumeS b (AOr A B) = AOr (assumeS b A) (assumeS b B)"
| "assumeS b (ANot A) = ANot (assumeS b A)"
| "assumeS b (ATogether A1 A2) =
    ATogether (assumeS b A1) (assumeS b A2)"
| "assumeS b (AFilter c A) = AFilter c (assumeS b A)"
| "assumeS b (ASem P) = ASem P"

lemma sem_assume_filter:
  "sem (Assume b) S = {\<phi> \<in> S. b (pproj \<phi>)}"
  by (auto simp: sem_assume pproj_def split: prod.splits)

theorem denote_assumeS:
  assumes na: "no_asem A"
  shows "denote (AFilter b A) S = denote A (sem (Assume b) S)"
proof -
  have "sat_hassertion [] [] (AFilter b A) S = sat_hassertion [] [] A {\<phi>\<in>S. b (pproj \<phi>)}"
    by simp
  then show ?thesis unfolding denote_def sem_assume_filter by simp
qed

theorem assumeS_rule:
  assumes na: "no_asem A"
  shows "\<Turnstile> {denote (AFilter b A)} Assume b {denote A}"
proof (unfold hyper_hoare_triple_def, rule allI, rule impI)
  fix S :: "(char, real) exstate set"
  assume "denote (AFilter b A) S"
  then show "denote A (sem (Assume b) S)"
    using denote_assumeS[OF na] by simp
qed

text \<open>\<^const>\<open>assumeS\<close> itself is the identity on the assertion structure:
filtering is absorbed by the \<^const>\<open>AFilter\<close> constructor, and the two
definitions agree on the \<open>no_asem\<close> fragment:\<close>

lemma denote_assumeS_same:
  assumes na: "no_asem A"
  shows "denote (assumeS b A) S = denote A S"
proof -
  have "assumeS b A = A" by (induction A) auto
  then show ?thesis by simp
qed

end
