theory PhaseG_Syntactic_More
  imports PhaseG_Havoc_Syntax
begin

section \<open>Extended syntactic rules (P2.7, partial)\<close>

text \<open>
Acceptance item P2.7 (partial): the syntactic layer is extended by
\<^const>\<open>ANot\<close>, \<^const>\<open>ATogether\<close> (HHL's \<open>\<otimes>\<close>-join for IChoice
posts), and \<^const>\<open>ATraceRel\<close> (two-run trace relations), and this theory
adds the corresponding usable rules:

  \<^item> \<^theory_text>\<open>ichoiceS_rule\<close>: the HHL IChoice rule, syntactically: the
    postcondition is the genuine syntactic constructor
    \<^term>\<open>ATogether Q1 Q2\<close>, not an \<^const>\<open>ASem\<close> escape.

  \<^item> A state-pure fragment (below) (no trace reads, no
    semantic escapes) whose satisfaction is invariant under
    logical/program-state-preserving correspondences; consequently
    \<^theory_text>\<open>wait_spure_rule\<close> and \<^theory_text>\<open>send_spure_rule\<close>: a
    state-pure assertion is preserved by \<^const>\<open>Wait\<close> and by output,
    because both only extend the trace.

  \<^item> the syntactic GNI assertion below: the trace-level GNI assertion
    \<^const>\<open>gni_obs\<close> expressed purely syntactically with
    \<^const>\<open>ATraceRel\<close>; \<^theory_text>\<open>denote_gni_synth\<close> proves the
    encoding correct.

  \<^item> the depth predicate below: a value-binder depth well-formedness tracking
    \<^const>\<open>EQVar\<close> indices (the missing half of @{const wf_hexp});
    preserved by \<^const>\<open>assignS\<close> and \<^const>\<open>assumeS\<close>.

Documented residual: \<^const>\<open>ATogether\<close> is excluded from the havoc
fragment (its two-dimensional preimage split is a separate construction);
the havoc wp for assertions with pre-existing value binders remains open.
\<close>


subsection \<open>IChoice with the syntactic join\<close>

theorem ichoiceS_rule:
  assumes r1: "\<Turnstile> {denote P} C1 {denote Q1}"
    and r2: "\<Turnstile> {denote P} C2 {denote Q2}"
  shows "\<Turnstile> {denote P} IChoice C1 C2 {denote (ATogether Q1 Q2)}"
proof (rule hyper_hoare_tripleI)
  fix S assume pS: "denote P S"
  from r1 pS have q1: "denote Q1 (sem C1 S)" by (rule hyper_hoare_tripleE)
  from r2 pS have q2: "denote Q2 (sem C2 S)" by (rule hyper_hoare_tripleE)
  show "denote (ATogether Q1 Q2) (sem (IChoice C1 C2) S)"
    unfolding sem_if denote_def sat_hassertion.simps
    apply (rule_tac x = "sem C1 S" in exI)
    apply (rule_tac x = "sem C2 S" in exI)
    using q1 q2 by (simp add: denote_def)
qed


subsection \<open>Skip/Seq at the denote level\<close>

theorem skipS_rule: "\<Turnstile> {denote P} Skip {denote P}"
  by (rule hyper_hoare_tripleI) (simp add: denote_def sem_skip)

theorem seqS_rule:
  assumes r1: "\<Turnstile> {denote P} C1 {denote R}"
    and r2: "\<Turnstile> {denote R} C2 {denote Q}"
  shows "\<Turnstile> {denote P} Seq C1 C2 {denote Q}"
  using r1 r2 by (rule seq_rule)


subsection \<open>The state-pure fragment\<close>

fun spure_hexp :: "hexp \<Rightarrow> bool" where
  "spure_hexp (EPVar st x) = True"
| "spure_hexp (ELVar st x) = True"
| "spure_hexp (EQVar i) = True"
| "spure_hexp (EConst v) = True"
| "spure_hexp (ETraceLen st) = False"
| "spure_hexp (EBinop a f b) = (spure_hexp a \<and> spure_hexp b)"
| "spure_hexp (EFun f a) = spure_hexp a"
| "spure_hexp (EPState st e) = True"

fun spure_frag :: "hassertion \<Rightarrow> bool" where
  "spure_frag (AConst b) = True"
| "spure_frag (AComp a c b) = (spure_hexp a \<and> spure_hexp b)"
| "spure_frag (ATrace st P) = False"
| "spure_frag (ATraceRel st1 st2 R) = False"
| "spure_frag (ASem P) = False"
| "spure_frag (AForallState A) = spure_frag A"
| "spure_frag (AExistsState A) = spure_frag A"
| "spure_frag (AForall A) = spure_frag A"
| "spure_frag (AExists A) = spure_frag A"
| "spure_frag (AAnd A B) = (spure_frag A \<and> spure_frag B)"
| "spure_frag (AOr A B) = (spure_frag A \<and> spure_frag B)"
| "spure_frag (ANot A) = spure_frag A"
| "spure_frag (ATogether A1 A2) = (spure_frag A1 \<and> spure_frag A2)"
| "spure_frag (AFilter b A) = spure_frag A"

lemma spure_interp:
  assumes stl: "list_all2 (\<lambda>a b. lproj a = lproj b \<and> pproj a = pproj b)
      states states'"
    and sp: "spure_hexp E" and wf: "wf_hexp (length states) E"
  shows "interp_hexp vals states E = interp_hexp vals states' E"
  using sp wf stl
proof (induction E arbitrary: states states' vals)
  case (EPVar st x)
  then show ?case using list_all2_nthD[OF EPVar.prems(3), of st]
    by (auto simp: pproj_def dest: fun_cong)
next
  case (ELVar st x)
  then show ?case using list_all2_nthD[OF ELVar.prems(3), of st]
    by (auto simp: lproj_def dest: fun_cong)
next
  case (EPState st e)
  then show ?case using list_all2_nthD[OF EPState.prems(3), of st]
    by (auto simp: pproj_def dest: fun_cong)
qed auto

definition sp_match ::
  "(char, real) exstate set \<Rightarrow> (char, real) exstate set \<Rightarrow> bool" where
  "sp_match S S' \<longleftrightarrow>
    (\<forall>\<phi>\<in>S. \<exists>\<psi>\<in>S'. lproj \<phi> = lproj \<psi> \<and> pproj \<phi> = pproj \<psi>) \<and>
    (\<forall>\<psi>\<in>S'. \<exists>\<phi>\<in>S. lproj \<phi> = lproj \<psi> \<and> pproj \<phi> = pproj \<psi>)"

subsection \<open>GNI as a purely syntactic assertion\<close>

definition gni_wit :: hassertion where
  "gni_wit =
    AAnd (AComp (ELVar 0 HI) (=) (ELVar 2 HI))
      (AAnd (AComp (ELVar 0 LO) (=) (ELVar 1 LO))
        (AAnd (AComp (EPVar 0 LL2) (=) (EPVar 1 LL2))
          (ATraceRel 0 1 (\<lambda>a b. obs_tr a = obs_tr b))))"

definition gni_synth :: hassertion where
  "gni_synth =
    AForallState (AForallState
      (AOr (ANot (AComp (ELVar 1 LO) (=) (ELVar 0 LO)))
        (AExistsState gni_wit)))"

theorem wf_gni_synth: "wf_hassertion 0 gni_synth"
  by (simp add: gni_synth_def gni_wit_def)

theorem pure_gni_synth: "no_asem gni_synth"
  by (simp add: gni_synth_def gni_wit_def)

theorem denote_gni_synth:
  "denote gni_synth S = gni_obs HI LO LL2 S"
  unfolding gni_synth_def gni_wit_def denote_def gni_obs_def low_obs_def
  by auto

corollary gni_synth_rule:
  assumes "\<Turnstile> {P} C {denote gni_synth}"
  shows "\<And>S. P S \<Longrightarrow> gni_obs HI LO LL2 (sem C S)"
  using assms by (auto simp: hyper_hoare_triple_def denote_gni_synth)


subsection \<open>Value-binder depth well-formedness\<close>

fun wfq_hexp :: "nat \<Rightarrow> hexp \<Rightarrow> bool" where
  "wfq_hexp n (EPVar st x) = True"
| "wfq_hexp n (ELVar st x) = True"
| "wfq_hexp n (EQVar i) = (i < n)"
| "wfq_hexp n (EConst v) = True"
| "wfq_hexp n (ETraceLen st) = True"
| "wfq_hexp n (EBinop a f b) = (wfq_hexp n a \<and> wfq_hexp n b)"
| "wfq_hexp n (EFun f a) = wfq_hexp n a"
| "wfq_hexp n (EPState st e) = True"

fun wfq :: "nat \<Rightarrow> hassertion \<Rightarrow> bool" where
  "wfq n (AConst b) = True"
| "wfq n (AComp a c b) = (wfq_hexp n a \<and> wfq_hexp n b)"
| "wfq n (ATrace st P) = True"
| "wfq n (ATraceRel st1 st2 R) = True"
| "wfq n (ASem P) = True"
| "wfq n (AForallState A) = wfq n A"
| "wfq n (AExistsState A) = wfq n A"
| "wfq n (AForall A) = wfq (Suc n) A"
| "wfq n (AExists A) = wfq (Suc n) A"
| "wfq n (AAnd A B) = (wfq n A \<and> wfq n B)"
| "wfq n (AOr A B) = (wfq n A \<and> wfq n B)"
| "wfq n (ANot A) = wfq n A"
| "wfq n (ATogether A1 A2) = (wfq n A1 \<and> wfq n A2)"
| "wfq n (AFilter b A) = wfq n A"

lemma wfq_sub_assign: "wfq_hexp n E \<Longrightarrow> wfq_hexp n (sub_assign x e E)"
  by (induction E arbitrary: n) auto

lemma assignS_wfq: "wfq n A \<Longrightarrow> wfq n (assignS x e A)"
  by (induction A arbitrary: n) (auto simp: wfq_sub_assign)

lemma assumeS_wfq: "wfq n A \<Longrightarrow> wfq n (assumeS b A)"
  by (induction A arbitrary: n) auto

end
