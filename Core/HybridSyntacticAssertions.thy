theory HybridSyntacticAssertions
  imports Logic
begin

section \<open>Lightweight Syntactic Assertions for H3L\<close>

text \<open>
This theory provides a shallow syntactic layer for the common real-valued
instantiation of logical variables.  The semantic escape hatch \<open>ASem\<close> keeps
the layer useful for hybrid commands whose exact weakest preconditions mention
traces or ODE solutions.
\<close>

type_synonym syn_state = "(var, real) exstate"
type_synonym real_binop = "real \<Rightarrow> real \<Rightarrow> real"
type_synonym real_comp = "real \<Rightarrow> real \<Rightarrow> bool"

datatype hexp =
  EPVar nat var
| ELVar nat var
| EQVar nat
| EConst real
| ETraceLen nat
| EBinop hexp real_binop hexp
| EFun "real \<Rightarrow> real" hexp

datatype hassertion =
  AConst bool
| AComp hexp real_comp hexp
| ATrace nat "trace \<Rightarrow> bool"
| ASem "syn_state set \<Rightarrow> bool"
| AForallState hassertion
| AExistsState hassertion
| AForall hassertion
| AExists hassertion
| AAnd hassertion hassertion
| AOr hassertion hassertion

fun interp_hexp :: "real list \<Rightarrow> syn_state list \<Rightarrow> hexp \<Rightarrow> real" where
  "interp_hexp vals states (EPVar st x) = pproj (states ! st) x"
| "interp_hexp vals states (ELVar st x) = lproj (states ! st) x"
| "interp_hexp vals states (EQVar x) = vals ! x"
| "interp_hexp vals states (EConst v) = v"
| "interp_hexp vals states (ETraceLen st) = real (length (tproj (states ! st)))"
| "interp_hexp vals states (EBinop e1 op e2) =
    op (interp_hexp vals states e1) (interp_hexp vals states e2)"
| "interp_hexp vals states (EFun f e) = f (interp_hexp vals states e)"

fun sat_hassertion :: "real list \<Rightarrow> syn_state list \<Rightarrow> hassertion \<Rightarrow> syn_state set \<Rightarrow> bool" where
  "sat_hassertion vals states (AConst b) S \<longleftrightarrow> b"
| "sat_hassertion vals states (AComp e1 cmp e2) S \<longleftrightarrow>
    cmp (interp_hexp vals states e1) (interp_hexp vals states e2)"
| "sat_hassertion vals states (ATrace st P) S \<longleftrightarrow> P (tproj (states ! st))"
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

definition denote :: "hassertion \<Rightarrow> syn_state hyperassertion" where
  "denote A S \<longleftrightarrow> sat_hassertion [] [] A S"

definition hnot :: "hassertion \<Rightarrow> hassertion" where
  "hnot A = ASem (\<lambda>S. \<not> denote A S)"

definition himp :: "hassertion \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "himp A B = AOr (hnot A) B"

lemma denote_ASem [simp]:
  "denote (ASem P) S \<longleftrightarrow> P S"
  by (simp add: denote_def)

lemma denote_hnot [simp]:
  "denote (hnot A) S \<longleftrightarrow> \<not> denote A S"
  by (simp add: hnot_def)

lemma denote_himp [simp]:
  "denote (himp A B) S \<longleftrightarrow> (denote A S \<longrightarrow> denote B S)"
  by (simp add: himp_def denote_def hnot_def)

subsection \<open>Weakest and Strongest Syntactic Wrappers\<close>

definition wp :: "proc \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp C A = ASem (\<lambda>S. denote A (sem C S))"

definition sp :: "proc \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "sp C A = ASem (\<lambda>S. \<exists>S0. denote A S0 \<and> S = sem C S0)"

theorem wp_rule:
  "\<Turnstile> {denote (wp C A)} C {denote A}"
  by (simp add: hyper_hoare_triple_def wp_def)

theorem sp_rule:
  "\<Turnstile> {denote A} C {denote (sp C A)}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume "denote A S"
  then show "denote (sp C A) (sem C S)"
    unfolding sp_def by (auto intro!: exI[of _ S])
qed

definition wp_assign :: "var \<Rightarrow> exp \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_assign x e A = wp (Assign x e) A"

definition wp_havoc :: "var \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_havoc x A = wp (Havoc x) A"

definition wp_assume :: "fform \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_assume b A = wp (Assume b) A"

definition wp_wait :: "exp \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_wait e A = wp (Wait e) A"

definition wp_send :: "cname \<Rightarrow> exp \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_send ch e A = wp (Cm (ch[!]e)) A"

definition wp_receive :: "cname \<Rightarrow> var \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_receive ch x A = wp (Cm (ch[?]x)) A"

definition wp_cont :: "ODE \<Rightarrow> fform \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "wp_cont ode b A = wp (Cont ode b) A"

theorem assign_syntactic_rule:
  "\<Turnstile> {denote (wp_assign x e A)} (Assign x e) {denote A}"
  by (simp add: wp_assign_def wp_rule)

theorem havoc_syntactic_rule:
  "\<Turnstile> {denote (wp_havoc x A)} (Havoc x) {denote A}"
  by (simp add: wp_havoc_def wp_rule)

theorem assume_syntactic_rule:
  "\<Turnstile> {denote (wp_assume b A)} (Assume b) {denote A}"
  by (simp add: wp_assume_def wp_rule)

theorem wait_syntactic_rule:
  "\<Turnstile> {denote (wp_wait e A)} (Wait e) {denote A}"
  by (simp add: wp_wait_def wp_rule)

theorem send_syntactic_rule:
  "\<Turnstile> {denote (wp_send ch e A)} (Cm (ch[!]e)) {denote A}"
  by (simp add: wp_send_def wp_rule)

theorem receive_syntactic_rule:
  "\<Turnstile> {denote (wp_receive ch x A)} (Cm (ch[?]x)) {denote A}"
  by (simp add: wp_receive_def wp_rule)

theorem cont_syntactic_rule:
  "\<Turnstile> {denote (wp_cont ode b A)} (Cont ode b) {denote A}"
  by (simp add: wp_cont_def wp_rule)

theorem seq_syntactic_rule:
  assumes "\<Turnstile> {denote A} C1 {denote B}"
      and "\<Turnstile> {denote B} C2 {denote D}"
    shows "\<Turnstile> {denote A} (C1; C2) {denote D}"
  using assms by (rule seq_rule)

theorem choice_syntactic_rule:
  assumes "\<Turnstile> {denote A} C1 {denote B1}"
      and "\<Turnstile> {denote A} C2 {denote B2}"
    shows "\<Turnstile> {denote A} (IChoice C1 C2) {join (denote B1) (denote B2)}"
  using assms by (rule if_rule)

end
