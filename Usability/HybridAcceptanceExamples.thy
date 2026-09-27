theory HybridAcceptanceExamples
  imports H3L_Loops.HybridLoops
begin

section \<open>Acceptance-level examples for phases 3 and 4\<close>

definition X :: var where
  "X = CHR ''x''"

definition all_pvar_eq :: "var \<Rightarrow> real \<Rightarrow> hassertion" where
  "all_pvar_eq x v = AForallState (AComp (EPVar 0 x) (=) (EConst v))"

definition every_trace_nonempty :: hassertion where
  "every_trace_nonempty = AForallState (ATrace 0 (\<lambda>tr. tr \<noteq> []))"

definition all_traces_end_with_out :: "cname \<Rightarrow> real \<Rightarrow> hassertion" where
  "all_traces_end_with_out ch v =
     AForallState (ATrace 0 (\<lambda>tr. \<exists>prefix. tr = prefix @ [OutBlock ch v]))"

definition all_traces_end_with_in :: "cname \<Rightarrow> hassertion" where
  "all_traces_end_with_in ch =
     AForallState (ATrace 0 (\<lambda>tr. \<exists>prefix v. tr = prefix @ [InBlock ch v]))"

lemma state_only_assign_const_syntactic_example:
  "\<Turnstile> {denote (AConst True)}
      (Assign X (\<lambda>_. (1::real)))
     {denote (all_pvar_eq X 1)}"
proof (rule consequence_rule)
  show "hyper_entails (denote (AConst True))
      (denote (wp_assign X (\<lambda>_. (1::real)) (all_pvar_eq X 1)))"
    unfolding hyper_entails_def denote_def wp_assign_def wp_def all_pvar_eq_def
    by (auto simp add: sem_assign pproj_def)
next
  show "hyper_entails (denote (all_pvar_eq X 1))
      (denote (all_pvar_eq X 1))"
    by (rule hyper_entails_refl)
next
  show "\<Turnstile> {denote (wp_assign X (\<lambda>_. (1::real)) (all_pvar_eq X 1))}
      (Assign X (\<lambda>_. (1::real)))
     {denote (all_pvar_eq X 1)}"
    by (rule assign_syntactic_rule)
qed

lemma send_trace_nonempty_syntactic_example:
  "\<Turnstile> {denote (AConst True)}
      (Cm (''ch''[!](\<lambda>_. (7::real))))
     {denote every_trace_nonempty}"
proof (rule consequence_rule)
  show "hyper_entails (denote (AConst True))
      (denote (wp_send ''ch'' (\<lambda>_. (7::real)) every_trace_nonempty))"
    unfolding hyper_entails_def denote_def wp_send_def wp_def every_trace_nonempty_def
    by (auto simp add: sem_send tproj_def)
next
  show "hyper_entails (denote every_trace_nonempty) (denote every_trace_nonempty)"
    by (rule hyper_entails_refl)
next
  show "\<Turnstile> {denote (wp_send ''ch'' (\<lambda>_. (7::real)) every_trace_nonempty)}
      (Cm (''ch''[!](\<lambda>_. (7::real))))
     {denote every_trace_nonempty}"
    by (rule send_syntactic_rule)
qed

lemma send_end_with_output_syntactic_example:
  "\<Turnstile> {denote (AConst True)}
      (Cm (''ch''[!](\<lambda>_. (7::real))))
     {denote (all_traces_end_with_out ''ch'' 7)}"
proof (rule consequence_rule)
  show "hyper_entails (denote (AConst True))
      (denote (wp_send ''ch'' (\<lambda>_. (7::real)) (all_traces_end_with_out ''ch'' 7)))"
    unfolding hyper_entails_def denote_def wp_send_def wp_def all_traces_end_with_out_def
    by (auto simp add: sem_send tproj_def append_assoc)
next
  show "hyper_entails (denote (all_traces_end_with_out ''ch'' 7))
      (denote (all_traces_end_with_out ''ch'' 7))"
    by (rule hyper_entails_refl)
next
  show "\<Turnstile> {denote (wp_send ''ch'' (\<lambda>_. (7::real)) (all_traces_end_with_out ''ch'' 7))}
      (Cm (''ch''[!](\<lambda>_. (7::real))))
     {denote (all_traces_end_with_out ''ch'' 7)}"
    by (rule send_syntactic_rule)
qed

lemma receive_end_with_input_syntactic_example:
  "\<Turnstile> {denote (AConst True)}
      (Cm (''ch''[?]X))
     {denote (all_traces_end_with_in ''ch'')}"
proof (rule consequence_rule)
  show "hyper_entails (denote (AConst True))
      (denote (wp_receive ''ch'' X (all_traces_end_with_in ''ch'')))"
    unfolding hyper_entails_def denote_def wp_receive_def wp_def all_traces_end_with_in_def
    by (auto simp add: sem_recv tproj_def append_assoc)
next
  show "hyper_entails (denote (all_traces_end_with_in ''ch''))
      (denote (all_traces_end_with_in ''ch''))"
    by (rule hyper_entails_refl)
next
  show "\<Turnstile> {denote (wp_receive ''ch'' X (all_traces_end_with_in ''ch''))}
      (Cm (''ch''[?]X))
     {denote (all_traces_end_with_in ''ch'')}"
    by (rule receive_syntactic_rule)
qed

definition same_pvar :: "var \<Rightarrow> syn_state hyperassertion" where
  "same_pvar x S \<longleftrightarrow> (\<forall>\<phi>\<in>S. \<forall>\<psi>\<in>S. pproj \<phi> x = pproj \<psi> x)"

definition positive_guard :: "var \<Rightarrow> fform" where
  "positive_guard x = (\<lambda>\<sigma>. \<sigma> x > 0)"

lemma wait_preserves_same_pvar_low:
  "\<Turnstile> {conj (same_pvar x) (holds_forall b)}
      (Wait e)
     {conj (same_pvar x) (low_exp b)}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume pre: "conj (same_pvar x) (holds_forall b) S"
  show "conj (same_pvar x) (low_exp b) (sem (Wait e) S)"
    using pre
    unfolding conj_def same_pvar_def holds_forall_def low_exp_def
    by (auto simp add: sem_wait pproj_def)
qed

theorem lockstep_two_run_hybrid_loop_example:
  "\<Turnstile> {conj (same_pvar X) (low_exp (positive_guard X))}
      while_cond (positive_guard X) (Wait (\<lambda>_. (1::real)))
     {conj (disj (same_pvar X) emp) (holds_forall (lnot (positive_guard X)))}"
  by (rule WhileSync_simpler) (rule wait_preserves_same_pvar_low)

definition exstate_gni :: "var \<Rightarrow> var \<Rightarrow> syn_state hyperassertion" where
  "exstate_gni high low S \<longleftrightarrow>
     (\<forall>\<phi>\<in>S. \<forall>v::real.
        \<exists>\<psi>\<in>S. pproj \<psi> high = v \<and> pproj \<phi> low = pproj \<psi> low)"

theorem havoc_high_gni_toy_example:
  assumes "high \<noteq> low"
  shows "\<Turnstile> {denote (AConst True)}
      (Havoc high)
     {exstate_gni high low}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume "denote (AConst True) S"
  show "exstate_gni high low (sem (Havoc high) S)"
    unfolding exstate_gni_def
  proof clarify
    fix \<phi> v
    assume \<phi>_in: "\<phi> \<in> sem (Havoc high) S"
    then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p tr w
      where orig: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr) \<in> S"
        and \<phi>_def: "\<phi> = (\<sigma>\<^sub>l, \<sigma>\<^sub>p(high := w), tr)"
      by (auto simp add: sem_havoc)
    let ?\<psi> = "(\<sigma>\<^sub>l, \<sigma>\<^sub>p(high := v), tr)"
    have "?\<psi> \<in> sem (Havoc high) S"
      using orig by (auto simp add: sem_havoc)
    moreover have "pproj ?\<psi> high = v \<and> pproj \<phi> low = pproj ?\<psi> low"
      using assms \<phi>_def by (simp add: pproj_def)
    ultimately show "\<exists>\<psi>\<in>sem (Havoc high) S.
        pproj \<psi> high = v \<and> pproj \<phi> low = pproj \<psi> low"
      by blast
  qed
qed

end
