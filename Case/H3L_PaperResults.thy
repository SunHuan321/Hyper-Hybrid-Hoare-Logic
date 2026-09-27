theory H3L_PaperResults
  imports H3L_Usability.HybridAcceptanceExamples H3L_Framework.HybridRefinement H3L_Core.ContinuousInv
    H3L_Usability.HybridDerivedRules H3L_Usability.HybridCompositionality H3L_Oracle.HybridOracle
    H3L_Semantics.Lander H3L_GNI.PhaseG_GNI_witness
    H3L_GNI.PhaseG_GNI_async_loop H3L_GNI.PhaseG_GNI_refinement
    H3L_GNI.PhaseG_Havoc_Syntax
begin

section \<open>Mechanized Result Index for Hyper-Hybrid Hoare Logic\<close>

subsection \<open>Core Semantics and Logic\<close>

lemmas h3l_core_soundness = Logic.soundness
lemmas h3l_core_completeness = Logic.completeness
lemmas h3l_parallel_soundness = Logic.par_hoare_sound
lemmas h3l_parallel_completeness = Logic.par_hoare_complete

subsection \<open>Phase 1: Hyperproperties and Disproving\<close>

lemmas h3l_disproving_triple = HybridDisproving.disproving_triple
lemmas h3l_parallel_disproving_triple = HybridDisproving.par_disproving_triple
lemmas h3l_k_hypersafety_implies_hypersafety =
  HybridHyperpropertyClasses.k_hypersafe_is_hypersafe
lemmas h3l_one_safety_characterization =
  HybridHyperpropertyClasses.one_safety_equiv
lemmas h3l_hypersat_unfold = HybridHyperpropertyClasses.hypersat_unfold

subsection \<open>Phase 2: Expressivity Encodings\<close>

lemmas h3l_encoding_HL = ProgramHyperproperties.encoding_HL
lemmas h3l_encoding_IL = ProgramHyperproperties.encoding_IL
lemmas h3l_encoding_CHL = HybridExpressivity.encoding_CHL
lemmas h3l_encoding_FU = HybridExpressivity.encoding_FU
lemmas h3l_RIL_semantic_target = HybridExpressivity.RIL_iff_subset
lemmas h3l_execution_refinement_preservation =
  HybridRefinement.execution_refinement_preserves_hypersat
lemmas h3l_trace_inclusion_refinement =
  HybridRefinement.trace_inclusion_refinement_iff_execution_refines
lemmas h3l_trace_inclusion_preserves_lower_closed =
  HybridRefinement.trace_inclusion_preserves_lower_closed
lemmas h3l_encoding_hybrid_sim_single =
  HybridRefinement.encoding_hybrid_sim_single
lemmas h3l_encoding_hybrid_sim_parallel =
  HybridRefinement.encoding_hybrid_sim_par
lemmas h3l_encoding_hybrid_sim_interrupt =
  HybridRefinement.encoding_hybrid_sim_int
lemmas h3l_encoding_hrl_single_refinement =
  HybridRefinement.encoding_hrl_single_refinement
lemmas h3l_encoding_hrl_parallel_refinement =
  HybridRefinement.encoding_hrl_par_refinement
lemmas h3l_encoding_hrl_interrupt_refinement =
  HybridRefinement.encoding_hrl_int_refinement
lemmas h3l_hrl_single_refinement_as_state_sims =
  HybridRefinement.hrl_single_refinement_iff_hybrid_sim
lemmas h3l_hrl_parallel_refinement_as_state_sims =
  HybridRefinement.hrl_par_refinement_iff_hybrid_sim
lemmas h3l_hrl_interrupt_refinement_as_state_sims =
  HybridRefinement.hrl_int_refinement_iff_hybrid_sim
lemmas h3l_hrl_interrupt_simulation_bridge =
  HybridRefinement.hybrid_sim_int_to_set_of_traces
lemmas h3l_hrl_interrupt_execution_refinement =
  HybridRefinement.hybrid_sim_int_execution_refines
lemmas h3l_hrl_interrupt_simulation_encoding =
  HybridRefinement.hybrid_sim_int_hrl_refinement

text \<open>
Planned Phase 2 continuations:

\<^item> full trace-aware RIL encoding with logical-variable packing,
\<^item> RFU encoding,
\<^item> RUE / k-UE encoding,
\<^item> HHL-style tag-variable encoding of trace-inclusion refinement,
\<^item> NC encoding.

These are intentionally recorded as planned items instead of unfinished theorem
statements, so the session remains free of long-term \<open>sorry\<close> placeholders.
\<close>

subsection \<open>Phase 3: Syntactic Assertion Layer\<close>

lemmas h3l_syntactic_wp_rule = HybridSyntacticAssertions.wp_rule
lemmas h3l_syntactic_sp_rule = HybridSyntacticAssertions.sp_rule
lemmas h3l_syntactic_assign = HybridSyntacticAssertions.assign_syntactic_rule
lemmas h3l_syntactic_havoc = HybridSyntacticAssertions.havoc_syntactic_rule
lemmas h3l_syntactic_assume = HybridSyntacticAssertions.assume_syntactic_rule
lemmas h3l_syntactic_wait = HybridSyntacticAssertions.wait_syntactic_rule
lemmas h3l_syntactic_send = HybridSyntacticAssertions.send_syntactic_rule
lemmas h3l_syntactic_receive = HybridSyntacticAssertions.receive_syntactic_rule
lemmas h3l_syntactic_cont = HybridSyntacticAssertions.cont_syntactic_rule
lemmas h3l_state_only_assign_example =
  HybridAcceptanceExamples.state_only_assign_const_syntactic_example
lemmas h3l_send_trace_nonempty_example =
  HybridAcceptanceExamples.send_trace_nonempty_syntactic_example
lemmas h3l_send_end_with_output_example =
  HybridAcceptanceExamples.send_end_with_output_syntactic_example
lemmas h3l_receive_end_with_input_example =
  HybridAcceptanceExamples.receive_end_with_input_syntactic_example

subsection \<open>Phase 4: Synchronized Guarded Control Flow\<close>

lemmas h3l_if_synchronized = HybridLoops.if_synchronized
lemmas h3l_while_synchronized = HybridLoops.while_synchronized
lemmas h3l_while_sync_simpler = HybridLoops.WhileSync_simpler
lemmas h3l_lockstep_two_run_hybrid_loop_example =
  HybridAcceptanceExamples.lockstep_two_run_hybrid_loop_example
lemmas h3l_havoc_high_gni_toy_example =
  HybridAcceptanceExamples.havoc_high_gni_toy_example

text \<open>
Planned Phase 4 continuations:

\<^item> while-forall-exists and while-exists witness rules,
\<^item> total-correctness synchronized while,
\<^item> trace-sensitive low-expression variants over projections of wait and
  communication blocks.
\<close>

subsection \<open>Continuous and Hybrid-Specific Rules\<close>

lemmas h3l_continuous_invariant_k = ContinuousInv.Valid_inv_k
lemmas h3l_differential_cut_k = ContinuousInv.DC_k
lemmas h3l_continuous_invariant_pair_forall = ContinuousInv.Valid_inv_Pair_forall
lemmas h3l_barrier_k = ContinuousInv.Valid_inv_barrier_s_tr_le_k

subsection \<open>Trace-Level GNI and Continuous Witnesses\<close>

lemmas h3l_trace_gni_projection = PhaseG_GNI_trace.gni_obs_imp_gni_final
lemmas h3l_trace_gni_positive = PhaseG_GNI_hybrid.gni_obs_c_havoc_cont
lemmas h3l_trace_value_leak = PhaseG_GNI_hybrid.value_leak_gni_obs_v_fails
lemmas h3l_trace_curve_leak = PhaseG_GNI_hybrid.curve_leak_gni_obs_c_fails
lemmas h3l_trace_wait_split = PhaseG_GNI_hybrid.obs_wait_split
lemmas h3l_ode_relational_invariant =
  PhaseG_GNI_hybrid.relational_ode_scalar_invariant
lemmas h3l_ode_low_curve = PhaseG_GNI_hybrid.relational_ode_curve_invariant
lemmas h3l_ode_synchronised_exit =
  PhaseG_GNI_hybrid.relational_ode_synchronised_exit
lemmas h3l_gni_loop_witness_cover = HybridLoopRules.rep_witness_cover
lemmas h3l_gni_loop_exit_rounds =
  PhaseG_GNI_trace.gni_obs_while_from_exited_round_cover
lemmas h3l_gni_loop_wf_cover = PhaseG_GNI_trace.gni_obs_while_wf_cover
lemmas h3l_gni_cont_set = PhaseG_GNI_witness.cont_gni_obs_decoupled_set
lemmas h3l_gni_parallel_obs = PhaseG_GNI_parallel.combine_obs_preserved
lemmas h3l_gni_while_wf_exit = HybridLoopRules.while_exists_wf
lemmas h3l_gni_async_loop = PhaseG_GNI_async_loop.async_loop_gni_curve
lemmas h3l_gni_async_loop_certificate =
  PhaseG_GNI_async_loop.async_loop_gni_by_certificate
lemmas h3l_gni_async_trace_difference =
  PhaseG_GNI_async_loop.async_observations_distinct
lemmas h3l_gni_syntactic_havoc = PhaseG_Havoc_Syntax.havocS_rule
lemmas h3l_gni_refinement_reverse_witness =
  PhaseG_GNI_refinement.gni_obs_c_reverse_witness_transfer

subsection \<open>Derived Usability Layer (HHL bridge and refinement drivers)\<close>

lemmas h3l_hl_bridge = HybridDerivedRules.hl_bridge
lemmas h3l_and_hl = HybridDerivedRules.h3l_and_hl
lemmas h3l_inv_single = HybridDerivedRules.h3l_inv_single
lemmas h3l_single_sim_execution_refines =
  HybridDerivedRules.single_sim_execution_refines
lemmas h3l_refine_then_verify_single =
  HybridDerivedRules.refine_then_verify_single
lemmas h3l_refine_then_verify_par =
  HybridDerivedRules.refine_then_verify_par
lemmas h3l_refine_then_verify_int =
  HybridDerivedRules.refine_then_verify_int
lemmas h3l_lander_init_sim = HybridDerivedRules.lander_init_sim
lemmas h3l_lander_refine_then_verify =
  HybridDerivedRules.lander_refine_then_verify
lemmas h3l_hl_bridge = HybridDerivedRules.hl_bridge
lemmas h3l_h3l_to_hl = HybridDerivedRules.h3l_to_hl
lemmas h3l_hl_trace_property = HybridDerivedRules.hl_trace_property
lemmas h3l_refine_trace_property = HybridDerivedRules.refine_trace_property
lemmas h3l_hl_refine_trace_property = HybridDerivedRules.hl_refine_trace_property
lemmas h3l_rep_invariant_trace = HybridDerivedRules.rep_invariant_trace
lemmas h3l_control_loop_invariant = HybridDerivedRules.control_loop_invariant
lemmas h3l_demo_const_var = HybridDerivedRules.demo_const_var

subsection \<open>Compositionality Seed and HHL Loop-Rule Ports\<close>

lemmas h3l_rule_And = HybridCompositionality.rule_And
lemmas h3l_rule_general_union = HybridCompositionality.rule_general_union
lemmas h3l_while_exists = HybridCompositionality.while_exists
lemmas h3l_rep_invariant_param = HybridCompositionality.rep_invariant_param
lemmas h3l_gni_loop_example = HybridCompositionality.gni_loop_example
lemmas h3l_h3l_Valid_inv_exemplar = HybridCompositionality.h3l_Valid_inv'

subsection \<open>Numerical Oracle Obligations (external solvers)\<close>

text \<open>
Framework-level results above are proved without \<open>sorry\<close>.  The purely
numerical facts about concrete polynomial invariants are isolated in
\<^theory_text>\<open>HybridOracle\<close> and delegated to external solvers
(SOS/SDP certificates).  \<^bold>\<open>Status: open by design\<close> -- the checklist is
\<^verbatim>\<open>grep oracle_ HybridOracle.thy\<close>:
  \<^item> \<^term>\<open>HybridOracle.oracle_Lander_discrete_step\<close> (used by lander safety)
  \<^item> \<^term>\<open>HybridOracle.oracle_Lander_barrier\<close> (used by lander safety)
\<close>

subsection \<open>Case Studies\<close>

lemmas h3l_lander_refinement = Lander.Lander_Refine

end
