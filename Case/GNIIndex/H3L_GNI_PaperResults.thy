theory H3L_GNI_PaperResults
  imports H3L_GNI.PhaseG_GNI_witness H3L_GNI.PhaseG_GNI_async_loop
    H3L_GNI.PhaseG_GNI_refinement H3L_GNI.PhaseG_Havoc_Syntax
    H3L_GNI.PhaseG_Lander_MassModel H3L_GNI.PhaseG_Lander_Mass_Consistency
    H3L_GNI.PhaseG_Lander_Obs H3L_GNI.PhaseG_Syntactic_More
    H3L_GNI.PhaseG_GNI_parallel_rich H3L_GNI.PhaseG_Lander_Mass_Witness
    H3L_GNI_WF.PhaseG_BigStep_Wf H3L_GNI_WF.PhaseG_Scale_Unbounded
    H3L_GNI_P14.PhaseG_Concrete_Positive
    H3L_GNI_P14.PhaseG_Global_GNI_Syntax
begin

section \<open>GNI results available without the Core build chain\<close>

text \<open>The unbounded mass-sensitive Lander0 has a proved three-run
normalized GNI instance over a nonempty, cross-closed initial family.
Its parallel trace transformation preserves the frozen public observation,
and a positive-time synchronized cycle witnesses substantive execution.
The earlier bounded Lander_M remains a separate candidate model.\<close>

lemmas h3l_trace_gni_projection = PhaseG_GNI_trace.gni_obs_imp_gni_final
lemmas h3l_trace_gni_positive = PhaseG_GNI_hybrid.gni_obs_c_havoc_cont
lemmas h3l_trace_value_leak = PhaseG_GNI_hybrid.value_leak_gni_obs_v_fails
lemmas h3l_trace_curve_leak = PhaseG_GNI_hybrid.curve_leak_gni_obs_c_fails
lemmas h3l_trace_wait_split = PhaseG_GNI_hybrid.obs_wait_split

lemmas h3l_ode_relational_invariant =
  PhaseG_GNI_hybrid.relational_ode_scalar_invariant
lemmas h3l_ode_low_curve =
  PhaseG_GNI_hybrid.relational_ode_curve_invariant
lemmas h3l_ode_synchronised_exit =
  PhaseG_GNI_hybrid.relational_ode_synchronised_exit
lemmas h3l_ode_three_run_surgery = PhaseG_GNI_witness.surgery_decoupled
lemmas h3l_cont_three_run_witness = PhaseG_GNI_witness.cont_witness_in_sem_decoupled
lemmas h3l_cont_set_gni = PhaseG_GNI_witness.cont_gni_obs_decoupled_set
lemmas h3l_cont_set_gni_rates = PhaseG_GNI_witness.cont_gni_obs_decoupled_set_rates

lemmas h3l_parallel_observation_left = PhaseG_GNI_parallel.combine_obs_left
lemmas h3l_parallel_observation_right = PhaseG_GNI_parallel.combine_obs_right
lemmas h3l_parallel_observation_preserved = PhaseG_GNI_parallel.combine_obs_preserved
lemmas h3l_parallel_rich_observation_left =
  PhaseG_GNI_parallel_rich.combine_rich_obs_left
lemmas h3l_parallel_rich_observation_preserved =
  PhaseG_GNI_parallel_rich.combine_rich_obs_preserved
lemmas h3l_parallel_rich_global_bridge =
  PhaseG_GNI_parallel_rich.robs_lander_global_IO

lemmas h3l_receive_now = PhaseG_GNI_comm.recv_nowI
lemmas h3l_receive_wait = PhaseG_GNI_comm.recv_waitI
lemmas h3l_interrupt_send_now = PhaseG_GNI_comm.interrupt_send_nowI
lemmas h3l_interrupt_send_wait = PhaseG_GNI_comm.interrupt_send_waitI
lemmas h3l_interrupt_recv_now = PhaseG_GNI_comm.interrupt_recv_nowI
lemmas h3l_interrupt_recv_wait = PhaseG_GNI_comm.interrupt_recv_waitI

lemmas h3l_syntactic_assign_rule = PhaseG_Syntactic.assignS_rule
lemmas h3l_syntactic_assume_rule = PhaseG_Syntactic.assumeS_rule
lemmas h3l_syntactic_havoc_rule = PhaseG_Havoc_Syntax.havocS_rule

lemmas h3l_gni_loop_witness_cover = HybridLoopRules.rep_witness_cover
lemmas h3l_gni_linking = HybridLoopRules.rule_linking
lemmas h3l_gni_while_initial_exit = HybridLoopRules.while_exists
lemmas h3l_gni_while_well_founded_exit = HybridLoopRules.while_exists_wf
lemmas h3l_gni_async_loop = PhaseG_GNI_async_loop.async_loop_gni_curve
lemmas h3l_gni_async_loop_certificate =
  PhaseG_GNI_async_loop.async_loop_gni_by_certificate
lemmas h3l_gni_async_trace_difference = PhaseG_GNI_async_loop.async_observations_distinct
lemmas h3l_gni_refinement_reverse_witness =
  PhaseG_GNI_refinement.gni_obs_c_reverse_witness_transfer
lemmas h3l_gni_loop_exit_rounds =
  PhaseG_GNI_trace.gni_obs_while_from_exited_round_cover
lemmas h3l_gni_loop_wf_cover = PhaseG_GNI_trace.gni_obs_while_wf_cover


subsection \<open>Mass-model consistency (P0.2)\<close>

lemmas h3l_mass_Fc_const = PhaseG_Lander_Mass_Consistency.mass_field_mass.Fc_const
lemmas h3l_mass_M_char = PhaseG_Lander_Mass_Consistency.mass_field_mass.M_char
lemmas h3l_mass_M_pos_margin = PhaseG_Lander_Mass_Consistency.mass_field_mass.M_pos_margin
lemmas h3l_mass_W_mono = PhaseG_Lander_Mass_Consistency.mass_field_mass.W_mono
lemmas h3l_mass_W_inv = PhaseG_Lander_Mass_Consistency.mass_field_mass.W_inv
lemmas h3l_mass_W_upper = PhaseG_Lander_Mass_Consistency.mass_field_mass.W_upper
lemmas h3l_mass_Fc_MW_invariant = PhaseG_Lander_Mass_Consistency.mass_Fc_MW_invariant
lemmas h3l_mass_Fc_MW_invariant_clock =
  PhaseG_Lander_Mass_Consistency.mass_clock_Fc_MW_invariant
lemmas h3l_mass_lie_from_inv = PhaseG_Lander_Mass_Consistency.mass_lie_from_inv
lemmas h3l_mass_low_sim = PhaseG_Lander_Mass_Consistency.mass_low_sim
lemmas h3l_mass_low_obs_sim = PhaseG_Lander_Mass_Consistency.mass_low_obs_sim

subsection \<open>Frozen observation model and family (P0.1)\<close>

lemmas h3l_obs_wait_split_rich = PhaseG_Lander_Obs.obs_lo_wait_split
lemmas h3l_obs_lo_eq_refl = PhaseG_Lander_Obs.obs_lo_eq_refl
lemmas h3l_obs_lo_eq_of_eq = PhaseG_Lander_Obs.obs_lo_eq_of_eq
lemmas h3l_obs_norm_cong_wait = PhaseG_Lander_Obs.norm_lo_cong_wait
lemmas h3l_obs_norm_split_cong = PhaseG_Lander_Obs.norm_lo_split_cong
lemmas h3l_mass_family_example_ok = PhaseG_Lander_Obs.lander_family_example_ok
lemmas h3l_mass_scale_ODE = PhaseG_Lander_Mass_Witness.mass_scale_ODEsol
lemmas h3l_mass_scale_cycle = PhaseG_Lander_Mass_Witness.mass_scale_abs_one_cycle
lemmas h3l_mass_scale_cycle_pair = PhaseG_Lander_Mass_Witness.mass_scale_abs_pair
lemmas h3l_mass_scale_loop_conditional =
  PhaseG_Lander_Mass_Witness.mass_scale_rep_by_step

subsection \<open>Well-formed concrete traces and the global IO bridge (P0.3)\<close>

lemmas h3l_wf_big_step_comm_only = PhaseG_BigStep_Wf.big_step_comm_only
lemmas h3l_wf_big_step_wnn_tr = PhaseG_BigStep_Wf.big_step_wnn_tr
lemmas h3l_wf_big_step_wf_waits = PhaseG_BigStep_Wf.big_step_wf_waits
lemmas h3l_wf_combine_wnn_tr = PhaseG_BigStep_Wf.combine_wnn_tr
lemmas h3l_wf_combine_global_IO = PhaseG_BigStep_Wf.combine_global_IO
lemmas h3l_wf_lander_global_obs_left =
  PhaseG_BigStep_Wf.lander_global_obs_left_big_step

subsection \<open>Unbounded mass scaling and concrete three-run GNI (P1.4)\<close>

lemmas h3l_unbounded_guard_scale =
  PhaseG_Scale_Unbounded.unbounded_guard_scale
lemmas h3l_mass_scale_cont_unbounded =
  PhaseG_Scale_Unbounded.mass_scale_cont_unbounded
lemmas h3l_mass_scale_abs0_cycle =
  PhaseG_Scale_Unbounded.mass_scale_abs0_one_cycle
lemmas h3l_scale_rep_by_step =
  PhaseG_Scale_Unbounded.scale_rep_by_step
lemmas h3l_abs0_all_branch_scale =
  PhaseG_Abs0_GNI.mass_scale_abs0_step
lemmas h3l_abs0_rep_scale =
  PhaseG_Abs0_GNI.mass_scale_rep_abs0
lemmas h3l_abs0_three_run_gni =
  PhaseG_Abs0_GNI.abs0_zero_family_gni
lemmas h3l_abs0_positive_cycle =
  PhaseG_Abs0_GNI.abs0_zero_family_positive_cycle
lemmas h3l_parallel_scale_combine =
  PhaseG_Parallel_Scale.combine_blocks_scale
lemmas h3l_lander0_plant_scale =
  PhaseG_Concrete_Scale.scale_ok_plant0
lemmas h3l_lander0_ctrl_scale =
  PhaseG_Concrete_Scale.scale_ok_ctrl0
lemmas h3l_lander0_parallel_scale =
  PhaseG_Concrete_Scale.lander0_scale_run
lemmas h3l_lander0_gni_intro =
  PhaseG_Concrete_GNI.lander0_mass_gni_norm
lemmas h3l_lander0_zero_family_gni =
  PhaseG_Concrete_GNI.lander0_zero_family_gni
lemmas h3l_lander0_positive_cycle =
  PhaseG_Concrete_Positive.lander0_zero_family_positive_cycle

subsection \<open>Syntactic global GNI assertion (S1/S2)\<close>

lemmas h3l_gni0_wf = PhaseG_Global_GNI_Syntax.GNI0_wf
lemmas h3l_gni0_denote = PhaseG_Global_GNI_Syntax.GNI0_denote

subsection \<open>Extended syntactic layer (P2.7, partial)\<close>

lemmas h3l_syntactic_ichoice = PhaseG_Syntactic_More.ichoiceS_rule
lemmas h3l_syntactic_skip = PhaseG_Syntactic_More.skipS_rule
lemmas h3l_syntactic_seq = PhaseG_Syntactic_More.seqS_rule
lemmas h3l_gni_synth_wf = PhaseG_Syntactic_More.wf_gni_synth
lemmas h3l_gni_synth_pure = PhaseG_Syntactic_More.pure_gni_synth
lemmas h3l_gni_synth_correct = PhaseG_Syntactic_More.denote_gni_synth
lemmas h3l_gni_synth_rule = PhaseG_Syntactic_More.gni_synth_rule
lemmas h3l_wfq_assign = PhaseG_Syntactic_More.assignS_wfq
lemmas h3l_wfq_assume = PhaseG_Syntactic_More.assumeS_wfq

end
