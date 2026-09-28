theory HybridRefinement
  imports H3L_Pending.HybridExpressivity H3L_Semantics.Sync_Refine
begin

section \<open>Hybrid Refinement Encodings\<close>

declare [[smt_timeout = 300]]

text \<open>\<^const>\<open>ProgramHyperproperties.set_of_traces\<close> and \<^const>\<open>ProgramHyperproperties.hypersat\<close>
use different binder orders in their defining comprehensions; this bridge
gives the \<^term>\<open>hypersat\<close>-style order uniformly.\<close>

lemma set_of_traces_eq:
  "set_of_traces C = {(s, l, s') |s l s'. par_big_step C s l s'}"
  unfolding set_of_traces_def by blast

lemma resid_test:
  assumes H: "\<forall>trc sc'. P trc sc' \<longrightarrow> (\<exists>tra sa'. Q trc tra sc' sa')"
      and P0: "P trc sc'"
    shows "\<exists>sa' tra. Q trc tra sc' sa'"
  using H P0 by blast

lemma resid_concrete:
  assumes A1: "(sc, sa) \<in> (\<alpha>::(state \<times> state) set)"
      and A2: "\<forall>sc' trc. big_step (Pc::proc) (sc::state) trc sc' \<longrightarrow>
        (\<exists>sa' tra. big_step (Pa::proc) sa tra sa' \<and> tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>)"
      and A3: "big_step Pc sc trc sc'"
    shows "\<exists>sa' tra. big_step Pa sa tra sa' \<and> tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>"
  using A2 A3 by blast

lemma resid_concrete_par:
  assumes A2: "\<forall>sc' trc. par_big_step (Pc::pproc) (sc::gstate) trc sc' \<longrightarrow>
        ((sc, sa) \<in> (\<alpha>::(gstate \<times> gstate) set) \<and>
          (\<exists>sa' tra. par_big_step (Pa::pproc) (sa::gstate) tra sa' \<and> tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))"
      and A3: "par_big_step Pc sc trc sc'"
    shows "\<exists>sa' tra. par_big_step Pa sa tra sa' \<and> tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>"
  using A2 A3 by blast

lemma resid_concrete_int:
  assumes A2: "\<forall>sc' trc. par_big_step (Pc::pproc) (sc::gstate) trc sc' \<longrightarrow>
        (\<exists>sa' tra. big_step (Pa::proc) (sa::state) tra sa' \<and> tr_int (\<alpha>::(gstate \<times> state) set) trc tra \<and> (sc', sa') \<in> \<alpha>)"
      and A3: "par_big_step Pc sc trc sc'"
    shows "\<exists>sa' tra. big_step Pa sa tra sa' \<and> tr_int \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>"
  using A2 A3 by blast

definition exec_init :: "hybrid_execution \<Rightarrow> gstate" where
  "exec_init e = fst e"

definition exec_trace :: "hybrid_execution \<Rightarrow> trace" where
  "exec_trace e = fst (snd e)"

definition exec_final :: "hybrid_execution \<Rightarrow> gstate" where
  "exec_final e = snd (snd e)"

definition execution_refines ::
  "(hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool) \<Rightarrow> pproc \<Rightarrow> pproc \<Rightarrow> bool"
where
  "execution_refines R Cc Ca \<longleftrightarrow>
    (\<forall>ec \<in> set_of_traces Cc. \<exists>ea \<in> set_of_traces Ca. R ec ea)"

definition hyperproperty_refinement ::
  "(hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool) \<Rightarrow>
  hybrid_hyperproperty \<Rightarrow> hybrid_hyperproperty \<Rightarrow> bool"
where
  "hyperproperty_refinement R Hc Ha \<longleftrightarrow>
    (\<forall>Sc Sa. (\<forall>ec \<in> Sc. \<exists>ea \<in> Sa. R ec ea) \<longrightarrow> Ha Sa \<longrightarrow> Hc Sc)"

theorem execution_refinement_preserves_hypersat:
  assumes "execution_refines R Cc Ca"
      and "hyperproperty_refinement R Hc Ha"
      and "hypersat Ca Ha"
    shows "hypersat Cc Hc"
proof -
  have key: "\<forall>ec\<in>{(s, l, s') |s l s'. par_big_step Cc s l s'}.
    \<exists>ea\<in>{(s, l, s') |s l s'. par_big_step Ca s l s'}. R ec ea"
    using assms(1)[unfolded execution_refines_def set_of_traces_eq] .
  have hc: "Ha {(s, l, s') |s l s'. par_big_step Ca s l s'}"
    using assms(3)[unfolded hypersat_def] .
  from assms(2)[unfolded hyperproperty_refinement_def] key hc
  have res: "Hc {(s, l, s') |s l s'. par_big_step Cc s l s'}"
    by blast
  show "hypersat Cc Hc"
    unfolding hypersat_def by (rule res)
qed

definition refines_hyperproperty ::
  "(hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool) \<Rightarrow> pproc \<Rightarrow> hybrid_hyperproperty"
where
  "refines_hyperproperty R Ca S \<longleftrightarrow>
    (\<forall>ec \<in> S. \<exists>ea \<in> set_of_traces Ca. R ec ea)"

lemma refines_hyperproperty_hypersat_iff:
  "hypersat Cc (refines_hyperproperty R Ca) \<longleftrightarrow> execution_refines R Cc Ca"
  unfolding refines_hyperproperty_def execution_refines_def
  by (simp add: hypersat_unfold)

subsection \<open>Trace-Inclusion Refinement\<close>

definition trace_inclusion_refinement :: "pproc \<Rightarrow> pproc \<Rightarrow> bool" where
  "trace_inclusion_refinement Cc Ca \<longleftrightarrow> set_of_traces Cc \<subseteq> set_of_traces Ca"

definition trace_refines_hyperproperty :: "pproc \<Rightarrow> hybrid_hyperproperty" where
  "trace_refines_hyperproperty Ca S \<longleftrightarrow> S \<subseteq> set_of_traces Ca"

lemma trace_refines_hyperproperty_eq:
  "trace_refines_hyperproperty Ca = refines_hyperproperty (=) Ca"
  unfolding trace_refines_hyperproperty_def refines_hyperproperty_def
  by (auto intro!: ext)

lemma trace_inclusion_refinement_iff_execution_refines:
  "trace_inclusion_refinement Cc Ca \<longleftrightarrow> execution_refines (=) Cc Ca"
  unfolding trace_inclusion_refinement_def execution_refines_def by (auto simp: subset_iff)

lemma trace_refines_hyperproperty_hypersat_iff:
  "hypersat Cc (trace_refines_hyperproperty Ca) \<longleftrightarrow>
    trace_inclusion_refinement Cc Ca"
  unfolding trace_refines_hyperproperty_eq
    trace_inclusion_refinement_iff_execution_refines
  by (rule refines_hyperproperty_hypersat_iff)

theorem trace_inclusion_preserves_lower_closed:
  assumes "trace_inclusion_refinement Cc Ca"
      and "lower_closed H"
      and "hypersat Ca H"
    shows "hypersat Cc H"
proof -
  from assms(1)[unfolded trace_inclusion_refinement_def set_of_traces_eq]
  have sub: "{(s, l, s') |s l s'. par_big_step Cc s l s'}
    \<subseteq> {(s, l, s') |s l s'. par_big_step Ca s l s'}" .
  have hc: "H {(s, l, s') |s l s'. par_big_step Ca s l s'}"
    using assms(3)[unfolded hypersat_def] .
  from assms(2)[unfolded lower_closed_def] hc sub
  have res: "H {(s, l, s') |s l s'. par_big_step Cc s l s'}"
    by blast
  show "hypersat Cc H"
    unfolding hypersat_def by (rule res)
qed

subsection \<open>Encoding HRL Refinement as Program Hyperproperties\<close>

text \<open>
The original HRL judgments in \<open>hrl/Par_Refine.thy\<close> and
\<open>hrl/Sync_Refine.thy\<close> are state-indexed simulations, such as
\<open>(Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)\<close>.  The first group of encodings below
turns those judgments directly into program hyperproperties by filtering the
execution set supplied by \<open>hypersat\<close> to the concrete initial state \<open>sc\<close>.

The second group packages the same idea at program level: every reachable
concrete initial state must admit some abstract initial state that makes the
corresponding HRL simulation judgment true.
\<close>

definition hrl_single_sim_hyperproperty ::
  "state rel \<Rightarrow> proc \<Rightarrow> state \<Rightarrow> state \<Rightarrow> progran_hyperproperty"
where
  "hrl_single_sim_hyperproperty \<alpha> Pa sc sa S \<longleftrightarrow>
    (sc, sa) \<in> \<alpha> \<and>
    (\<forall>trc sc'. (State sc, trc, State sc') \<in> S \<longrightarrow>
      (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
        tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))"

lemma par_big_step_Single [simp]:
  "par_big_step (Single P) (State s) tr (State s') \<longleftrightarrow> big_step P s tr s'"
proof
  assume "par_big_step (Single P) (State s) tr (State s')"
  then show "big_step P s tr s'"
    by (auto elim: SingleE)
next
  assume "big_step P s tr s'"
  then show "par_big_step (Single P) (State s) tr (State s')"
    by (auto intro: SingleB)
qed

text \<open>Only the soundness direction of the encoding holds unconditionally:
the converse needs every concrete state to have some terminating execution,
which fails e.g. for \<open>Assume\<close> with an unsatisfiable guard.\<close>

theorem encoding_hybrid_sim_single:
  assumes sim: "(Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
  shows "hypersat (Single Pc) (hrl_single_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding hrl_single_sim_hyperproperty_def hypersat_unfold set_of_traces_eq
    hybrid_sim_single_def[symmetric]
  using sim[unfolded hybrid_sim_single_def]
  apply (auto simp: set_of_traces_eq)
  subgoal premises pre for trc sc'
    using resid_concrete[OF pre(1) pre(2) pre(3)] by blast
  done

definition hrl_par_sim_hyperproperty ::
  "gstate rel \<Rightarrow> pproc \<Rightarrow> gstate \<Rightarrow> gstate \<Rightarrow> progran_hyperproperty"
where
  "hrl_par_sim_hyperproperty \<alpha> Pa sc sa S \<longleftrightarrow>
    (\<forall>trc sc'. (sc, trc, sc') \<in> S \<longrightarrow>
      (sc, sa) \<in> \<alpha> \<and>
      (\<exists>tra sa'. par_big_step Pa sa tra sa' \<and>
        tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))"

theorem encoding_hybrid_sim_par:
  assumes sim: "(Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
  shows "hypersat Pc (hrl_par_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding hrl_par_sim_hyperproperty_def hypersat_unfold set_of_traces_eq
    hybrid_sim_par_def[symmetric]
  using sim[unfolded hybrid_sim_par_def]
  apply (auto simp: set_of_traces_eq)
  subgoal premises pre for trc sc'
    using resid_concrete_par[OF pre(1) pre(2)] by blast
  done

definition hrl_int_sim_hyperproperty ::
  "(gstate \<times> state) set \<Rightarrow> proc \<Rightarrow> gstate \<Rightarrow> state \<Rightarrow> progran_hyperproperty"
where
  "hrl_int_sim_hyperproperty \<alpha> Pa sc sa S \<longleftrightarrow>
    (sc, sa) \<in> \<alpha> \<and>
    (\<forall>trc sc'. (sc, trc, sc') \<in> S \<longrightarrow>
      (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
        tr_int \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))"

theorem encoding_hybrid_sim_int:
  assumes sim: "(Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
  shows "hypersat Pc (hrl_int_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding hrl_int_sim_hyperproperty_def hypersat_unfold set_of_traces_eq
    hybrid_sim_int_def[symmetric]
  using sim[unfolded hybrid_sim_int_def]
  apply (auto simp: set_of_traces_eq)
  subgoal premises pre for trc sc'
    using pre by (meson resid_concrete_int)
  done

lemma hrl_single_sim_hyperproperty_lower_closed:
  "lower_closed (hrl_single_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding lower_closed_def hrl_single_sim_hyperproperty_def
  by force

lemma hrl_par_sim_hyperproperty_lower_closed:
  "lower_closed (hrl_par_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding lower_closed_def hrl_par_sim_hyperproperty_def
  by force

lemma hrl_int_sim_hyperproperty_lower_closed:
  "lower_closed (hrl_int_sim_hyperproperty \<alpha> Pa sc sa)"
  unfolding lower_closed_def hrl_int_sim_hyperproperty_def
  by force

definition hrl_single_refinement ::
  "state rel \<Rightarrow> proc \<Rightarrow> proc \<Rightarrow> bool"
where
  "hrl_single_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc)) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc) \<longrightarrow>
          (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
            tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

definition hrl_single_hyperproperty ::
  "state rel \<Rightarrow> proc \<Rightarrow> progran_hyperproperty"
where
  "hrl_single_hyperproperty \<alpha> Pa S \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (State sc, trc, State sc') \<in> S) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (State sc, trc, State sc') \<in> S \<longrightarrow>
          (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
            tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

theorem encoding_hrl_single_refinement:
  "hrl_single_refinement \<alpha> Pc Pa \<longleftrightarrow>
    hypersat (Single Pc) (hrl_single_hyperproperty \<alpha> Pa)"
  unfolding hrl_single_refinement_def hrl_single_hyperproperty_def
  by (simp add: hypersat_unfold)

definition hrl_par_refinement ::
  "gstate rel \<Rightarrow> pproc \<Rightarrow> pproc \<Rightarrow> bool"
where
  "hrl_par_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<longrightarrow>
          (\<exists>tra sa'. par_big_step Pa sa tra sa' \<and>
            tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

definition hrl_par_hyperproperty ::
  "gstate rel \<Rightarrow> pproc \<Rightarrow> progran_hyperproperty"
where
  "hrl_par_hyperproperty \<alpha> Pa S \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> S) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (sc, trc, sc') \<in> S \<longrightarrow>
          (\<exists>tra sa'. par_big_step Pa sa tra sa' \<and>
            tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

theorem encoding_hrl_par_refinement:
  "hrl_par_refinement \<alpha> Pc Pa \<longleftrightarrow>
    hypersat Pc (hrl_par_hyperproperty \<alpha> Pa)"
  unfolding hrl_par_refinement_def hrl_par_hyperproperty_def
  by (simp add: hypersat_unfold)

definition hrl_int_refinement ::
  "(gstate \<times> state) set \<Rightarrow> pproc \<Rightarrow> proc \<Rightarrow> bool"
where
  "hrl_int_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<longrightarrow>
          (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
            tr_int \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

definition hrl_int_hyperproperty ::
  "(gstate \<times> state) set \<Rightarrow> proc \<Rightarrow> progran_hyperproperty"
where
  "hrl_int_hyperproperty \<alpha> Pa S \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> S) \<longrightarrow>
      (\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
        (\<forall>trc sc'. (sc, trc, sc') \<in> S \<longrightarrow>
          (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
            tr_int \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))))"

theorem encoding_hrl_int_refinement:
  "hrl_int_refinement \<alpha> Pc Pa \<longleftrightarrow>
    hypersat Pc (hrl_int_hyperproperty \<alpha> Pa)"
  unfolding hrl_int_refinement_def hrl_int_hyperproperty_def
  by (simp add: hypersat_unfold)

lemma hrl_single_refinement_iff_hybrid_sim:
  "hrl_single_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc)) \<longrightarrow>
      (\<exists>sa. (Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)))"
  unfolding hrl_single_refinement_def hybrid_sim_single_def
  by (auto simp add: set_of_traces_def elim: SingleE intro: SingleB, meson)

lemma hrl_par_refinement_iff_hybrid_sim:
  "hrl_par_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<longrightarrow>
      (\<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)))"
  unfolding hrl_par_refinement_def hybrid_sim_par_def set_of_traces_def
  by (auto simp: set_of_traces_def, force)

lemma hrl_int_refinement_iff_hybrid_sim:
  "hrl_int_refinement \<alpha> Pc Pa \<longleftrightarrow>
    (\<forall>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<longrightarrow>
      (\<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)))"
  unfolding hrl_int_refinement_def hybrid_sim_int_def set_of_traces_def
  by (auto simp: set_of_traces_def, meson)

lemma hrl_single_hyperproperty_lower_closed:
  "lower_closed (hrl_single_hyperproperty \<alpha> Pa)"
  unfolding lower_closed_def hrl_single_hyperproperty_def
  by force

lemma hrl_par_hyperproperty_lower_closed:
  "lower_closed (hrl_par_hyperproperty \<alpha> Pa)"
  unfolding lower_closed_def hrl_par_hyperproperty_def
  by force

lemma hrl_int_hyperproperty_lower_closed:
  "lower_closed (hrl_int_hyperproperty \<alpha> Pa)"
  unfolding lower_closed_def hrl_int_hyperproperty_def
  by force

lemma hybrid_sim_single_hrl_refinement:
  assumes "\<And>sc. (\<exists>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc)) \<Longrightarrow>
    \<exists>sa. (Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
  shows "hrl_single_refinement \<alpha> Pc Pa"
  unfolding hrl_single_refinement_def
proof (intro allI impI)
  fix sc
  assume reach: "\<exists>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc)"
  then obtain sa where sim: "(Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
    using assms by (metis (no_types, lifting) set_of_traces_def)
  show "\<exists>sa. (sc, sa) \<in> \<alpha> \<and>
    (\<forall>trc sc'. (State sc, trc, State sc') \<in> set_of_traces (Single Pc) \<longrightarrow>
      (\<exists>tra sa'. big_step Pa sa tra sa' \<and>
        tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>))"
  proof (intro exI[where x=sa] conjI allI impI)
    show "(sc, sa) \<in> \<alpha>"
      using sim unfolding hybrid_sim_single_def by (metis (no_types, lifting) set_of_traces_def)
  next
    fix trc sc'
    assume "(State sc, trc, State sc') \<in> set_of_traces (Single Pc)"
    then have "big_step Pc sc trc sc'"
      by (auto simp add: set_of_traces_def elim: SingleE)
    with sim show "\<exists>tra sa'. big_step Pa sa tra sa' \<and>
      tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>"
      unfolding hybrid_sim_single_def by (metis (no_types, lifting) set_of_traces_def)
  qed
qed

lemma hybrid_sim_par_hrl_refinement:
  assumes "\<And>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<Longrightarrow>
    \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
  shows "hrl_par_refinement \<alpha> Pc Pa"
  using assms
  unfolding hrl_par_refinement_def hybrid_sim_par_def set_of_traces_def
  by (auto simp: set_of_traces_def, force)

lemma hybrid_sim_int_hrl_refinement:
  assumes "\<And>sc. (\<exists>trc sc'. (sc, trc, sc') \<in> set_of_traces Pc) \<Longrightarrow>
    \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
  shows "hrl_int_refinement \<alpha> Pc Pa"
  using assms
  unfolding hrl_int_refinement_def hybrid_sim_int_def set_of_traces_def
  by (auto simp: set_of_traces_def, meson)

subsection \<open>Simulation Relations as Execution Relations\<close>

definition single_execution_rel ::
  "state rel \<Rightarrow> hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool"
where
  "single_execution_rel \<alpha> ec ea \<longleftrightarrow>
    (\<exists>sc sc' sa sa' trc tra.
      ec = (State sc, trc, State sc') \<and>
      ea = (State sa, tra, State sa') \<and>
      (sc, sa) \<in> \<alpha> \<and> tr_single \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>)"

definition par_execution_rel ::
  "gstate rel \<Rightarrow> hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool"
where
  "par_execution_rel \<alpha> ec ea \<longleftrightarrow>
    (\<exists>sc sc' sa sa' trc tra.
      ec = (sc, trc, sc') \<and>
      ea = (sa, tra, sa') \<and>
      (sc, sa) \<in> \<alpha> \<and> tr_par \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>)"

definition int_execution_rel ::
  "(gstate \<times> state) set \<Rightarrow> hybrid_execution \<Rightarrow> hybrid_execution \<Rightarrow> bool"
where
  "int_execution_rel \<alpha> ec ea \<longleftrightarrow>
    (\<exists>sc sc' sa sa' trc tra.
      ec = (sc, trc, sc') \<and>
      ea = (State sa, tra, State sa') \<and>
      (sc, sa) \<in> \<alpha> \<and> tr_int \<alpha> trc tra \<and> (sc', sa') \<in> \<alpha>)"

lemma hybrid_sim_single_execution:
  assumes "(Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
      and "big_step Pc sc trc sc'"
    shows "\<exists>sa' tra.
      big_step Pa sa tra sa' \<and>
      single_execution_rel \<alpha> (State sc, trc, State sc') (State sa, tra, State sa')"
  using assms
  unfolding hybrid_sim_single_def single_execution_rel_def
  by (metis (no_types, lifting) set_of_traces_def)

lemma hybrid_sim_single_to_set_of_traces:
  assumes "(Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
      and "(State sc, trc, State sc') \<in> set_of_traces (Single Pc)"
    shows "\<exists>ea \<in> set_of_traces (Single Pa).
      single_execution_rel \<alpha> (State sc, trc, State sc') ea"
proof -
  from assms(2) have "big_step Pc sc trc sc'"
    by (auto simp add: set_of_traces_def elim: SingleE)
  with assms(1) obtain sa' tra where
    "big_step Pa sa tra sa'"
    "single_execution_rel \<alpha> (State sc, trc, State sc') (State sa, tra, State sa')"
    using hybrid_sim_single_execution by (metis (no_types, lifting) set_of_traces_def)
  then show ?thesis
    by (auto simp add: set_of_traces_def intro: SingleB)
qed

lemma hybrid_sim_par_execution:
  assumes "(Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
      and "par_big_step Pc sc trc sc'"
    shows "\<exists>sa' tra.
      par_big_step Pa sa tra sa' \<and>
      par_execution_rel \<alpha> (sc, trc, sc') (sa, tra, sa')"
  using assms
  unfolding hybrid_sim_par_def par_execution_rel_def
  by (metis (no_types, lifting) set_of_traces_def)

lemma resid_exec_par:
  assumes A1: "(Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
      and A2: "par_big_step Pc sc trc sc'"
    shows "\<exists>sa' tra. par_big_step Pa sa tra sa' \<and>
      par_execution_rel \<alpha> (sc, trc, sc') (sa, tra, sa')"
  using A1 A2 unfolding hybrid_sim_par_def par_execution_rel_def by blast

lemma hybrid_sim_par_to_set_of_traces:
  assumes "(Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
      and "(sc, trc, sc') \<in> set_of_traces Pc"
    shows "\<exists>ea \<in> set_of_traces Pa. par_execution_rel \<alpha> (sc, trc, sc') ea"
proof -
  from assms(2)[unfolded set_of_traces_eq] have pbs: "par_big_step Pc sc trc sc'"
    by auto
  from resid_exec_par[OF assms(1) pbs] obtain sa' tra where
    e1: "par_big_step Pa sa tra sa'" and
    e2: "par_execution_rel \<alpha> (sc, trc, sc') (sa, tra, sa')"
    by blast
  have "(sa, tra, sa') \<in> set_of_traces Pa"
    unfolding set_of_traces_eq using e1 by blast
  with e2 show ?thesis
    by blast
qed

lemma hybrid_sim_par_execution_refines:
  assumes "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
    \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
  shows "execution_refines (par_execution_rel \<alpha>) Pc Pa"
  using assms hybrid_sim_par_to_set_of_traces
  unfolding execution_refines_def
  by (meson assms hybrid_sim_par_to_set_of_traces)

lemma hybrid_sim_int_execution:
  assumes "(Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
      and "par_big_step Pc sc trc sc'"
    shows "\<exists>sa' tra.
      big_step Pa sa tra sa' \<and>
      int_execution_rel \<alpha> (sc, trc, sc') (State sa, tra, State sa')"
  using assms
  unfolding hybrid_sim_int_def int_execution_rel_def
  by (metis (no_types, lifting) set_of_traces_def)

lemma hybrid_sim_int_to_set_of_traces:
  assumes "(Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
      and "(sc, trc, sc') \<in> set_of_traces Pc"
    shows "\<exists>ea \<in> set_of_traces (Single Pa). int_execution_rel \<alpha> (sc, trc, sc') ea"
proof -
  from assms(2) have "par_big_step Pc sc trc sc'"
    by (simp add: set_of_traces_def)
  with assms(1) obtain sa' tra where
    "big_step Pa sa tra sa'"
    "int_execution_rel \<alpha> (sc, trc, sc') (State sa, tra, State sa')"
    using hybrid_sim_int_execution by (metis (no_types, lifting) set_of_traces_def)
  then show ?thesis
    by (auto simp add: set_of_traces_def intro: SingleB)
qed

lemma hybrid_sim_int_execution_refines:
  assumes "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
    \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
  shows "execution_refines (int_execution_rel \<alpha>) Pc (Single Pa)"
  using assms hybrid_sim_int_to_set_of_traces
  unfolding execution_refines_def
  by (meson assms hybrid_sim_int_to_set_of_traces)

end
