theory PhaseG_Global_GNI_Bridge
  imports "H3L_Core.Logic"
    "H3L_GNI_P14.PhaseG_Concrete_Positive"
    "H3L_GNI_P14.PhaseG_Global_GNI_Syntax"
begin

section \<open>The concrete lander GNI inside the unified logic\<close>

text \<open>
\<^bold>\<open>Purpose.\<close>  Bridge theory of the design note \<^emph>\<open>Global GNI
assertions and the unified logic bridge\<close> (2026-09-27).  It imports
the Core logic and the GNI side session at the \<^bold>\<open>same\<close> semantic
types (both descend from H3L_Semantics) and proves the two mandatory
theorems B1 and B2: the main result as a Core \<^emph>\<open>parallel\<close> hyper
Hoare triple over the syntactic assertion, and the nonempty,
positive-cycle example run.  No semantics is redefined here.\<close>

subsection \<open>B1: the main result as a parallel hyper Hoare triple\<close>

definition Init0 :: "((char, real) exgstate) set \<Rightarrow> bool" where
  "Init0 S \<longleftrightarrow> S \<noteq> {} \<and> lander0_initial_cross S"

theorem lander0_global_GNI:
  "\<Turnstile>\<^sub>P {Init0} Lander0 {gdenote GNI0}"
  unfolding par_hyper_hoare_triple_def
proof (intro allI impI)
  fix S :: "((char, real) exgstate) set"
  assume init: "Init0 S"
  then have cross: "lander0_initial_cross S"
    unfolding Init0_def by simp
  have gni: "lander_mass_gni_norm (par_sem Lander0 S)"
    by (rule lander0_mass_gni_norm[OF cross])
  show "gdenote GNI0 (par_sem Lander0 S)"
    by (rule GNI0_denote[THEN iffD2, OF gni])
qed

subsection \<open>B2: the case is not vacuously true\<close>

theorem lander0_global_GNI_example:
  "Init0 lander0_zero_family \<and>
   gdenote GNI0 (par_sem Lander0 lander0_zero_family) \<and>
   (\<exists>r\<in>par_sem Lander0 lander0_zero_family.
      \<exists>p rdy rest. 0 < Period \<and>
        snd r = WaitBlk Period p rdy # rest)"
proof (intro conjI)
  show "Init0 lander0_zero_family"
    unfolding Init0_def
    using lander0_zero_family_nonempty lander0_zero_family_cross by simp
  show "gdenote GNI0 (par_sem Lander0 lander0_zero_family)"
    by (rule GNI0_denote[THEN iffD2, OF lander0_zero_family_gni])
  show "\<exists>r\<in>par_sem Lander0 lander0_zero_family.
      \<exists>p rdy rest. 0 < Period \<and>
        snd r = WaitBlk Period p rdy # rest"
    by (rule lander0_zero_family_positive_cycle)
qed

end
