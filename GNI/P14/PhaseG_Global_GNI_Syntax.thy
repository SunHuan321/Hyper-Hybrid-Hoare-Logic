theory PhaseG_Global_GNI_Syntax
  imports "H3L_GNI.PhaseG_Lander_Obs"
begin

section \<open>A minimal syntactic assertion layer for global GNI\<close>

text \<open>
\<^bold>\<open>Purpose.\<close>  This theory gives the checkable front end required by the
design note \<^emph>\<open>Global GNI assertions and the unified logic bridge\<close>
(2026-09-27): a small datatype of global assertions over runs
(\<^emph>\<open>g_run\<close> below), an interpretation \<^emph>\<open>gsat\<close> that only uses the fixed
projection/observation interface of the frozen attacker model, and the
two mandatory theorems S1 (well-formedness of the GNI assertion) and
S2 (interpretation correctness against \<^const>\<open>lander_mass_gni_norm\<close>).
The datatype has deliberately \<^bold>\<open>no\<close> semantics constructor: every
atom is one of the fixed projections below.\<close>

subsection \<open>Runs, syntax, interpretation\<close>

type_synonym g_run = "((char, real) exgstate \<times> trace)"

datatype ghassert =
    GDefined nat
  | GHighEq nat nat
  | GLowEq nat nat
  | GObsEq nat nat
  | GAnd ghassert ghassert
  | GImp ghassert ghassert
  | GAll ghassert
  | GEx ghassert

text \<open>
\<^emph>\<open>gsat\<close> interprets an assertion against a list of already chosen
runs (index \<^term>\<open>0\<close> being the most recently bound) inside a fixed
run set.  \<^const>\<open>GAll\<close>/\<^const>\<open>GEx\<close> choose from the \<^emph>\<open>same\<close> run set and
push the chosen run onto the front of the environment.  Malformed
indices (out of the environment) make atoms false, so a well-formed
assertion never depends on this guard.\<close>

fun gsat :: "g_run list \<Rightarrow> ghassert \<Rightarrow> g_run set \<Rightarrow> bool" where
  "gsat env (GDefined i) Runs \<longleftrightarrow>
    i < length env \<and>
    lander_high_input (env ! i) \<noteq> None \<and>
    lander_low_input (env ! i) \<noteq> None \<and>
    lander_final_low (fst (env ! i)) \<noteq> None"
| "gsat env (GHighEq i j) Runs \<longleftrightarrow>
    i < length env \<and> j < length env \<and>
    lander_high_input (env ! i) = lander_high_input (env ! j)"
| "gsat env (GLowEq i j) Runs \<longleftrightarrow>
    i < length env \<and> j < length env \<and>
    lander_low_input (env ! i) = lander_low_input (env ! j)"
| "gsat env (GObsEq i j) Runs \<longleftrightarrow>
    i < length env \<and> j < length env \<and>
    lander_low_observation_norm (env ! i) =
      lander_low_observation_norm (env ! j)"
| "gsat env (GAnd A B) Runs \<longleftrightarrow> gsat env A Runs \<and> gsat env B Runs"
| "gsat env (GImp A B) Runs \<longleftrightarrow> (gsat env A Runs \<longrightarrow> gsat env B Runs)"
| "gsat env (GAll A) Runs \<longleftrightarrow> (\<forall>r\<in>Runs. gsat (r # env) A Runs)"
| "gsat env (GEx A) Runs \<longleftrightarrow> (\<exists>r\<in>Runs. gsat (r # env) A Runs)"

definition gdenote :: "ghassert \<Rightarrow> g_run set \<Rightarrow> bool" where
  "gdenote A Runs = gsat [] A Runs"

subsection \<open>Well-formedness (S1)\<close>

fun wf_ghassert :: "nat \<Rightarrow> ghassert \<Rightarrow> bool" where
  "wf_ghassert n (GDefined i) \<longleftrightarrow> i < n"
| "wf_ghassert n (GHighEq i j) \<longleftrightarrow> i < n \<and> j < n"
| "wf_ghassert n (GLowEq i j) \<longleftrightarrow> i < n \<and> j < n"
| "wf_ghassert n (GObsEq i j) \<longleftrightarrow> i < n \<and> j < n"
| "wf_ghassert n (GAnd A B) \<longleftrightarrow> wf_ghassert n A \<and> wf_ghassert n B"
| "wf_ghassert n (GImp A B) \<longleftrightarrow> wf_ghassert n A \<and> wf_ghassert n B"
| "wf_ghassert n (GAll A) \<longleftrightarrow> wf_ghassert (Suc n) A"
| "wf_ghassert n (GEx A) \<longleftrightarrow> wf_ghassert (Suc n) A"

text \<open>The GNI assertion of the frozen attacker model.  After the two
universal quantifiers, index \<^term>\<open>1\<close> is the first and \<^term>\<open>0\<close> the
second run; inside the existential, \<^term>\<open>0\<close>/\<^term>\<open>1\<close>/\<^term>\<open>2\<close> are
the third/second/first run.  The definition does \<^bold>\<open>not\<close> mention
\<^const>\<open>lander_mass_gni_norm\<close>; the equivalence is theorem
\<^emph>\<open>GNI0_denote\<close> below.\<close>

definition GNI0 :: ghassert where
  "GNI0 =
    GAnd (GAll (GDefined 0))
      (GAll (GAll
        (GImp (GLowEq 1 0)
          (GEx (GAnd (GHighEq 0 2)
            (GAnd (GLowEq 0 1) (GObsEq 0 1)))))))"

theorem GNI0_wf:
  "wf_ghassert 0 GNI0"
  by (simp add: GNI0_def)

subsection \<open>Interpretation correctness (S2)\<close>

theorem GNI0_denote:
  fixes Runs :: "g_run set"
  shows "gdenote GNI0 Runs \<longleftrightarrow> lander_mass_gni_norm Runs"
proof -
  have "gdenote GNI0 Runs \<longleftrightarrow>
    (\<forall>r\<in>Runs. lander_high_input r \<noteq> None \<and>
      lander_low_input r \<noteq> None \<and>
      lander_final_low (fst r) \<noteq> None) \<and>
    (\<forall>r1\<in>Runs. \<forall>r2\<in>Runs.
      lander_low_input r1 = lander_low_input r2 \<longrightarrow>
      (\<exists>r3\<in>Runs.
        lander_high_input r3 = lander_high_input r1 \<and>
        lander_low_input r3 = lander_low_input r2 \<and>
        lander_low_observation_norm r3 = lander_low_observation_norm r2))"
    unfolding gdenote_def GNI0_def by simp
  then show ?thesis unfolding lander_mass_gni_norm_def .
qed

text \<open>Every atom of the language is a fixed projection of runs; the
interpretation of a closed assertion is therefore a pure combinator
over \<^const>\<open>lander_high_input\<close>, \<^const>\<open>lander_low_input\<close>,
\<^const>\<open>lander_final_low\<close> and \<^const>\<open>lander_low_observation_norm\<close>.
This is a design property of the grammar (no semantics constructor),
recorded here for the paper; it needs no separate theorem.\<close>

end
