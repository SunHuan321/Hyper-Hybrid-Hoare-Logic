theory HybridDerivedRules
  imports H3L_Framework.HybridRefinement H3L_Core.ContinuousInv H3L_Semantics.ComplementlemmaHHL H3L_Semantics.Lander
begin

section \<open>A usable derived-rule layer for H3L\<close>

text \<open>
The core proof system of H3L (theory \<^theory_text>\<open>Logic\<close>) is stated over semantic
hyper-assertions, so using it directly forces proofs to unfold \<^const>\<open>sem\<close>
and \<^const>\<open>big_step\<close> all the time.  This theory provides the middle layer
that case studies should actually reason with:

  \<^item> a bridge \<^const>\<open>hl_lift\<close> that reuses every classical HHL triple
    (including the whole gGHL rule library in
    \<^theory_text>\<open>hhl/ComplementlemmaHHL\<close> and \<^theory_text>\<open>hhl/ContinuousInvHHL\<close>)
    as an H3L hyper-triple;
  \<^item> a conjunction combator \<^term>\<open>h3l_and_hl\<close> that mixes HHL-derived
    single-execution facts with genuinely hyper facts;
  \<^item> a tag-free single-run ODE invariant rule \<^term>\<open>h3l_inv_single\<close>
    (no logical-variable bookkeeping, no reference to a fixed input trace);
  \<^item> refinement drivers that turn an hrl simulation into
    hyperproperty transfer, so the intended workflow
    \<^emph>\<open>refine first, then verify the abstract model\<close> is one rule application.

For two-run (robustness / agreement) reasoning, use the existing
\<^term>\<open>ContinuousInv.Valid_inv_Pair_forall\<close> and
\<^term>\<open>ContinuousInv.Valid_inv_barrier_s_tr_le_k\<close>.
\<close>


subsection \<open>Bridging classical HHL triples into H3L\<close>

definition hl_lift :: "assn \<Rightarrow> (('lvar, 'lval) exstate) hyperassertion" where
  "hl_lift P = over_approx (lift_assn P)"

lemma HL_sem_subset:
  assumes "HL P C Q"
  shows "sem C P \<subseteq> Q"
proof
  fix \<phi> assume "\<phi> \<in> sem C P"
  then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p' l l' where "\<phi> = (\<sigma>\<^sub>l, \<sigma>\<^sub>p', l @ l')"
    "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> P" "big_step C \<sigma>\<^sub>p l' \<sigma>\<^sub>p'"
    using sem_def[of C P] by auto
  with assms show "\<phi> \<in> Q" unfolding HL_def by auto
qed

text \<open>Every HHL triple is an H3L triple over the lifted assertion.\<close>

theorem hl_bridge:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {P} C {Q}"
  shows "\<Turnstile> {hl_lift P} C {hl_lift Q}"
proof (rule hyper_hoare_tripleI)
  fix S assume "hl_lift P S"
  then have sub: "S \<subseteq> lift_assn P" by (simp add: hl_lift_def over_approx_def)
  from assms have HL: "HL (lift_assn P) C (lift_assn Q)"
    by (simp add: HL_encode_triple)
  from HL_sem_subset[OF HL] sub have "sem C S \<subseteq> lift_assn Q"
    using sem_monotonic by blast
  then show "hl_lift Q (sem C S)" by (simp add: hl_lift_def over_approx_def)
qed

text \<open>
HHL-derived facts compose with hyper facts: prove the single-execution part
with the classical rule library and the multi-execution part with the hyper
rules, and conjoin both.
\<close>

theorem h3l_and_hl:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {P} C {Q}"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {conj (hl_lift P) P'} C {conj (hl_lift Q) Q'}"
proof (rule hyper_hoare_tripleI)
  fix S assume S: "conj (hl_lift P) P' S"
  then have sub: "S \<subseteq> lift_assn P" and p': "P' S"
    by (auto simp: conj_def hl_lift_def over_approx_def)
  from assms(1) have HL: "HL (lift_assn P) C (lift_assn Q)"
    by (simp add: HL_encode_triple)
  from HL_sem_subset[OF HL] sub have "sem C S \<subseteq> lift_assn Q"
    using sem_monotonic by blast
  moreover have "Q' (sem C S)"
    using hyper_hoare_tripleE[OF assms(2) p'] .
  ultimately show "conj (hl_lift Q) Q' (sem C S)"
    by (simp add: conj_def hl_lift_def over_approx_def)
qed


subsection \<open>A tag-free single-run ODE invariant rule\<close>

text \<open>
\<^term>\<open>Valid_inv\<close> in \<^theory_text>\<open>hhl/ContinuousInvHHL\<close> proves the same mathematical
fact, but its precondition pins the input trace to a parameter \<^term>\<open>tra\<close>,
which is awkward inside hyper-triples.  The rule below speaks directly about
all executions of a set: if every execution starts in the domain \<open>b\<close> and on
the level set \<^term>\<open>inv = r\<close>, then every execution follows one solution for
some positive duration and stays on the level set throughout the flow.
\<close>

theorem h3l_inv_single:
  fixes inv :: "state \<Rightarrow> real"
  assumes diff: "\<forall>x. ((\<lambda>v. inv (vec2state v)) has_derivative g' x) (at x within UNIV)"
      and lie: "\<forall>s. b s \<longrightarrow> g' (state2vec s) (ODE2Vec ode s) = 0"
    shows "\<Turnstile> {\<lambda>S. (\<forall>\<phi>\<in>S. b (pproj \<phi>)) \<and> (\<forall>\<phi>\<in>S. inv (pproj \<phi>) = r)}
       Cont ode b
      {\<lambda>S. \<forall>\<phi>\<in>S. \<exists>p d tr0. tproj \<phi> = tr0 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]
        \<and> 0 < d \<and> p d = pproj \<phi> \<and> (\<forall>t\<in>{0..d}. inv (p t) = r)}"
proof (rule hyper_hoare_tripleI)
  fix S assume pre: "(\<forall>\<phi>\<in>S. b (pproj \<phi>)) \<and> (\<forall>\<phi>\<in>S. inv (pproj \<phi>) = r)"
  show "\<forall>\<phi>\<in>sem (Cont ode b) S. \<exists>p d tr0. tproj \<phi> = tr0 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]
        \<and> 0 < d \<and> p d = pproj \<phi> \<and> (\<forall>t\<in>{0..d}. inv (p t) = r)"
  proof
    fix \<phi>' assume mem: "\<phi>' \<in> sem (Cont ode b) S"
    then obtain \<sigma>\<^sub>p tr0 tr1 where inS: "(fst \<phi>', \<sigma>\<^sub>p, tr0) \<in> S"
      "big_step (Cont ode b) \<sigma>\<^sub>p tr1 (fst (snd \<phi>'))" "snd (snd \<phi>') = tr0 @ tr1"
      by (meson in_sem)
    from inS pre have b0: "b \<sigma>\<^sub>p" and inv0: "inv \<sigma>\<^sub>p = r" by auto
    from inS(2) show "\<exists>p d tr0. tproj \<phi>' = tr0 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]
        \<and> 0 < d \<and> p d = pproj \<phi>' \<and> (\<forall>t\<in>{0..d}. inv (p t) = r)"
    proof (rule contE)
      assume nb: "\<not> b \<sigma>\<^sub>p"
      from nb b0 show ?thesis by simp
    next
      fix d p assume tr1: "tr1 = [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"
        and d0: "0 < d" and sol: "ODEsol ode p d" and pin: "p 0 = \<sigma>\<^sub>p"
        and hold: "\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)"
        and pex: "\<not> b (p d)" and pfin: "p d = fst (snd \<phi>')"
      have 1: "\<forall>t\<in>{0..d}. ((\<lambda>t. inv (p t)) has_derivative
          (\<lambda>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)))) (at t within {0..d})"
        using diff sol chainrule[of inv "\<lambda>x. g' (state2vec x)" ode p d] by auto
      have 2: "\<forall>s. g' (state2vec (p t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec ode (p t))
                 = s *\<^sub>R g' (state2vec (p t)) (1 *\<^sub>R ODE2Vec ode (p t))" if "t\<in>{0..d}" for t
        using 1 unfolding has_derivative_def bounded_linear_def
        using that linear_iff[of "(\<lambda>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)))"]
        by blast
      have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
      have 4: "\<forall>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t))
                 = s *\<^sub>R g' (state2vec (p t)) (1 *\<^sub>R ODE2Vec ode (p t))" if "t\<in>{0..d}" for t
        using 2 3 that by auto
      have 5: "\<forall>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)) = 0" if "t\<in>{0..<d}" for t
        using 4 lie that hold by auto
      have invflow: "\<And>t. t \<in> {0..d} \<Longrightarrow> inv (p t) = r"
      proof -
        fix t assume t: "t \<in> {0..d}"
        have "inv (p 0) = r" using pin inv0 by simp
        then show "inv (p t) = r"
          using mvt_real_eq[of d "(\<lambda>t. inv (p t))"
              "\<lambda>t. (\<lambda>s. g' (state2vec (p t)) (s *\<^sub>R ODE2Vec ode (p t)))" t]
          using 1 5 t d0 by auto
      qed
      show ?thesis
        apply (rule_tac x = p in exI, rule_tac x = d in exI, rule_tac x = tr0 in exI)
        using tr1 inS(3) pfin d0 invflow by (auto simp: pproj_def tproj_def)
    qed
  qed
qed


subsection \<open>Refinement drivers: refine first, then verify the abstraction\<close>

text \<open>
One application turns an hrl simulation (as proved for the lunar lander in
\<^theory_text>\<open>hrl/Lander\<close>) into an execution-level refinement; a second application
transfers hyperproperty satisfaction from the abstract to the concrete model.
\<close>

corollary single_sim_execution_refines:
  assumes init_sim: "\<And>sc sa. (sc, sa) \<in> \<alpha> \<Longrightarrow> (Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
      and cover: "\<And>sc trc sc'. big_step Pc sc trc sc' \<Longrightarrow> \<exists>sa. (sc, sa) \<in> \<alpha>"
  shows "execution_refines (single_execution_rel \<alpha>) (Single Pc) (Single Pa)"
proof (unfold execution_refines_def, rule ballI)
  fix ec assume ec: "ec \<in> set_of_traces (Single Pc)"
  then obtain g trc g' where split: "ec = (g, trc, g')"
    "par_big_step (Single Pc) g trc g'"
    unfolding set_of_traces_def by blast
  from split(2) obtain sc sc' where g: "g = State sc" "g' = State sc'"
    and bs: "big_step Pc sc trc sc'"
    by (blast elim!: SingleE)
  from cover[OF bs] obtain sa where sa: "(sc, sa) \<in> \<alpha>" ..
  from hybrid_sim_single_to_set_of_traces[OF init_sim[OF sa]]
    split(2)[unfolded g, folded split(1)]
  show "\<exists>ea \<in> set_of_traces (Single Pa). single_execution_rel \<alpha> ec ea"
    by blast
qed

corollary refine_then_verify_single:
  assumes init_sim: "\<And>sc sa. (sc, sa) \<in> \<alpha> \<Longrightarrow> (Pc, sc) \<sqsubseteq> \<alpha> (Pa, sa)"
      and cover: "\<And>sc trc sc'. big_step Pc sc trc sc' \<Longrightarrow> \<exists>sa. (sc, sa) \<in> \<alpha>"
      and abs: "hypersat (Single Pa) Ha"
      and compat: "hyperproperty_refinement (single_execution_rel \<alpha>) Hc Ha"
  shows "hypersat (Single Pc) Hc"
  using execution_refinement_preserves_hypersat
    [OF single_sim_execution_refines[OF init_sim cover] compat abs] .


subsection \<open>A worked micro-example\<close>

text \<open>
A toy plant with a clock: \<open>\<dot>XX = 0\<close>, \<open>\<dot>TT = 1\<close>, evolving while \<open>TT < 1\<close>.
The proof is one application of \<^term>\<open>h3l_inv_single\<close>; no unfolding of
\<^const>\<open>sem\<close>, \<^const>\<open>big_step\<close>, or \<^const>\<open>hyper_hoare_triple_def\<close> is needed.
\<close>

definition XX :: var where "XX = CHR ''x''"
definition TT :: var where "TT = CHR ''t''"

definition toy_ode :: ODE where
  "toy_ode = ODE ((\<lambda>_ _. 0)(XX := \<lambda>_. 0, TT := \<lambda>_. 1))"

definition toy_b :: fform where
  "toy_b s \<longleftrightarrow> s TT < 1"

lemma toy_proj_deriv:
  "((\<lambda>v. v $ XX) has_derivative (\<lambda>w. w $ XX)) (at x within (UNIV :: vec set))"
proof -
  have "((\<lambda>v. v $ XX) has_derivative (\<lambda>w. w $ XX)) (at x)"
    by (rule bounded_linear.has_derivative[OF bounded_linear_vec_nth])
  then show ?thesis by (rule has_derivative_at_withinI)
qed

theorem demo_const_var:
  fixes r0 :: real
  shows "\<Turnstile> {\<lambda>S. (\<forall>\<phi>\<in>S. toy_b (pproj \<phi>)) \<and> (\<forall>\<phi>\<in>S. pproj \<phi> XX = r0)}
     Cont toy_ode toy_b
    {\<lambda>S. \<forall>\<phi>\<in>S. \<exists>p d tr0. tproj \<phi> = tr0 @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]
       \<and> 0 < d \<and> p d = pproj \<phi> \<and> (\<forall>t\<in>{0..d}. p t XX = r0)}"
proof (rule h3l_inv_single[where inv = "\<lambda>s. s XX" and g' = "\<lambda>x w. w $ XX" and r = r0])
  show "\<forall>x. ((\<lambda>v. (vec2state v) XX) has_derivative (\<lambda>w. w $ XX)) (at x within UNIV)"
    unfolding vec2state_def using toy_proj_deriv by blast
next
  show "\<forall>s. toy_b s \<longrightarrow> (ODE2Vec toy_ode s) $ XX = 0"
    by (auto simp add: toy_b_def toy_ode_def ODE2Vec_def)
qed


subsection \<open>Parallel and interface refinement drivers\<close>

corollary refine_then_verify_par:
  assumes cover: "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
      \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>p \<alpha> (Pa, sa)"
      and abs: "hypersat Pa Ha"
      and compat: "hyperproperty_refinement (par_execution_rel \<alpha>) Hc Ha"
  shows "hypersat Pc Hc"
  using execution_refinement_preserves_hypersat
    [OF hybrid_sim_par_execution_refines[OF cover] compat abs] .

text \<open>
Interface refinement: a parallel concrete process simulated by a sequential
abstract process (the shape of the lunar lander refinement).
\<close>

corollary refine_then_verify_int:
  assumes cover: "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
      \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
      and abs: "hypersat (Single Pa) Ha"
      and compat: "hyperproperty_refinement (int_execution_rel \<alpha>) Hc Ha"
  shows "hypersat Pc Hc"
  using execution_refinement_preserves_hypersat
    [OF hybrid_sim_int_execution_refines[OF cover] compat abs] .


subsection \<open>Instantiation: the lunar lander, end to end\<close>

definition Lander_P :: pproc where
  "Lander_P = Parallel (Single (Rep Plant)) {''p2c'', ''c2p''} (Single (Rep Ctrl))"

definition Lander_\<alpha> :: "(gstate \<times> state) set" where
  "Lander_\<alpha> = {(ParState (State s\<^sub>p) (State s\<^sub>c), s\<^sub>p(T := t)) |s\<^sub>p s\<^sub>c t. True}"

text \<open>Every lander execution starts from a pair of states, and for such
initial states \<^term>\<open>Lander_Refine\<close> provides the simulation.\<close>

lemma lander_init_sim:
  assumes ec: "(sc, trc, sc') \<in> set_of_traces Lander_P"
  shows "\<exists>sa. (Lander_P, sc) \<sqsubseteq>\<^sub>I Lander_\<alpha> (Rep Abs, sa)"
proof -
  from ec have pb: "par_big_step (Parallel (Single (Rep Plant)) {''p2c'', ''c2p''} (Single (Rep Ctrl))) sc trc sc'"
    by (auto simp add: Lander_P_def set_of_traces_def)
  then obtain s1 s2 l1 l2 s1' s2' where
    sc: "sc = ParState s1 s2"
    and bs1: "par_big_step (Single (Rep Plant)) s1 l1 s1'"
    and bs2: "par_big_step (Single (Rep Ctrl)) s2 l2 s2'"
    by (blast elim!: ParallelE)
  from bs1 obtain sp where s1: "s1 = State sp" by (blast elim!: SingleE)
  from bs2 obtain scc where s2: "s2 = State scc" by (blast elim!: SingleE)
  have sim: "(Lander_P, ParState (State sp) (State scc)) \<sqsubseteq>\<^sub>I Lander_\<alpha> (Rep Abs, sp)"
    unfolding Lander_P_def
    using Lander_Refine[where \<alpha> = Lander_\<alpha> and s\<^sub>p = sp and s\<^sub>c = scc]
    by (simp add: Lander_\<alpha>_def)
  with sc s1 s2 show ?thesis by blast
qed

text \<open>
The end-to-end refinement theorem for the lander: any hyperproperty (in the
compatibility sense) established for the abstract model \<^term>\<open>Rep Abs\<close>
transfers to the concrete parallel implementation.
\<close>

theorem lander_refine_then_verify:
  assumes abs: "hypersat (Single (Rep Abs)) Ha"
      and compat: "hyperproperty_refinement (int_execution_rel Lander_\<alpha>) Hc Ha"
  shows "hypersat Lander_P Hc"
  using refine_then_verify_int[OF lander_init_sim abs compat] .


subsection \<open>Gluing the classical HHL rule library to refinement (framework bridges)\<close>

text \<open>
The round trip between classical HHL triples and H3L hyper-triples:
\<^term>\<open>hl_bridge\<close> (above) lifts classical triples; the converse extracts a
classical triple from a hyper-triple over lifted assertions.
\<close>

theorem h3l_to_hl:
  assumes "\<Turnstile> {hl_lift P} C {hl_lift Q}"
  shows "\<Turnstile>\<^sub>H\<^sub>L {P} C {Q}"
proof -
  from assms have "HL (lift_assn P) C (lift_assn Q)"
    unfolding hl_lift_def using encoding_HL by blast
  then show ?thesis using HL_encode_triple by blast
qed

text \<open>Trace-level properties: the meeting point of the two frameworks.\<close>

definition trace_sat :: "(trace \<Rightarrow> bool) \<Rightarrow> pproc \<Rightarrow> bool" where
  "trace_sat \<phi> C \<longleftrightarrow> (\<forall>s tr s'. (s, tr, s') \<in> set_of_traces C \<longrightarrow> \<phi> tr)"

text \<open>A classical HHL triple with a trace postcondition establishes the
trace property (the shape produced by the gGHL rule library, e.g.\
\<^term>\<open>ContinuousInvHHL.Valid_inv'\<close> with its \<^term>\<open>@\<^sub>t\<close>-assertions).\<close>

lemma hl_trace_property:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. True} Pa {\<lambda>s tr. \<phi> tr}"
  shows "trace_sat \<phi> (Single Pa)"
  using assms unfolding trace_sat_def Valid_def set_of_traces_def
  by (auto elim!: SingleE)

text \<open>
\<^bold>\<open>Flagship glue.\<close> Refinement transfers trace properties downwards:
prove the abstract model's property with the classical single-run rule
library and obtain the property for the concrete parallel implementation,
provided \<open>\<phi>\<close> is stable under the simulation's trace relation.
\<close>

theorem refine_trace_property:
  assumes cover: "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
      \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
      and abs: "trace_sat \<phi> (Single Pa)"
      and mono: "\<And>trc tra. tr_int \<alpha> trc tra \<Longrightarrow> \<phi> tra \<Longrightarrow> \<phi> trc"
  shows "trace_sat \<phi> Pc"
proof (unfold trace_sat_def, rule ballI)
  fix ec assume "ec \<in> set_of_traces Pc"
  then obtain sc trc sc' where ec: "ec = (sc, trc, sc')"
    "(sc, trc, sc') \<in> set_of_traces Pc" by (cases ec) auto
  from cover[OF ec(2)] obtain sa where sim: "(Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)" ..
  from ec(2) have pb: "par_big_step Pc sc trc sc'"
    by (auto simp: set_of_traces_def)
  from hybrid_sim_int_execution[OF sim pb] obtain sa' tra
    where hb: "big_step Pa sa tra sa'"
    and rel4: "int_execution_rel \<alpha> (sc, trc, sc') (State sa, tra, State sa')" .
  from rel4 have rel: "tr_int \<alpha> trc tra" by (simp add: int_execution_rel_def)
  from abs hb have "\<phi> tra"
    by (auto simp: trace_sat_def set_of_traces_def intro: SingleB)
  from mono[OF rel this] show "\<phi> trc" .
qed

theorem hl_refine_trace_property:
  assumes cover: "\<And>sc trc sc'. (sc, trc, sc') \<in> set_of_traces Pc \<Longrightarrow>
      \<exists>sa. (Pc, sc) \<sqsubseteq>\<^sub>I \<alpha> (Pa, sa)"
      and hl: "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. True} Pa {\<lambda>s tr. \<phi> tr}"
      and mono: "\<And>trc tra. tr_int \<alpha> trc tra \<Longrightarrow> \<phi> tra \<Longrightarrow> \<phi> trc"
  shows "trace_sat \<phi> Pc"
  using refine_trace_property[OF cover hl_trace_property[OF hl] mono] .


subsection \<open>Practical rules: state-and-trace invariants for periodic loops\<close>

text \<open>
\<^term>\<open>RepH\<close> is complete but impractical: it needs an indexed family of
assertions and a \<^term>\<open>natural_partition\<close> discharge.  The rules below
carry a \<^bold>\<open>single state-and-trace invariant\<close> through loops -- the shape
used by periodic-control case studies.
\<close>

definition blocks_inv :: "((real \<Rightarrow> gstate) \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> trace \<Rightarrow> bool" where
  "blocks_inv R tr \<longleftrightarrow> (\<forall>bl \<in> set tr. \<forall>d p rdy. bl = WaitBlock d p rdy \<longrightarrow> R p d)"

lemma blocks_inv_app:
  assumes "blocks_inv R tr" "R p d"
  shows "blocks_inv R (tr @ [WaitBlock d p rdy])"
  using assms unfolding blocks_inv_def by auto

lemma trace_prop_rep:
  assumes step: "\<And>S. (\<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)) \<Longrightarrow>
      (\<forall>\<phi>'\<in>sem C S. I (pproj \<phi>') (tproj \<phi>'))"
      and a0: "\<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)"
  shows "\<forall>\<phi>'\<in>sem (Rep C) S. I (pproj \<phi>') (tproj \<phi>')"
proof -
  have "\<And>n. \<forall>\<psi>\<in>iterate_sem n C S. I (pproj \<psi>) (tproj \<psi>)"
  proof (induct n)
    case 0 show ?case using a0 by simp
  next
    case (Suc n)
    have "iterate_sem (Suc n) C S = sem C (iterate_sem n C S)" by simp
    also have "\<forall>\<psi>\<in>sem C (iterate_sem n C S). I (pproj \<psi>) (tproj \<psi>)"
      by (rule step) (rule Suc)
    finally show ?case .
  qed
  then show ?thesis by (auto simp: sem_while)
qed

text \<open>
Loop rule with a single invariant: one application instead of constructing
an indexed family \<^term>\<open>I :: nat \<Rightarrow> _\<close> and discharging the natural partition.
\<close>

theorem rep_invariant_trace:
  assumes inv: "\<Turnstile> {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)} C
                    {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)}"
  shows "\<Turnstile> {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)} Rep C
                    {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)}"
proof (rule hyper_hoare_tripleI)
  fix S assume a0: "\<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)"
  from trace_prop_rep[of I C S] inv[unfolded hyper_hoare_triple_def, rule_format, OF a0] a0
  show "\<forall>\<phi>'\<in>sem (Rep C) S. I (pproj \<phi>') (tproj \<phi>')" by blast
qed

text \<open>Periodic-control pattern: evolution + discrete update, repeated.\<close>

corollary control_loop_invariant:
  assumes "\<Turnstile> {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)} C1
                    {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)}"
      and "\<Turnstile> {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)} C2
                    {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)}"
  shows "\<Turnstile> {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)} Rep (C1; C2)
                    {\<lambda>S. \<forall>\<phi>\<in>S. I (pproj \<phi>) (tproj \<phi>)}"
  using rep_invariant_trace[OF seq_rule[OF assms(1) assms(2)]] .

end
