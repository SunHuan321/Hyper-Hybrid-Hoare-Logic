theory PhaseG_GNI_hybrid
  imports PhaseG_GNI_trace
begin

section \<open>Acceptance items: wider observers and hybrid examples (F7/F1)\<close>

text \<open>
Corresponds to the acceptance review (2026-09-25):

  \<^item> \<open>F7(b)\<close>: value leak.  A public send whose payload is the high
    input: under the channel-only observer of \<^theory_text>\<open>PhaseG_GNI_trace\<close>
    the program is GNI, but any observer that also sees the transmitted
    VALUE rejects it.  \<^theory_text>\<open>value_leak_gni_obs_v_fails\<close> /
    \<^theory_text>\<open>channel_only_gni_obs_holds\<close>.

  \<^item> \<open>F7(a)\<close>: continuous-curve leak.  Two branches, distinguished by
    the high input, evolve the low variable along \<open>t\<close> resp. \<open>t\<^sup>2\<close>
    to the SAME endpoint in the SAME duration.  Duration-only observation
    cannot separate them; an observer that sees the low curve can.
    \<^theory_text>\<open>curve_leak_gni_obs_c_fails\<close> /
    \<^theory_text>\<open>duration_only_gni_obs_holds\<close>.

  \<^item> positive example with an ODE: havoc followed by a clock evolution.
    \<^theory_text>\<open>gni_obs_c_havoc_cont\<close>.

  \<^item> \<open>F1\<close> (list level): wait splitting is invisible to the
    block-boundary-insensitive normalisation of observations,
    \<^theory_text>\<open>obs_wait_split\<close>.

The elementary ODE solutions and their componentwise characterisations
are proved below using vector-derivative projections and the mean-value
theorem. The F7 separation results and positive clock-ODE example therefore
have no local analytic axioms.\<close>


subsection \<open>Analytic lemmas for the example ODEs\<close>

definition CC :: var where "CC = CHR ''c''"

lemma CC_LL2_neq [simp]: "CC \<noteq> LL2" "LL2 \<noteq> CC"
  unfolding CC_def LL2_def by auto

lemma CC_HH2_neq [simp]: "CC \<noteq> HH2" "HH2 \<noteq> CC"
  unfolding CC_def HH2_def by auto

definition ode_lin :: ODE where
  "ode_lin = ODE (\<lambda>a s. if a = LL2 then 1 else 0)"

definition ode_sq :: ODE where
  "ode_sq = ODE (\<lambda>a s. if a = LL2 then 2 * s CC else (if a = CC then 1 else 0))"

definition ode_cl :: ODE where
  "ode_cl = ODE (\<lambda>a s. if a = CC then 1 else 0)"

definition bnd_x :: fform where "bnd_x s \<longleftrightarrow> s LL2 < 1"
definition bnd_c :: fform where "bnd_c s \<longleftrightarrow> s CC < 1"

text \<open>The six analytic obligations are derived from componentwise ODE derivatives and the mean-value theorem.\<close>

lemma ODEsol_component_vderiv:
  assumes sol: "ODEsol (ODE f) p d"
  shows "((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {0..d}"
  using has_vderiv_on_proj[OF ODEsol_old[OF sol], of x]
  by (simp add: state2vec_def)

lemma ODEsol_component_const:
  assumes sol: "ODEsol (ODE f) p d"
    and zero: "\<And>s. f x s = 0"
    and t: "t \<in> {0..d}"
  shows "p t x = p 0 x"
proof -
  have v: "((\<lambda>u. p u x) has_vderiv_on (\<lambda>u. 0)) {0..d}"
    using ODEsol_component_vderiv[OF sol, of x] by (simp add: zero)
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u x) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
    using v unfolding has_vderiv_on_def has_vector_derivative_def by simp
  have "0 \<le> d" using sol unfolding ODEsol_def by simp
  from mvt_real_eq[OF der this _ t] show ?thesis by simp
qed

lemma ODEsol_component_affine:
  assumes sol: "ODEsol (ODE f) p d"
    and rate: "\<And>s. f x s = c"
    and t: "t \<in> {0..d}"
  shows "p t x = p 0 x + c * t"
proof -
  have v: "((\<lambda>u. p u x) has_vderiv_on (\<lambda>u. c)) {0..d}"
    using ODEsol_component_vderiv[OF sol, of x] by (simp add: rate)
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u x - c * u) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have pv: "((\<lambda>u. p u x) has_derivative (\<lambda>h. h *\<^sub>R c)) (at u within {0..d})"
      using v u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have cv: "((\<lambda>u. c * u) has_derivative (\<lambda>h. h *\<^sub>R c)) (at u within {0..d})"
      apply (rule has_derivative_eq_rhs[OF has_derivative_mult_right])
       apply (rule has_derivative_ident)
      by (simp add: mult.commute)
    show "((\<lambda>u. p u x - c * u) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
      using has_derivative_diff[OF pv cv] by simp
  qed
  have "0 \<le> d" using sol unfolding ODEsol_def by simp
  have "p 0 x - c * 0 = p t x - c * t"
    by (rule mvt_real_eq[OF der \<open>0 \<le> d\<close> _ t], simp)
  then show ?thesis by simp
qed

lemma ode_lin_char:
  assumes sol: "ODEsol ode_lin p d"
  shows "\<forall>t\<in>{0..d}. p t LL2 = p 0 LL2 + t \<and> p t CC = p 0 CC"
proof (intro ballI)
  fix t assume t: "t \<in> {0..d}"
  have ll: "p t LL2 = p 0 LL2 + 1 * t"
    using ODEsol_component_affine[of "\<lambda>a s. if a = LL2 then 1 else 0" p d LL2 1 t]
      sol t by (simp add: ode_lin_def)
  have cc: "p t CC = p 0 CC"
    using ODEsol_component_const[of "\<lambda>a s. if a = LL2 then 1 else 0" p d CC t]
      sol t by (simp add: ode_lin_def)
  show "p t LL2 = p 0 LL2 + t \<and> p t CC = p 0 CC"
    using ll cc by simp
qed

lemma ode_cl_char:
  assumes sol: "ODEsol ode_cl p d"
  shows "\<forall>t\<in>{0..d}. p t CC = p 0 CC + t \<and> (\<forall>a. a \<noteq> CC \<longrightarrow> p t a = p 0 a)"
proof (intro ballI conjI allI impI)
  fix t assume t: "t \<in> {0..d}"
  show "p t CC = p 0 CC + t"
    using ODEsol_component_affine[of "\<lambda>a s. if a = CC then 1 else 0" p d CC 1 t]
      sol t by (simp add: ode_cl_def)
  fix a assume neq: "a \<noteq> CC"
  show "p t a = p 0 a"
    using ODEsol_component_const[of "\<lambda>a s. if a = CC then 1 else 0" p d a t]
      sol t neq by (simp add: ode_cl_def)
qed

lemma ode_sq_char:
  assumes sol: "ODEsol ode_sq p d"
  shows "\<forall>t\<in>{0..d}. p t CC = p 0 CC + t \<and>
    p t LL2 = (p t CC)\<^sup>2 - (p 0 CC)\<^sup>2 + p 0 LL2"
proof (intro ballI conjI)
  fix t assume t: "t \<in> {0..d}"
  let ?f = "\<lambda>a s. if a = LL2 then 2 * s CC else (if a = CC then 1 else 0)"
  have sol': "ODEsol (ODE ?f) p d" using sol by (simp add: ode_sq_def)
  show cc: "p t CC = p 0 CC + t"
    using ODEsol_component_affine[of ?f p d CC 1 t] sol' t by simp
  have cv: "((\<lambda>u. p u CC) has_vderiv_on (\<lambda>u. 1)) {0..d}"
    using ODEsol_component_vderiv[OF sol', of CC] by simp
  have lv: "((\<lambda>u. p u LL2) has_vderiv_on (\<lambda>u. 2 * p u CC)) {0..d}"
    using ODEsol_component_vderiv[OF sol', of LL2] by simp
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u LL2 - (p u CC)\<^sup>2)
      has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have cd: "((\<lambda>u. p u CC) has_derivative (\<lambda>h. h *\<^sub>R 1)) (at u within {0..d})"
      using cv u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have ld: "((\<lambda>u. p u LL2) has_derivative (\<lambda>h. h *\<^sub>R (2 * p u CC))) (at u within {0..d})"
      using lv u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have sd: "((\<lambda>u. (p u CC)\<^sup>2) has_derivative (\<lambda>h. h *\<^sub>R (2 * p u CC))) (at u within {0..d})"
      using has_derivative_power[OF cd, of 2] by (simp add: algebra_simps)
    show "((\<lambda>u. p u LL2 - (p u CC)\<^sup>2) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
      using has_derivative_diff[OF ld sd] by simp
  qed
  have nonneg: "0 \<le> d" using sol unfolding ODEsol_def by simp
  have "p 0 LL2 - (p 0 CC)\<^sup>2 = p t LL2 - (p t CC)\<^sup>2"
    by (rule mvt_real_eq[OF der nonneg _ t], simp)
  then show "p t LL2 = (p t CC)\<^sup>2 - (p 0 CC)\<^sup>2 + p 0 LL2"
    by linarith
qed

lemma ODEsol_from_components:
  assumes d: "0 \<le> d" and e: "0 < e"
    and comp: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {-e..d+e}"
  shows "ODEsol (ODE f) p d"
proof -
  have "((\<lambda>t. state2vec (p t)) has_vderiv_on
      (\<lambda>t. ODE2Vec (ODE f) (p t))) {-e..d+e}"
    by (rule has_vderiv_on_projI) (simp add: state2vec_def comp)
  with d e show ?thesis unfolding ODEsol_def by blast
qed

lemma ode_cl_sol:
  assumes d: "0 < d"
  shows "ODEsol ode_cl (\<lambda>t. q(CC := q CC + t)) d"
proof -
  let ?p = "\<lambda>t. q(CC := q CC + t)"
  let ?f = "\<lambda>a s. if a = CC then 1 else 0"
  have comp: "\<And>x. ((\<lambda>t. ?p t x) has_vderiv_on
      (\<lambda>t. ?f x (?p t))) {-1..d+1}"
  proof -
    fix x
    show "((\<lambda>t. ?p t x) has_vderiv_on (\<lambda>t. ?f x (?p t))) {-1..d+1}"
    proof (cases "x = CC")
      case True
      then show ?thesis
        by (simp add: has_vderiv_on_def has_vector_derivative_def shift_has_derivative_id)
    next
      case False
      then show ?thesis by (simp add: has_vderiv_on_const)
    qed
  qed
  have "ODEsol (ODE ?f) ?p d"
    by (rule ODEsol_from_components[OF _ _ comp]) (use d in auto)
  then show ?thesis by (simp add: ode_cl_def)
qed

lemma ode_lin_sol:
  "ODEsol ode_lin (\<lambda>t. ((\<lambda>_. 0)(HH2 := 1))(LL2 := t)) 1"
proof -
  let ?p = "\<lambda>t. ((\<lambda>_. 0)(HH2 := 1))(LL2 := t)"
  let ?f = "\<lambda>a s. if a = LL2 then 1 else 0"
  have comp: "\<And>x. ((\<lambda>t. ?p t x) has_vderiv_on
      (\<lambda>t. ?f x (?p t))) {-1..1+1}"
  proof -
    fix x
    show "((\<lambda>t. ?p t x) has_vderiv_on (\<lambda>t. ?f x (?p t))) {-1..1+1}"
    proof (cases "x = LL2")
      case True
      then show ?thesis by (simp add: has_vderiv_on_id)
    next
      case False
      then show ?thesis by (simp add: has_vderiv_on_const)
    qed
  qed
  have "ODEsol (ODE ?f) ?p 1"
    by (rule ODEsol_from_components[OF _ _ comp]) auto
  then show ?thesis by (simp add: ode_lin_def)
qed

lemma ode_sq_sol:
  "ODEsol ode_sq (\<lambda>t. (((\<lambda>_. 0)(HH2 := 2))(LL2 := t * t))(CC := t)) 1"
proof -
  let ?p = "\<lambda>t. (((\<lambda>_. 0)(HH2 := 2))(LL2 := t * t))(CC := t)"
  let ?f = "\<lambda>a s. if a = LL2 then 2 * s CC else (if a = CC then 1 else 0)"
  have sq: "((\<lambda>t. t * t) has_vderiv_on (\<lambda>t. 2 * t)) {-1..1+1}"
  proof (unfold has_vderiv_on_def, intro ballI)
    fix t :: real assume "t \<in> {-1..1+1}"
    show "((\<lambda>u. u * u) has_vector_derivative 2 * t) (at t within {-1..1+1})"
      unfolding has_vector_derivative_def
      apply (rule has_derivative_eq_rhs[OF has_derivative_mult])
        apply (rule has_derivative_ident)
       apply (rule has_derivative_ident)
      by (simp add: algebra_simps)
  qed
  have comp: "\<And>x. ((\<lambda>t. ?p t x) has_vderiv_on
      (\<lambda>t. ?f x (?p t))) {-1..1+1}"
  proof -
    fix x
    show "((\<lambda>t. ?p t x) has_vderiv_on (\<lambda>t. ?f x (?p t))) {-1..1+1}"
    proof (cases "x = LL2")
      case True
      then show ?thesis using sq by simp
    next
      case notll: False
      show ?thesis
      proof (cases "x = CC")
        case True
        then show ?thesis using notll by (simp add: has_vderiv_on_id)
      next
        case False
        then show ?thesis using notll by (simp add: has_vderiv_on_const)
      qed
    qed
  qed
  have "ODEsol (ODE ?f) ?p 1"
  proof (rule ODEsol_from_components[where e=1])
    show "0 \<le> (1::real)" by simp
    show "0 < (1::real)" by simp
    fix x
    show "((\<lambda>t. ?p t x) has_vderiv_on (\<lambda>t. ?f x (?p t))) {-1..1+1}"
      by (rule comp)
  qed
  then show ?thesis by (simp add: ode_sq_def)
qed


subsection \<open>Two-run differential certificates and time alignment\<close>

text \<open>A smooth scalar certificate on the product state preserves a two-run
relation throughout aligned ODE solutions. If the relation synchronises the
exit guard, the two maximal continuous runs have the same duration.\<close>

lemma relational_ode_scalar_invariant:
  fixes G :: "((real^var) \<times> (real^var)) \<Rightarrow> real"
  assumes sol1: "ODEsol ode p1 d" and sol2: "ODEsol ode p2 d"
    and smooth: "\<And>v. (G has_derivative G' v) (at v)"
    and init: "G (state2vec_Pair (p1 0, p2 0)) = 0"
    and lie: "\<And>u. u \<in> {0..<d} \<Longrightarrow>
      G' (state2vec_Pair (p1 u, p2 u)) (ODE2Vec_Pair ode (p1 u, p2 u)) = 0"
  shows "\<forall>u\<in>{0..d}. G (state2vec_Pair (p1 u, p2 u)) = 0"
proof (intro ballI)
  fix t assume t: "t \<in> {0..d}"
  let ?v = "\<lambda>u. state2vec_Pair (p1 u, p2 u)"
  let ?v' = "\<lambda>u. ODE2Vec_Pair ode (p1 u, p2 u)"
  have vd: "(?v has_vderiv_on ?v') {0..d}"
    by (rule ODEsol_old_Pair[OF sol1 sol2])
  have deriv: "\<forall>u\<in>{0..d}. ((\<lambda>u. G (?v u)) has_derivative
      (\<lambda>h. G' (?v u) (h *\<^sub>R ?v' u))) (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have base: "(?v has_derivative (\<lambda>h. h *\<^sub>R ?v' u)) (at u within {0..d})"
      using vd u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    show "((\<lambda>u. G (?v u)) has_derivative
        (\<lambda>h. G' (?v u) (h *\<^sub>R ?v' u))) (at u within {0..d})"
      by (rule has_derivative_compose[OF base smooth])
  qed
  have zero: "\<forall>u\<in>{0..<d}. \<forall>h. G' (?v u) (h *\<^sub>R ?v' u) = 0"
  proof (intro ballI allI)
    fix u h assume u: "u \<in> {0..<d}"
    have lin: "linear (G' (?v u))"
      using smooth[of "?v u"] has_derivative_linear by blast
    have "G' (?v u) (h *\<^sub>R ?v' u) = h *\<^sub>R G' (?v u) (?v' u)"
      by (rule linear.scaleR[OF lin])
    also have "... = 0" using lie[OF u] by simp
    finally show "G' (?v u) (h *\<^sub>R ?v' u) = 0" .
  qed
  have d: "0 \<le> d" using sol1 unfolding ODEsol_def by simp
  have "G (?v 0) = G (?v t)"
    by (rule mvt_real_eq[OF deriv d zero t])
  then show "G (state2vec_Pair (p1 t, p2 t)) = 0" using init by simp
qed

lemma relational_ode_curve_invariant:
  fixes G :: "((real^var) \<times> (real^var)) \<Rightarrow> real"
  assumes sol1: "ODEsol ode p1 d" and sol2: "ODEsol ode p2 d"
    and smooth: "\<And>v. (G has_derivative G' v) (at v)"
    and init: "G (state2vec_Pair (p1 0, p2 0)) = 0"
    and lie: "\<And>u. u \<in> {0..<d} \<Longrightarrow>
      G' (state2vec_Pair (p1 u, p2 u)) (ODE2Vec_Pair ode (p1 u, p2 u)) = 0"
    and low: "\<And>s1 s2. G (state2vec_Pair (s1, s2)) = 0 \<Longrightarrow> s1 l = s2 l"
  shows "\<forall>u\<in>{0..d}. p1 u l = p2 u l"
  using relational_ode_scalar_invariant[OF sol1 sol2 smooth init lie] low by blast

lemma relational_ode_synchronised_exit:
  fixes G :: "((real^var) \<times> (real^var)) \<Rightarrow> real"
  assumes d1: "0 < d1" and d2: "0 < d2"
    and sol1: "ODEsol ode p1 d1" and sol2: "ODEsol ode p2 d2"
    and guard1: "\<And>u. u \<in> {0..<d1} \<Longrightarrow> b (p1 u)"
    and guard2: "\<And>u. u \<in> {0..<d2} \<Longrightarrow> b (p2 u)"
    and exit1: "\<not> b (p1 d1)" and exit2: "\<not> b (p2 d2)"
    and smooth: "\<And>v. (G has_derivative G' v) (at v)"
    and init: "G (state2vec_Pair (p1 0, p2 0)) = 0"
    and lie: "\<And>s1 s2. b s1 \<Longrightarrow> b s2 \<Longrightarrow>
      G' (state2vec_Pair (s1, s2)) (ODE2Vec_Pair ode (s1, s2)) = 0"
    and sync: "\<And>s1 s2. G (state2vec_Pair (s1, s2)) = 0 \<Longrightarrow>
      b s1 \<longleftrightarrow> b s2"
  shows "d1 = d2"
proof -
  let ?d = "min d1 d2"
  have s1: "ODEsol ode p1 ?d" using ODEsol_le[OF sol1] d1 d2 by simp
  have s2: "ODEsol ode p2 ?d" using ODEsol_le[OF sol2] d1 d2 by simp
  have lie': "\<And>u. u \<in> {0..<?d} \<Longrightarrow>
    G' (state2vec_Pair (p1 u, p2 u)) (ODE2Vec_Pair ode (p1 u, p2 u)) = 0"
    using guard1 guard2 lie by auto
  have inv: "\<forall>u\<in>{0.. ?d}. G (state2vec_Pair (p1 u, p2 u)) = 0"
    by (rule relational_ode_scalar_invariant[OF s1 s2 smooth init lie'])
  have at_min: "b (p1 ?d) \<longleftrightarrow> b (p2 ?d)"
    using inv sync d1 d2 by auto
  show ?thesis
  proof (rule ccontr)
    assume "d1 \<noteq> d2"
    then consider (lt) "d1 < d2" | (gt) "d2 < d1" by linarith
    then show False
    proof cases
      case lt
      then have "b (p2 ?d)" using guard2[of d1] d1 by simp
      moreover have "\<not> b (p1 ?d)" using exit1 lt by simp
      ultimately show False using at_min by simp
    next
      case gt
      then have "b (p1 ?d)" using guard1[of d2] d2 by simp
      moreover have "\<not> b (p2 ?d)" using exit2 gt by simp
      ultimately show False using at_min by simp
    qed
  qed
qed


subsection \<open>F1 (list level): block-boundary-insensitive observation\<close>

fun norm_obs :: "obs_event list \<Rightarrow> obs_event list" where
  "norm_obs [] = []"
| "norm_obs (Inl d # Inl d' # rest) = norm_obs (Inl (d + d') # rest)"
| "norm_obs (e # rest) = e # norm_obs rest"

theorem obs_wait_split:
  "norm_obs (obs_tr [WaitBlock d1 p r, WaitBlock d2 (\<lambda>u. p (u + d1)) r])
   = norm_obs (obs_tr [WaitBlock (d1 + d2) p r])"
  by (simp add: obs_tr_def obs_block_def)


subsection \<open>F7(b): the value leak\<close>

type_synonym obs_event_v = "real + (cname \<times> real)"

definition obs_block_v :: "trace_block \<Rightarrow> obs_event_v" where
  "obs_block_v blk = (case blk of
      WaitBlock d p rdy \<Rightarrow> Inl d
    | CommBlock ct ch v \<Rightarrow> Inr (ch, v))"

definition obs_tr_v :: "trace \<Rightarrow> obs_event_v list" where
  "obs_tr_v = map obs_block_v"

definition low_obs_v :: "var \<Rightarrow> (('lvar, 'lval) exstate) \<Rightarrow> real \<times> obs_event_v list" where
  "low_obs_v l \<phi> = (pproj \<phi> l, obs_tr_v (tproj \<phi>))"

definition gni_obs_v :: "'lvar \<Rightarrow> 'lvar \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni_obs_v hi lo l S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. lproj \<phi>1 lo = lproj \<phi>2 lo \<longrightarrow>
      (\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
        \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
        \<and> low_obs_v l \<phi>3 = low_obs_v l \<phi>2))"

definition VP :: cname where "VP = ''pub''"

definition C_val :: proc where
  "C_val = Cm (VP[!] (\<lambda>\<sigma>. \<sigma> HH2))"

definition val_init1 :: "(char, real) exstate" where
  "val_init1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1), [])"

definition val_init2 :: "(char, real) exstate" where
  "val_init2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2), [])"

definition S_val :: "(char, real) exstate set" where
  "S_val = {val_init1, val_init2}"

lemma val_send_nowI:
  assumes src: "(a, b, []) \<in> S_val"
  shows "(a, b, [OutBlock VP (b HH2)]) \<in> sem C_val S_val"
  unfolding C_val_def sem_send
  apply (rule UnI1, rule CollectI)
  apply (rule_tac x = a in exI, rule_tac x = b in exI,
         rule_tac x = "[]" in exI)
  using src by simp

lemma val_send_waitI:
  assumes src: "(a, b, []) \<in> S_val" and pos: "0 < d"
  shows "(a, b, [WaitBlk d (\<lambda>_. State b) ({VP}, {}), OutBlock VP (b HH2)])
     \<in> sem C_val S_val"
  unfolding C_val_def sem_send
  apply (rule UnI2, rule CollectI)
  apply (rule_tac x = a in exI, rule_tac x = b in exI,
         rule_tac x = "[]" in exI, rule_tac x = d in exI)
  using src pos by simp

definition val_run1 :: "(char, real) exstate" where
  "val_run1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1), [OutBlock VP 1])"

definition val_run2 :: "(char, real) exstate" where
  "val_run2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2), [OutBlock VP 2])"

lemma val_run1_mem:
  "val_run1 \<in> sem C_val S_val"
proof -
  have src: "val_init1 \<in> S_val" by (simp add: S_val_def)
  have mem: "(fst val_init1, fst (snd val_init1),
      [OutBlock VP ((fst (snd val_init1)) HH2)]) \<in> sem C_val S_val"
    using val_send_nowI[of "fst val_init1" "fst (snd val_init1)"] src
    by (simp add: val_init1_def)
  show ?thesis using mem by (simp add: val_run1_def val_init1_def)
qed

lemma val_run2_mem:
  "val_run2 \<in> sem C_val S_val"
proof -
  have src: "val_init2 \<in> S_val" by (simp add: S_val_def)
  have mem: "(fst val_init2, fst (snd val_init2),
      [OutBlock VP ((fst (snd val_init2)) HH2)]) \<in> sem C_val S_val"
    using val_send_nowI[of "fst val_init2" "fst (snd val_init2)"] src
    by (simp add: val_init2_def)
  show ?thesis using mem by (simp add: val_run2_def val_init2_def)
qed

lemma val_src_trace:
  assumes "(a, b, t) \<in> S_val"
  shows "t = []"
  using assms by (auto simp: S_val_def val_init1_def val_init2_def)

lemma val_mem_cases:
  assumes m: "\<phi> \<in> sem C_val S_val"
  shows "(\<exists>a b. (a, b, []) \<in> S_val \<and> \<phi> = (a, b, [OutBlock VP (b HH2)]))
     \<or> (\<exists>a b d. (a, b, []) \<in> S_val \<and> 0 < d \<and>
          \<phi> = (a, b, [WaitBlk d (\<lambda>_. State b) ({VP}, {}), OutBlock VP (b HH2)]))"
proof -
  from m [unfolded C_val_def sem_send] show ?thesis
  proof (elim UnE)
    assume imm: "\<phi> \<in> {(a, b, t @ [OutBlock VP (b HH2)]) |a b t.
                         (a, b, t) \<in> S_val}"
    then obtain a b t where src: "(a, b, t) \<in> S_val"
      and eq: "\<phi> = (a, b, t @ [OutBlock VP (b HH2)])"
      by (auto simp only: mem_Collect_eq)
    have tz: "t = []" by (rule val_src_trace [OF src])
    show ?thesis
      apply (rule disjI1)
      apply (rule_tac x = a in exI, rule_tac x = b in exI)
      using src eq tz by simp
  next
    assume wt: "\<phi> \<in> {(a, b, t @ [WaitBlk d (\<lambda>_. State b) ({VP}, {}),
                                          OutBlock VP (b HH2)]) |a b t d.
                         0 < d \<and> (a, b, t) \<in> S_val}"
    then obtain a b t d where pos: "0 < d" and src: "(a, b, t) \<in> S_val"
      and eq: "\<phi> = (a, b, t @ [WaitBlk d (\<lambda>_. State b) ({VP}, {}),
                                      OutBlock VP (b HH2)])"
      by (auto simp only: mem_Collect_eq)
    have tz: "t = []" by (rule val_src_trace [OF src])
    show ?thesis
      apply (rule disjI2)
      apply (rule_tac x = a in exI, rule_tac x = b in exI,
             rule_tac x = d in exI)
      using src pos eq tz by simp
  qed
qed

lemma val_src_h:
  assumes "(a, b, []) \<in> S_val"
  shows "(a HI = 1 \<longleftrightarrow> b HH2 = 1) \<and> (a HI = 2 \<longleftrightarrow> b HH2 = 2)
    \<and> b LL2 = 0 \<and> a LO = 0"
  using assms by (auto simp: S_val_def val_init1_def val_init2_def)

theorem value_leak_gni_obs_v_fails:
  "\<not> gni_obs_v HI LO LL2 (sem C_val S_val)"
proof -
  have loeq: "lproj val_run1 LO = lproj val_run2 LO"
    by (simp add: val_run1_def val_run2_def lproj_def)
  show ?thesis
  proof
    assume g: "gni_obs_v HI LO LL2 (sem C_val S_val)"
    from g [unfolded gni_obs_v_def, rule_format, OF val_run1_mem val_run2_mem loeq]
    obtain \<phi>3 where w3: "\<phi>3 \<in> sem C_val S_val"
      "lproj \<phi>3 HI = lproj val_run1 HI"
      "lproj \<phi>3 LO = lproj val_run2 LO"
      "low_obs_v LL2 \<phi>3 = low_obs_v LL2 val_run2" by blast
    from val_mem_cases [OF w3(1)] show False
    proof (elim disjE exE conjE)
      fix a b assume src: "(a, b, []) \<in> S_val" and eq: "\<phi>3 = (a, b, [OutBlock VP (b HH2)])"
      from val_src_h [OF src] have corr: "a HI = 1 \<longleftrightarrow> b HH2 = 1" by simp
      from eq have "lproj \<phi>3 HI = a HI" by (simp add: lproj_def)
      with w3(2) have "a HI = 1" by (simp add: val_run1_def lproj_def)
      with corr have bh1: "b HH2 = 1" by blast
      from w3(4) eq bh1 show False
        by (simp add: low_obs_v_def obs_tr_v_def obs_block_v_def val_run2_def pproj_def tproj_def)
    next
      fix a b d assume src: "(a, b, []) \<in> S_val" and "0 < d"
        and eq: "\<phi>3 = (a, b, [WaitBlk d (\<lambda>_. State b) ({VP}, {}), OutBlock VP (b HH2)])"
      from val_src_h [OF src] have corr: "a HI = 1 \<longleftrightarrow> b HH2 = 1" by simp
      from eq have "lproj \<phi>3 HI = a HI" by (simp add: lproj_def)
      with w3(2) have "a HI = 1" by (simp add: val_run1_def lproj_def)
      with corr have bh1: "b HH2 = 1" by blast
      from w3(4) eq bh1 show False
        by (simp add: low_obs_v_def obs_tr_v_def obs_block_v_def val_run2_def pproj_def tproj_def)
    qed
  qed
qed

theorem channel_only_gni_obs_holds:
  "gni_obs HI LO LL2 (sem C_val S_val)"
proof (unfold gni_obs_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> sem C_val S_val" and m2: "\<phi>2 \<in> sem C_val S_val"
     and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
  from val_mem_cases [OF m1] obtain a1 b1 where
    s1: "(a1, b1, []) \<in> S_val"
    and t1: "\<phi>1 = (a1, b1, [OutBlock VP (b1 HH2)])
              \<or> (\<exists>d>0. \<phi>1 = (a1, b1, [WaitBlk d (\<lambda>_. State b1) ({VP}, {}), OutBlock VP (b1 HH2)]))"
    by blast
  from val_mem_cases [OF m2] obtain a2 b2 where
    s2: "(a2, b2, []) \<in> S_val"
    and t2: "\<phi>2 = (a2, b2, [OutBlock VP (b2 HH2)])
              \<or> (\<exists>d>0. \<phi>2 = (a2, b2, [WaitBlk d (\<lambda>_. State b2) ({VP}, {}), OutBlock VP (b2 HH2)]))"
    by blast
  have obs_imm: "low_obs LL2 (a, b, [OutBlock VP (b HH2)]) = (b LL2, [Inr VP])"
    for a b by (simp add: low_obs_def obs_tr_def obs_block_def pproj_def tproj_def)
  have obs_wait: "0 < d \<Longrightarrow> low_obs LL2 (a, b, [WaitBlk d (\<lambda>_. State b) ({VP}, {}), OutBlock VP (b HH2)])
      = (b LL2, [Inl d, Inr VP])" for a b d
    by (simp add: low_obs_def obs_tr_def obs_block_def WaitBlk_def pproj_def tproj_def)
  from s1 s2 have lows: "b1 LL2 = 0" "b2 LL2 = 0"
    and los: "a1 LO = 0" "a2 LO = 0"
    using val_src_h[OF s1] val_src_h[OF s2] by simp_all
  show "\<exists>\<phi>3 \<in> sem C_val S_val. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
  proof (cases "\<exists>d>0. \<phi>2 = (a2, b2, [WaitBlk d (\<lambda>_. State b2) ({VP}, {}), OutBlock VP (b2 HH2)])")
    case False
    with t2 have eq2: "\<phi>2 = (a2, b2, [OutBlock VP (b2 HH2)])" by blast
    then have obs2: "low_obs LL2 \<phi>2 = (0, [Inr VP])" using lows(2) by (simp add: obs_imm)
    define w where "w = (a1, b1, [OutBlock VP (b1 HH2)])"
    have wmem: "w \<in> sem C_val S_val"
      unfolding w_def by (rule val_send_nowI [OF s1])
    have wobs: "low_obs LL2 w = (0, [Inr VP])" using lows(1) by (simp add: w_def obs_imm)
    have wl1: "lproj w HI = lproj \<phi>1 HI" using t1 by (auto simp: w_def lproj_def)
    have wl2: "lproj w LO = lproj \<phi>2 LO" using eq2 los by (simp add: w_def lproj_def)
    have key: "\<exists>\<phi>3 \<in> sem C_val S_val. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
      apply (rule_tac x = w in bexI)
       apply (simp add: wl1 wl2 wobs obs2)
      apply (rule wmem)
      done
    from key show ?thesis .
  next
    case True
    then obtain d2 where d2: "0 < d2"
      and eq2: "\<phi>2 = (a2, b2, [WaitBlk d2 (\<lambda>_. State b2) ({VP}, {}), OutBlock VP (b2 HH2)])" by blast
    then have obs2: "low_obs LL2 \<phi>2 = (0, [Inl d2, Inr VP])" using lows(2) by (simp add: obs_wait)
    define w where "w = (a1, b1, [WaitBlk d2 (\<lambda>_. State b1) ({VP}, {}), OutBlock VP (b1 HH2)])"
    have wmem: "w \<in> sem C_val S_val"
      unfolding w_def by (rule val_send_waitI [OF s1 d2])
    have wobs: "low_obs LL2 w = (0, [Inl d2, Inr VP])"
      unfolding w_def using lows(1) d2 by (simp add: obs_wait)
    have wl1: "lproj w HI = lproj \<phi>1 HI" using t1 by (auto simp: w_def lproj_def)
    have wl2: "lproj w LO = lproj \<phi>2 LO"
      using eq2 los by (simp add: w_def lproj_def)
    have key: "\<exists>\<phi>3 \<in> sem C_val S_val. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
      apply (rule_tac x = w in bexI)
       apply (simp add: wl1 wl2 wobs obs2)
      apply (rule wmem)
      done
    from key show ?thesis .
  qed
qed




subsection \<open>F7(a): the continuous-curve leak\<close>

type_synonym obs_event_c = "(real \<times> (real \<Rightarrow> real)) + cname"

definition low_curve :: "var \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> real \<Rightarrow> real" where
  "low_curve l p t = (case p t of State s \<Rightarrow> s l | ParState _ _ \<Rightarrow> 0)"

definition obs_block_c :: "var \<Rightarrow> trace_block \<Rightarrow> obs_event_c" where
  "obs_block_c l blk = (case blk of
      WaitBlock d p rdy \<Rightarrow> Inl (d, low_curve l p)
    | CommBlock ct ch v \<Rightarrow> Inr ch)"

definition obs_tr_c :: "var \<Rightarrow> trace \<Rightarrow> obs_event_c list" where
  "obs_tr_c l = map (obs_block_c l)"

definition low_obs_c :: "var \<Rightarrow> (('lvar, 'lval) exstate) \<Rightarrow> real \<times> obs_event_c list" where
  "low_obs_c l \<phi> = (pproj \<phi> l, obs_tr_c l (tproj \<phi>))"

definition gni_obs_c :: "'lvar \<Rightarrow> 'lvar \<Rightarrow> var \<Rightarrow> (('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "gni_obs_c hi lo l S \<longleftrightarrow>
    (\<forall>\<phi>1 \<in> S. \<forall>\<phi>2 \<in> S. lproj \<phi>1 lo = lproj \<phi>2 lo \<longrightarrow>
      (\<exists>\<phi>3 \<in> S. lproj \<phi>3 hi = lproj \<phi>1 hi
        \<and> lproj \<phi>3 lo = lproj \<phi>2 lo
        \<and> low_obs_c l \<phi>3 = low_obs_c l \<phi>2))"

definition C_L :: proc where "C_L = Cont ode_lin bnd_x"
definition C_R :: proc where "C_R = Cont ode_sq bnd_x"

definition C_sep :: proc where
  "C_sep = IChoice (Seq (Assume (\<lambda>s. s HH2 = 1)) C_L)
                   (Seq (Assume (\<lambda>s. s HH2 = 2)) C_R)"

definition sep_init1 :: "(char, real) exstate" where
  "sep_init1 = ((\<lambda>_. 0)(HI := 1), (\<lambda>_. 0)(HH2 := 1), [])"

definition sep_init2 :: "(char, real) exstate" where
  "sep_init2 = ((\<lambda>_. 0)(HI := 2), (\<lambda>_. 0)(HH2 := 2), [])"

definition S_sep :: "(char, real) exstate set" where
  "S_sep = {sep_init1, sep_init2}"

definition lin_st :: "real \<Rightarrow> state" where
  "lin_st t = ((\<lambda>_. 0)(HH2 := 1))(LL2 := t)"

definition sep_run1 :: "(char, real) exstate" where
  "sep_run1 = ((\<lambda>_. 0)(HI := 1), lin_st 1,
      [WaitBlk 1 (\<lambda>\<tau>. State (lin_st \<tau>)) ({}, {})])"

definition sq_st :: "real \<Rightarrow> state" where
  "sq_st t = (((\<lambda>_. 0)(HH2 := 2))(LL2 := t * t))(CC := t)"

definition sep_run2 :: "(char, real) exstate" where
  "sep_run2 = ((\<lambda>_. 0)(HI := 2), sq_st 1,
      [WaitBlk 1 (\<lambda>\<tau>. State (sq_st \<tau>)) ({}, {})])"

lemma sq_lt1: "(t::real) \<ge> 0 \<Longrightarrow> t < 1 \<Longrightarrow> t * t < 1"
proof -
  assume t0: "0 \<le> t" and t1: "t < 1"
  have "t * t \<le> t * 1" using t0 t1 by (intro mult_left_mono; simp)
  then show "t * t < 1" using t1 by simp
qed

lemma sq_ge1: assumes dp: "(d::real) > 0" and ex: "\<not> (d * d < 1)" shows "1 \<le> d"
proof (rule ccontr)
  assume "\<not> 1 \<le> d" then have dlt: "d < 1" by simp
  have dz: "0 \<le> d" using dp by simp
  from dz dlt have "d * d < 1" by (rule sq_lt1)
  with ex show False by simp
qed


lemma sep_run1_mem:
  "sep_run1 \<in> sem C_sep S_sep"
proof -
  define p1 :: "real \<Rightarrow> state" where "p1 = lin_st"
  have filt1: "{(a, b, t) |a b t. (a, b, t) \<in> S_sep \<and> b HH2 = 1} = {sep_init1}"
    by (auto simp: S_sep_def sep_init1_def sep_init2_def)
  have sol: "ODEsol ode_lin p1 1"
    unfolding p1_def lin_st_def by (rule ode_lin_sol)
  have st1eq: "p1 0 = fst (snd sep_init1)"
    unfolding p1_def lin_st_def sep_init1_def by (rule ext, simp)
  have src: "(fst sep_init1, p1 0, snd (snd sep_init1)) \<in> {sep_init1}"
    by (simp add: sep_init1_def st1eq)
  have bef: "\<forall>t. 0 \<le> t \<and> t < 1 \<longrightarrow> bnd_x (p1 t)"
    by (auto simp: bnd_x_def p1_def lin_st_def)
  have exi: "\<not> bnd_x (p1 1)"
    by (simp add: bnd_x_def p1_def lin_st_def)
  have w: "(fst sep_init1, p1 1,
      snd (snd sep_init1) @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})]) \<in> sem C_L {sep_init1}"
    unfolding C_L_def sem_ode
  proof (rule UnI2)
    show "(fst sep_init1, p1 1,
      snd (snd sep_init1) @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})])
      \<in> {(\<sigma>\<^sub>l, p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l p d.
          (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> {sep_init1} \<and> 0 < d \<and> ODEsol ode_lin p d
           \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> bnd_x (p t)) \<and> \<not> bnd_x (p d) \<and> p 0 = \<sigma>\<^sub>p}"
      apply (rule CollectI)
      apply (rule_tac exI [where x = "fst sep_init1"], rule_tac exI [where x = "p1 0"],
             rule_tac exI [where x = "snd (snd sep_init1)"], rule_tac exI [where x = "p1"],
             rule_tac exI [where x = "1"])
      apply (intro conjI)
        apply (rule refl)
       apply (rule src)
       apply simp
       apply (rule sol)
      apply (rule bef)
      apply (rule exi)
      apply (rule refl)
      done
  qed
  have w2: "(fst sep_init1, p1 1,
      snd (snd sep_init1) @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})]) \<in> sem C_L {(a, b, t) |a b t. (a, b, t) \<in> S_sep \<and> b HH2 = 1}"
    by (simp only: filt1, rule w)
  have w3: "(fst sep_init1, p1 1,
      snd (snd sep_init1) @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})]) \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 1)) C_L) S_sep"
    using w2 by (simp add: sem_seq sem_assume)
  have eq: "sep_run1 = (fst sep_init1, p1 1,
      snd (snd sep_init1) @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})])"
    by (simp add: sep_run1_def sep_init1_def p1_def)
  from w3 [folded eq] show ?thesis
    unfolding C_sep_def sem_if by (rule UnI1)
qed


lemma sep_run2_mem:
  "sep_run2 \<in> sem C_sep S_sep"
proof -
  define p2 :: "real \<Rightarrow> state" where "p2 = sq_st"
  have filt2: "{(a, b, t) |a b t. (a, b, t) \<in> S_sep \<and> b HH2 = 2} = {sep_init2}"
    by (auto simp: S_sep_def sep_init1_def sep_init2_def)
  have sol2: "ODEsol ode_sq p2 1"
    unfolding p2_def sq_st_def by (rule ode_sq_sol)
  have st2eq: "p2 0 = fst (snd sep_init2)"
    unfolding p2_def sq_st_def sep_init2_def by (rule ext, simp)
  have src: "(fst sep_init2, p2 0, snd (snd sep_init2)) \<in> {sep_init2}"
    by (simp add: sep_init2_def st2eq)
  have bef: "\<forall>t. 0 \<le> t \<and> t < 1 \<longrightarrow> bnd_x (p2 t)"
  proof (intro allI impI)
    fix t :: real assume t01: "0 \<le> t \<and> t < 1"
    then have t0: "0 \<le> t" and t1: "t < 1" by simp_all
    from sq_lt1 [OF t0 t1] have "t * t < 1" .
    then show "bnd_x (p2 t)" by (simp add: bnd_x_def p2_def sq_st_def)
  qed
  have exi: "\<not> bnd_x (p2 1)"
    by (simp add: bnd_x_def p2_def sq_st_def)
  have w: "(fst sep_init2, p2 1,
      snd (snd sep_init2) @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]) \<in> sem C_R {sep_init2}"
    unfolding C_R_def sem_ode
  proof (rule UnI2)
    show "(fst sep_init2, p2 1,
      snd (snd sep_init2) @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})])
      \<in> {(\<sigma>\<^sub>l, p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l p d.
          (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> {sep_init2} \<and> 0 < d \<and> ODEsol ode_sq p d
           \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> bnd_x (p t)) \<and> \<not> bnd_x (p d) \<and> p 0 = \<sigma>\<^sub>p}"
      apply (rule CollectI)
      apply (rule_tac exI [where x = "fst sep_init2"], rule_tac exI [where x = "p2 0"],
             rule_tac exI [where x = "snd (snd sep_init2)"], rule_tac exI [where x = "p2"],
             rule_tac exI [where x = "1"])
      apply (intro conjI)
        apply (rule refl)
       apply (rule src)
       apply simp
       apply (rule sol2)
      apply (rule bef)
      apply (rule exi)
      apply (rule refl)
      done
  qed
  have w2: "(fst sep_init2, p2 1,
      snd (snd sep_init2) @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]) \<in> sem C_R {(a, b, t) |a b t. (a, b, t) \<in> S_sep \<and> b HH2 = 2}"
    by (simp only: filt2, rule w)
  have w3: "(fst sep_init2, p2 1,
      snd (snd sep_init2) @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]) \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 2)) C_R) S_sep"
    using w2 by (simp add: sem_seq sem_assume)
  have eq: "sep_run2 = (fst sep_init2, p2 1,
      snd (snd sep_init2) @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})])"
    by (simp add: sep_run2_def sep_init2_def p2_def)
  from w3 [folded eq] show ?thesis
    unfolding C_sep_def sem_if by (rule UnI2)
qed

lemma sep_mem_cases:
  assumes m: "\<phi> \<in> sem C_sep S_sep"
  shows "(\<exists>p d. 0 < d \<and> ODEsol ode_lin p d \<and> p 0 = (\<lambda>_. 0)(HH2 := 1)
           \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1) \<and> \<not> (p d LL2 < 1)
           \<and> \<phi> = ((\<lambda>_::char. 0::real)(HI := 1), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]))
     \<or> (\<exists>p d. 0 < d \<and> ODEsol ode_sq p d \<and> p 0 = (\<lambda>_. 0)(HH2 := 2)
           \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1) \<and> \<not> (p d LL2 < 1)
           \<and> \<phi> = ((\<lambda>_::char. 0::real)(HI := 2), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]))"
proof -
  from m have "(\<phi> \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 1)) C_L) S_sep)
            \<or> (\<phi> \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 2)) C_R) S_sep)"
    unfolding C_sep_def sem_if by blast
  then show ?thesis
  proof (elim disjE exE conjE)
    assume l: "\<phi> \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 1)) C_L) S_sep"
    from l [unfolded sem_seq sem_assume] consider
        (inst) a b t where "(a, b, t) \<in> S_sep" "b HH2 = 1" "\<not> bnd_x b" "\<phi> = (a, b, t)"
      | (wait) a b t p d where "(a, b, t) \<in> S_sep" "b HH2 = 1" "0 < d"
          "ODEsol ode_lin p d" "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> bnd_x (p t))"
          "\<not> bnd_x (p d)" "p 0 = b"
          "\<phi> = (a, p d, t @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      unfolding C_L_def sem_ode by blast
    then show ?thesis
    proof cases
      case inst
      then show ?thesis by (auto simp: S_sep_def sep_init1_def sep_init2_def bnd_x_def)
    next
      case wait
      from wait(1) wait(2) have abc: "a = (\<lambda>_::char. 0::real)(HI := 1)"
        "b = (\<lambda>_. 0::real)(HH2 := 1)" "t = []"
        by (auto simp: S_sep_def sep_init1_def sep_init2_def)
      show ?thesis
      proof (rule disjI1, rule_tac x = p in exI, rule_tac x = d in exI, intro conjI)
        show "0 < d" by (rule wait(3))
        show "ODEsol ode_lin p d" by (rule wait(4))
        show "p 0 = (\<lambda>_. 0::real)(HH2 := 1)" using wait(7) abc(2) by simp
        show "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
          using wait(5) unfolding bnd_x_def by simp
        show "\<not> (p d LL2 < 1)" using wait(6) unfolding bnd_x_def by simp
        show "\<phi> = ((\<lambda>_::char. 0::real)(HI := 1), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
          using wait(8) abc by simp
      qed
    qed
  next
    assume r: "\<phi> \<in> sem (Seq (Assume (\<lambda>s. s HH2 = 2)) C_R) S_sep"
    from r [unfolded sem_seq sem_assume] consider
        (inst) a b t where "(a, b, t) \<in> S_sep" "b HH2 = 2" "\<not> bnd_x b" "\<phi> = (a, b, t)"
      | (wait) a b t p d where "(a, b, t) \<in> S_sep" "b HH2 = 2" "0 < d"
          "ODEsol ode_sq p d" "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> bnd_x (p t))"
          "\<not> bnd_x (p d)" "p 0 = b"
          "\<phi> = (a, p d, t @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      unfolding C_R_def sem_ode by blast
    then show ?thesis
    proof cases
      case inst
      then show ?thesis by (auto simp: S_sep_def sep_init1_def sep_init2_def bnd_x_def)
    next
      case wait
      from wait(1) wait(2) have abc: "a = (\<lambda>_::char. 0::real)(HI := 2)"
        "b = (\<lambda>_. 0::real)(HH2 := 2)" "t = []"
        by (auto simp: S_sep_def sep_init1_def sep_init2_def)
      show ?thesis
      proof (rule disjI2, rule_tac x = p in exI, rule_tac x = d in exI, intro conjI)
        show "0 < d" by (rule wait(3))
        show "ODEsol ode_sq p d" by (rule wait(4))
        show "p 0 = (\<lambda>_. 0::real)(HH2 := 2)" using wait(7) abc(2) by simp
        show "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
          using wait(5) unfolding bnd_x_def by simp
        show "\<not> (p d LL2 < 1)" using wait(6) unfolding bnd_x_def by simp
        show "\<phi> = ((\<lambda>_::char. 0::real)(HI := 2), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
          using wait(8) abc by simp
      qed
    qed
  qed
qed


subsection \<open>Exit times for the two branches\<close>


lemma sep_exit_lin:
  assumes sol: "ODEsol ode_lin p d" and p0: "p 0 = (\<lambda>_. 0)(HH2 := 1)"
      and dp: "0 < d"
      and bef: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
      and ex: "\<not> (p d LL2 < 1)"
  shows "d = 1" and "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = t"
proof -
  from ode_lin_char [OF sol]
  have ch: "\<forall>t\<in>{0..d}. p t LL2 = p 0 LL2 + t \<and> p t CC = p 0 CC" .
  have p0l: "p 0 LL2 = 0" using p0 by simp
  have chL: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = p 0 LL2 + t"
  proof -
    fix t assume tm: "t \<in> {0..d}"
    from ch [rule_format, OF tm] show "p t LL2 = p 0 LL2 + t" by simp
  qed
  show chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = t"
  proof -
    fix t assume "t \<in> {0..d}"
    from chL [OF this] show "p t LL2 = t" using p0l by simp
  qed
  have dge: "1 \<le> d"
  proof -
    have "d \<in> {0..d}" using dp by simp
    then have "p d LL2 = d" by (rule chl)
    with ex show "1 \<le> d" by simp
  qed
  show "d = 1"
  proof (rule ccontr)
    assume "d \<noteq> 1"
    with dge have "1 < d" by simp
    moreover have "p 1 LL2 = 1" using chl [of 1] dge by simp
    ultimately show False using bef [rule_format, of 1] by simp
  qed
qed

lemma sep_exit_sq:
  assumes sol: "ODEsol ode_sq p d" and p0: "p 0 = (\<lambda>_. 0)(HH2 := 2)"
      and dp: "0 < d"
      and bef: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
      and ex: "\<not> (p d LL2 < 1)"
  shows "d = 1" and "\<And>t. t \<in> {0..d} \<Longrightarrow> p t CC = t \<and> p t LL2 = t * t"
proof -
  from ode_sq_char [OF sol] have ch: "\<forall>t\<in>{0..d}. p t CC = p 0 CC + t
    \<and> p t LL2 = (p t CC)\<^sup>2 - (p 0 CC)\<^sup>2 + p 0 LL2" .
  have p0l: "p 0 CC = 0" "p 0 LL2 = 0" using p0 by simp_all
  have chCC: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t CC = p 0 CC + t"
  proof -
    fix t assume tm: "t \<in> {0..d}"
    from ch [rule_format, OF tm] show "p t CC = p 0 CC + t" by simp
  qed
  have chL2: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = (p t CC)\<^sup>2 - (p 0 CC)\<^sup>2 + p 0 LL2"
  proof -
    fix t assume tm: "t \<in> {0..d}"
    from ch [rule_format, OF tm] show "p t LL2 = (p t CC)\<^sup>2 - (p 0 CC)\<^sup>2 + p 0 LL2" by simp
  qed
  show chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t CC = t \<and> p t LL2 = t * t"
  proof -
    fix t assume td: "t \<in> {0..d}"
    from chCC [OF td] have cc: "p t CC = t" using p0l(1) by simp
    from chL2 [OF td] cc p0l have "p t LL2 = t * t"
      by (simp add: power2_eq_square)
    with cc show "p t CC = t \<and> p t LL2 = t * t" by simp
  qed
  have dge: "1 \<le> d"
  proof -
    have "d \<in> {0..d}" using dp by simp
    then have "p d LL2 = d * d" using chl by simp
    with ex dp show "1 \<le> d" by (metis sq_ge1)
  qed
  show "d = 1"
  proof (rule ccontr)
    assume "d \<noteq> 1"
    with dge have "1 < d" by simp
    moreover have "p 1 LL2 = 1 * 1" using chl [of 1] dge by simp
    ultimately have "p 1 LL2 = 1" by simp
    with bef [rule_format, of 1] \<open>1 < d\<close> show False by simp
  qed
qed


subsection \<open>F7(a): the two separation theorems\<close>

theorem curve_leak_gni_obs_c_fails:
  "\<not> gni_obs_c HI LO LL2 (sem C_sep S_sep)"
proof -
  have loeq: "lproj sep_run1 LO = lproj sep_run2 LO"
    by (simp add: sep_run1_def sep_run2_def lproj_def)
  show ?thesis
  proof
    assume g: "gni_obs_c HI LO LL2 (sem C_sep S_sep)"
    from g [unfolded gni_obs_c_def, rule_format, OF sep_run1_mem sep_run2_mem loeq]
    obtain \<phi>3 where w3: "\<phi>3 \<in> sem C_sep S_sep"
      "lproj \<phi>3 HI = lproj sep_run1 HI"
      "lproj \<phi>3 LO = lproj sep_run2 LO"
      "low_obs_c LL2 \<phi>3 = low_obs_c LL2 sep_run2" by blast
    from sep_mem_cases [OF w3(1)] show False
    proof (elim disjE exE conjE)
      fix p d
      assume dp: "0 < d" and sol: "ODEsol ode_lin p d"
        and p0: "p 0 = (\<lambda>_. 0::real)(HH2 := 1)"
        and bef: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
        and ex: "\<not> (p d LL2 < 1)"
        and eq: "\<phi>3 = ((\<lambda>_::char. 0::real)(HI := 1), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      from sep_exit_lin [OF sol p0 dp bef ex] have d1: "d = 1"
        and chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = t" by blast+
      from w3(4) eq d1 have cveq:
        "low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p \<tau>))
          = low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (sq_st \<tau>))"
        by (simp add: low_obs_c_def obs_tr_c_def obs_block_c_def pproj_def tproj_def
                      sep_run2_def sq_st_def power2_eq_square WaitBlk_def)
      have half: "(1/2 :: real) \<in> {0..1}" by simp
      have lhs: "low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p \<tau>)) (1/2) = 1/2"
        using chl [of "1/2"] half d1
        by (simp add: low_curve_def restrict_apply')
      have rhs: "low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (sq_st \<tau>)) (1/2) = 1/4"
        using half by (simp add: low_curve_def restrict_apply' sq_st_def)
      from fun_cong [OF cveq, of "1/2"] lhs rhs show False by simp
    next
      fix p d
      assume dp: "0 < d" and sol: "ODEsol ode_sq p d"
        and p0: "p 0 = (\<lambda>_. 0::real)(HH2 := 2)"
        and eq: "\<phi>3 = ((\<lambda>_::char. 0::real)(HI := 2), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      from eq have "lproj \<phi>3 HI = ((\<lambda>_::char. 0::real)(HI := 2)) HI" by (simp add: lproj_def)
      with w3(2) show False by (simp add: sep_run1_def lproj_def)
    qed
  qed
qed

lemma sep_obs_c_common:
  assumes m: "\<phi> \<in> sem C_sep S_sep"
  shows "low_obs LL2 \<phi> = (1, [Inl 1])"
proof -
  from sep_mem_cases [OF m] show ?thesis
  proof (elim disjE exE conjE)
    fix p d
    assume dp: "0 < d" and sol: "ODEsol ode_lin p d"
      and p0: "p 0 = (\<lambda>_. 0::real)(HH2 := 1)"
      and bef: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
      and ex: "\<not> (p d LL2 < 1)"
      and eq: "\<phi> = ((\<lambda>_::char. 0::real)(HI := 1), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
    from sep_exit_lin [OF sol p0 dp bef ex] have d1: "d = 1"
      and chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t LL2 = t" by blast+
    have "p 1 LL2 = 1" using chl [of 1] d1 by simp
    with eq d1 show ?thesis
      by (simp add: low_obs_def obs_tr_def obs_block_def WaitBlk_def pproj_def tproj_def)
  next
    fix p d
    assume dp: "0 < d" and sol: "ODEsol ode_sq p d"
      and p0: "p 0 = (\<lambda>_. 0::real)(HH2 := 2)"
      and bef: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> p t LL2 < 1"
      and ex: "\<not> (p d LL2 < 1)"
      and eq: "\<phi> = ((\<lambda>_::char. 0::real)(HI := 2), p d,
                 [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
    from sep_exit_sq [OF sol p0 dp bef ex] have d1: "d = 1"
      and chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t CC = t \<and> p t LL2 = t * t" by blast+
    have "p 1 LL2 = 1 * 1" using chl [of 1] d1 by simp
    hence "p 1 LL2 = 1" by simp
    with eq d1 show ?thesis
      by (simp add: low_obs_def obs_tr_def obs_block_def WaitBlk_def pproj_def tproj_def)
  qed
qed

theorem duration_only_gni_obs_holds:
  "gni_obs HI LO LL2 (sem C_sep S_sep)"
proof (unfold gni_obs_def, rule ballI, rule ballI, rule impI)
  fix \<phi>1 \<phi>2
  assume m1: "\<phi>1 \<in> sem C_sep S_sep" and m2: "\<phi>2 \<in> sem C_sep S_sep"
     and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
  from sep_obs_c_common [OF m1] have o1: "low_obs LL2 \<phi>1 = (1, [Inl 1])" .
  from sep_obs_c_common [OF m2] have o2: "low_obs LL2 \<phi>2 = (1, [Inl 1])" .
  have key: "\<exists>\<phi>3 \<in> sem C_sep S_sep. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2"
    apply (rule_tac x = "\<phi>1" in bexI)
     apply (simp add: o1 o2 loeq)
    apply (rule m1)
    done
  from key show "\<exists>\<phi>3 \<in> sem C_sep S_sep. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs LL2 \<phi>3 = low_obs LL2 \<phi>2" by blast
qed




subsection \<open>Positive example with an ODE: havoc followed by a clock\<close>

definition cc_zero :: "(('lvar, 'lval) exstate) set \<Rightarrow> bool" where
  "cc_zero S \<longleftrightarrow> (\<forall>\<phi>\<in>S. pproj \<phi> CC = 0)"

lemma havoc_preserves_cc_zero:
  assumes neq: "x \<noteq> CC" and cz: "cc_zero S"
  shows "cc_zero (sem (Havoc x) S)"
proof (unfold cc_zero_def, rule ballI)
  fix \<phi>' assume m: "\<phi>' \<in> sem (Havoc x) S"
  then obtain \<sigma>\<^sub>l \<sigma>\<^sub>p l v where pd: "\<phi>' = (\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := v), l)"
    and src: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S"
    unfolding sem_havoc by blast
  from cz [unfolded cc_zero_def, rule_format, OF src]
  have "pproj (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) CC = 0" .
  then show "pproj \<phi>' CC = 0" using pd neq by (simp add: pproj_def)
qed

definition C_cl :: proc where "C_cl = Cont ode_cl bnd_c"
definition C_hyb :: proc where "C_hyb = Seq (Havoc HH2) C_cl"

lemma low_curve_eq_const:
  assumes d1: "\<And>s. s \<in> {0..d} \<Longrightarrow> p1 s l = c"
      and d2: "\<And>s. s \<in> {0..d} \<Longrightarrow> p2 s l = c"
  shows "low_curve l (\<lambda>\<tau>\<in>{0..d}. State (p1 \<tau>)) = low_curve l (\<lambda>\<tau>\<in>{0..d}. State (p2 \<tau>))"
  apply (rule ext)
  unfolding low_curve_def
  by (auto simp: restrict_apply d1 d2 split: if_splits)

lemma gni_obs_c_havoc_cont_set:
  assumes lc: "low_const LL2 c S"
      and tc: "t_const_at tr S"
      and cz: "cc_zero S"
  shows "gni_obs_c HI LO LL2 (sem C_hyb (S :: ((char, real) exstate) set))"
proof -
  have h1l: "low_const LL2 c (sem (Havoc HH2) S)"
    using havoc_preserves_low [OF HH2_LL2_neq(1)] lc
    unfolding hyper_hoare_triple_def by blast
  have h1t: "t_const_at tr (sem (Havoc HH2) S)"
    using havoc_preserves_tconst tc
    unfolding hyper_hoare_triple_def by blast
  have h1c: "cc_zero (sem (Havoc HH2) S)"
    by (rule havoc_preserves_cc_zero [OF CC_HH2_neq(2) cz])
  have char: "\<And>\<phi>. \<phi> \<in> sem C_hyb S \<Longrightarrow>
      (\<exists>a q p. p 0 = q \<and> ODEsol ode_cl p 1
        \<and> (\<forall>t\<in>{0..1}. p t CC = t \<and> p t LL2 = q LL2)
        \<and> q LL2 = c \<and> tproj (a, q, tr) = tr
        \<and> \<phi> = (a, p 1, tr @ [WaitBlk 1 (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]))"
  proof -
    fix \<phi> assume m: "\<phi> \<in> sem C_hyb S"
    then have m': "\<phi> \<in> sem C_cl (sem (Havoc HH2) S)"
      by (simp add: C_hyb_def sem_seq)
    from m' [unfolded C_cl_def sem_ode] consider
        (inst) a b t where "(a, b, t) \<in> sem (Havoc HH2) S" "\<not> bnd_c b" "\<phi> = (a, b, t)"
      | (wait) a b t p d where "(a, b, t) \<in> sem (Havoc HH2) S" "0 < d"
          "ODEsol ode_cl p d" "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> bnd_c (p t))"
          "\<not> bnd_c (p d)" "p 0 = b"
          "\<phi> = (a, p d, t @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      by blast
    then show "(\<exists>a q p. p 0 = q \<and> ODEsol ode_cl p 1
        \<and> (\<forall>t\<in>{0..1}. p t CC = t \<and> p t LL2 = q LL2)
        \<and> q LL2 = c \<and> tproj (a, q, tr) = tr
        \<and> \<phi> = (a, p 1, tr @ [WaitBlk 1 (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]))"
    proof cases
      case inst
      from inst(1) have "pproj (a, b, t) CC = 0" using h1c by (simp add: cc_zero_def)
      with inst(2) have False by (simp add: bnd_c_def pproj_def)
      then show ?thesis by blast
    next
      case wait
      have bz: "b CC = 0"
        using h1c [unfolded cc_zero_def, rule_format, OF wait(1)]
        by (simp add: pproj_def)
      have tz: "t = tr"
        using h1t [unfolded t_const_at_def, rule_format, OF wait(1)]
        by (simp add: tproj_def)
      from ode_cl_char [OF wait(3)] have ch: "\<forall>t\<in>{0..d}. p t CC = p 0 CC + t
        \<and> (\<forall>a. a \<noteq> CC \<longrightarrow> p t a = p 0 a)" .
      have chl: "\<And>t. t \<in> {0..d} \<Longrightarrow> p t CC = t \<and> p t LL2 = b LL2"
        using ch wait(6) bz by simp
      have dge: "1 \<le> d"
      proof -
        have "d \<in> {0..d}" using wait(2) by simp
        then have "p d CC = d" using chl by simp
        with wait(5) show "1 \<le> d" by (simp add: bnd_c_def)
      qed
      have d1: "d = 1"
      proof (rule ccontr)
        assume "d \<noteq> 1"
        with dge have gt: "1 < d" by simp
        have p1: "p 1 CC = 1" using chl [of 1] dge by simp
        have g1: "bnd_c (p 1)" using wait(4) gt by simp
        from g1 p1 have False by (simp add: bnd_c_def)
        then show False .
      qed
      have q0: "b LL2 = c"
        using h1l [unfolded low_const_def, rule_format, OF wait(1)]
        by (simp add: pproj_def)
      show ?thesis
      proof (rule_tac x = a in exI, rule_tac x = b in exI, rule_tac x = p in exI,
             intro conjI)
        show "p 0 = b" by (rule wait(6))
        show "ODEsol ode_cl p 1" using wait(3) d1 by simp
        show "\<forall>t\<in>{0..1}. p t CC = t \<and> p t LL2 = b LL2" using chl d1 by simp
        show "b LL2 = c" by (rule q0)
        show "tproj (a, b, tr) = tr" by (simp add: tproj_def)
        show "\<phi> = (a, p 1, tr @ [WaitBlk 1 (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
          using wait(7) tz d1 by simp
      qed
    qed
  qed
  show ?thesis
  proof (unfold gni_obs_c_def, rule ballI, rule ballI, rule impI)
    fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> sem C_hyb S" and m2: "\<phi>2 \<in> sem C_hyb S"
       and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
    from char [OF m1] obtain a1 q1 p1 where
      s1: "p1 0 = q1" "ODEsol ode_cl p1 1"
          "\<forall>t\<in>{0..1}. p1 t CC = t \<and> p1 t LL2 = q1 LL2"
          "q1 LL2 = c"
          "\<phi>1 = (a1, p1 1, tr @ [WaitBlk 1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})])" by blast
    from char [OF m2] obtain a2 q2 p2 where
      s2: "p2 0 = q2" "ODEsol ode_cl p2 1"
          "\<forall>t\<in>{0..1}. p2 t CC = t \<and> p2 t LL2 = q2 LL2"
          "q2 LL2 = c"
          "\<phi>2 = (a2, p2 1, tr @ [WaitBlk 1 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})])" by blast
    have c1: "p1 1 LL2 = c" using s1(3) s1(4) by simp
    have c2: "p2 1 LL2 = c" using s2(3) s2(4) by simp
    have obs1: "low_obs_c LL2 \<phi>1
      = (c, obs_tr_c LL2 tr @ [Inl (1, low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p1 \<tau>)))])"
      unfolding low_obs_c_def obs_tr_c_def obs_block_c_def
      by (simp add: s1(5) WaitBlk_def c1 tproj_def pproj_def)
    have obs2: "low_obs_c LL2 \<phi>2
      = (c, obs_tr_c LL2 tr @ [Inl (1, low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p2 \<tau>)))])"
      unfolding low_obs_c_def obs_tr_c_def obs_block_c_def
      by (simp add: s2(5) WaitBlk_def c2 tproj_def pproj_def)
    have curve_eq: "low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p1 \<tau>))
      = low_curve LL2 (\<lambda>\<tau>\<in>{0..1}. State (p2 \<tau>))"
    proof (rule low_curve_eq_const)
      fix s :: real assume "s \<in> {0..1}"
      with s1(3) s1(4) show "p1 s LL2 = c" by simp
    next
      fix s :: real assume "s \<in> {0..1}"
      with s2(3) s2(4) show "p2 s LL2 = c" by simp
    qed
    have key: "\<exists>\<phi>3 \<in> sem C_hyb S. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs_c LL2 \<phi>3 = low_obs_c LL2 \<phi>2"
      apply (rule_tac x = "\<phi>1" in bexI)
       apply (simp add: obs1 obs2 curve_eq loeq)
      apply (rule m1)
      done
    show "\<exists>\<phi>3 \<in> sem C_hyb S. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs_c LL2 \<phi>3 = low_obs_c LL2 \<phi>2"
      by (rule key)
  qed
qed

theorem gni_obs_c_havoc_cont:
  "hyper_hoare_triple ((\<lambda>S. low_agree LL2 S \<and> t_const_at tr S \<and> cc_zero S)
        :: ((char, real) exstate) set \<Rightarrow> bool)
       C_hyb (gni_obs_c HI LO LL2)"
proof (rule hyper_hoare_tripleI)
  fix S :: "(char, real) exstate set"
  assume pre: "low_agree LL2 S \<and> t_const_at tr S \<and> cc_zero S"
  then obtain c where c: "low_const LL2 c S" by (auto simp: low_agree_def)
  from pre have tc: "t_const_at tr S" and cz: "cc_zero S" by blast+
  from c tc cz show "gni_obs_c HI LO LL2 (sem C_hyb S)"
    by (rule gni_obs_c_havoc_cont_set)
qed


end
