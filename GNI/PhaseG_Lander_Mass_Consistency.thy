theory PhaseG_Lander_Mass_Consistency
  imports PhaseG_Lander_MassModel
begin

section \<open>Consistency of the mass-sensitive lander field (P0.2)\<close>

text \<open>
Acceptance item P0.2 (\<^emph>\<open>H3L unified framework acceptance 2026-09-26\<close>):
prove that the candidate mass model of \<^theory_text>\<open>PhaseG_Lander_MassModel\<close>
is internally consistent, without reusing the old \<^term>\<open>Lander_Refine\<close>.

  \<^item> \<^bold>\<open>M positivity\<close>: along any solution of the mass field,
    \<^term>\<open>p t M = p 0 M - (p 0 Fc) * t / 2500\<close> (\<^term>\<open>Fc\<close> is constant),
    so with \<^term>\<open>0 \<le> s Fc\<close> and \<^term>\<open>s Fc \<le> Fmax\<close> the mass stays positive for any
    duration up to \<^term>\<open>Period\<close> whenever
    \<^term>\<open>Fmax * Period < 2500 * p 0 M\<close>: the guard \<^term>\<open>0 < s M\<close> can
    only be violated because of the clock, never because of the mass.

  \<^item> \<^bold>\<open>Fc = M * W compatibility\<close>: the relation \<^term>\<open>s Fc = s M * s W\<close> is
    preserved by the four-dimensional field whenever it holds initially
    (a single-run differential certificate via the mean-value theorem).

  \<^item> \<^bold>\<open>W positivity and closed-form bound\<close>: W' = W^2/2500 is
    nondecreasing while nonnegative; from a positive initial value one gets
    the exact relation 1/W t = 1/W 0 - t/2500, giving the
    explicit upper bound used by the actuator margin.

  \<^item> \<^bold>\<open>Low observation simulation\<close>: under Fc = M*W and
    the guard \<^term>\<open>0 < s M\<close>, the (V,W,T)-dynamics of the mass field coincides with
    the normalized field of the original lander; the simulated run freezes
    the mass and produces the very same low observation.

All component lemmas are stated inside a locale for an abstract field
agreeing with \<^const>\<open>lander_mass_field\<close> on the \<^term>\<open>Fc\<close>, \<^term>\<open>M\<close>
and \<^term>\<open>W\<close> components, so they apply to both
\<^const>\<open>lander_mass_field\<close> and \<^const>\<open>lander_mass_clock_field\<close>.
\<close>


subsection \<open>Variable distinctness and field values\<close>

lemma lander_vars_neq [simp]:
  "Fc \<noteq> M" "Fc \<noteq> V" "Fc \<noteq> T" "Fc \<noteq> W"
  "M \<noteq> Fc" "M \<noteq> V" "M \<noteq> T" "M \<noteq> W"
  "V \<noteq> Fc" "V \<noteq> M" "V \<noteq> T" "V \<noteq> W"
  "T \<noteq> Fc" "T \<noteq> M" "T \<noteq> V" "T \<noteq> W"
  "W \<noteq> Fc" "W \<noteq> M" "W \<noteq> V" "W \<noteq> T"
  unfolding Fc_def M_def V_def T_def W_def by auto

lemma mass_field_simps [simp]:
  "lander_mass_field V s = s Fc / s M - 3.732"
  "lander_mass_field M s = -(s Fc) / 2500"
  "lander_mass_field Fc s = 0"
  "lander_mass_field W s = (s W)\<^sup>2 / 2500"
  "x \<noteq> V \<Longrightarrow> x \<noteq> M \<Longrightarrow> x \<noteq> Fc \<Longrightarrow> x \<noteq> W \<Longrightarrow> lander_mass_field x s = 0"
  unfolding lander_mass_field_def by simp_all

lemma mass_clock_field_simps [simp]:
  "lander_mass_clock_field V s = s Fc / s M - 3.732"
  "lander_mass_clock_field M s = -(s Fc) / 2500"
  "lander_mass_clock_field Fc s = 0"
  "lander_mass_clock_field W s = (s W)\<^sup>2 / 2500"
  "lander_mass_clock_field T s = 1"
  "x \<noteq> V \<Longrightarrow> x \<noteq> M \<Longrightarrow> x \<noteq> Fc \<Longrightarrow> x \<noteq> W \<Longrightarrow> x \<noteq> T \<Longrightarrow>
     lander_mass_clock_field x s = 0"
  unfolding lander_mass_clock_field_def lander_mass_field_def by simp_all


subsection \<open>A congruence lemma for vector derivatives\<close>

lemma vderiv_on_cong_rates:
  fixes f q q' :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes h: "(f has_vderiv_on q) S"
    and eq: "\<And>t. t \<in> S \<Longrightarrow> q t = q' t"
  shows "(f has_vderiv_on q') S"
  unfolding has_vderiv_on_def
proof
  fix t assume "t \<in> S"
  from h[unfolded has_vderiv_on_def, rule_format, OF this]
  have "(f has_vector_derivative (q t)) (at t within S)" .
  then show "(f has_vector_derivative (q' t)) (at t within S)"
    unfolding has_vector_derivative_def using eq[OF \<open>t \<in> S\<close>] by simp
qed


subsection \<open>Componentwise characterisations (abstract field)\<close>

locale mass_field =
  fixes f :: "var \<Rightarrow> state \<Rightarrow> real"
  assumes fFc [simp]: "\<And>s. f Fc s = 0"
    and fM [simp]: "\<And>s. f M s = -(s Fc) / 2500"
    and fW [simp]: "\<And>s. f W s = (s W)\<^sup>2 / 2500"
begin

lemma vderiv: "ODEsol (ODE f) p d \<Longrightarrow>
  ((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {0..d}"
  using ODEsol_component_vderiv by simp

lemma Fc_const:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}"
  shows "p t Fc = p 0 Fc"
proof -
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u Fc) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
    using vderiv[OF sol, of Fc] t
    unfolding has_vderiv_on_def has_vector_derivative_def by simp
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  from mvt_real_eq[OF der d0 _ t] show ?thesis by simp
qed

lemma M_char:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}"
  shows "p t M = p 0 M - (p 0 Fc) * t / 2500"
proof -
  define c where "c = -(p 0 Fc) / 2500"
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u M - c * u) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have pv0: "((\<lambda>u. p u M) has_derivative (\<lambda>h. h *\<^sub>R (-(p u Fc) / 2500)))
        (at u within {0..d})"
      using vderiv[OF sol, of M] u
      unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have pv: "((\<lambda>u. p u M) has_derivative (\<lambda>h. h *\<^sub>R c)) (at u within {0..d})"
      apply (rule has_derivative_eq_rhs[OF pv0])
      using Fc_const[OF sol u] by (simp add: c_def)
    have cv: "((\<lambda>u. c * u) has_derivative (\<lambda>h. h *\<^sub>R c)) (at u within {0..d})"
      apply (rule has_derivative_eq_rhs[OF has_derivative_mult_right])
       apply (rule has_derivative_ident)
      by (simp add: mult.commute)
    show "((\<lambda>u. p u M - c * u) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
      using has_derivative_diff[OF pv cv] by simp
  qed
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  have "p 0 M - c * 0 = p t M - c * t"
    by (rule mvt_real_eq[OF der d0 _ t], simp)
  then show ?thesis unfolding c_def by simp
qed

lemma M_lower:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}"
    and fmax: "0 \<le> p 0 Fc" "p 0 Fc \<le> Fmax"
  shows "p 0 M - Fmax * t / 2500 \<le> p t M"
proof -
  have t0: "0 \<le> t" using t by auto
  have "(p 0 Fc) * t / 2500 \<le> Fmax * t / 2500"
    by (intro mult_right_mono divide_right_mono)
       (use fmax t0 in auto)
  with M_char[OF sol t] show ?thesis by linarith
qed

lemma M_pos_margin:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}"
    and fmax: "0 \<le> p 0 Fc" "p 0 Fc \<le> Fmax" and fmax0: "0 \<le> Fmax"
    and margin: "Fmax * d < 2500 * p 0 M"
  shows "0 < p t M"
proof -
  have ge: "p 0 M - Fmax * t / 2500 \<le> p t M" by (rule M_lower[OF sol t fmax])
  have "Fmax * t / 2500 \<le> Fmax * d / 2500"
    by (intro mult_left_mono divide_right_mono)
       (use t sol fmax0 in auto)
  with ge margin show ?thesis by linarith
qed

lemma W_mono:
  assumes sol: "ODEsol (ODE f) p d" and s: "s \<in> {0..d}" and t: "t \<in> {0..d}" and st: "s \<le> t"
  shows "p s W \<le> p t W"
proof -
  have sub: "{s..t} \<subseteq> {0..d}" using s t st by auto
  have der: "\<And>x. x \<in> {s..t} \<Longrightarrow>
      ((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p x W)\<^sup>2 / 2500))) (at x within {s..t})"
  proof -
    fix x assume x: "x \<in> {s..t}"
    have x0: "x \<in> {0..d}" using x sub by auto
    from vderiv[OF sol, of W] have
      hvd: "\<And>tt. tt \<in> {0..d} \<Longrightarrow>
        ((\<lambda>u. p u W) has_vector_derivative (f W (p tt))) (at tt within {0..d})"
      unfolding has_vderiv_on_def by blast
    from hvd[OF x0] have
      base: "((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p x W)\<^sup>2 / 2500)))
        (at x within {0..d})"
      unfolding has_vector_derivative_def by simp
    from has_derivative_subset[OF base sub] show
      "((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p x W)\<^sup>2 / 2500))) (at x within {s..t})" .
  qed
  have derI: "\<And>x. \<lbrakk>s \<le> x; x \<le> t\<rbrakk> \<Longrightarrow>
      ((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p x W)\<^sup>2 / 2500))) (at x within {s..t})"
    using der by auto
  from mvt_very_simple[where a = s and b = t and f = "\<lambda>u. p u W"
      and f' = "\<lambda>x h. h *\<^sub>R ((p x W)\<^sup>2 / 2500)", OF st derI]
  obtain x where eq: "p t W - p s W = (t - s) *\<^sub>R ((p x W)\<^sup>2 / 2500)" by blast
  from eq have rate: "p t W - p s W = (t - s) * ((p x W)\<^sup>2 / 2500)"
    by (simp add: real_scaleR_def)
  have ge: "0 \<le> (t - s) * ((p x W)\<^sup>2 / 2500)"
    using st by (simp add: zero_le_square divide_nonneg_nonneg)
  from rate ge show ?thesis by simp
qed

lemma W_pos:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}" and w0: "0 < p 0 W"
  shows "0 < p t W"
proof -
  have z: "0 \<in> {0..d}" using sol unfolding ODEsol_def by simp
  have t0: "0 \<le> t" using t by auto
  have "p 0 W \<le> p t W" by (rule W_mono[OF sol z t t0])
  with w0 show ?thesis by simp
qed

lemma W_inv:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}" and w0: "0 < p 0 W"
  shows "1 / (p t W) = 1 / (p 0 W) - t / 2500"
proof -
  have wpos: "\<And>u. u \<in> {0..d} \<Longrightarrow> p u W \<noteq> 0"
    using W_pos[OF sol _ w0] by force
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. 1 / (p u W) + u / 2500) has_derivative (\<lambda>h. h *\<^sub>R 0))
      (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have wd: "((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p u W)\<^sup>2 / 2500))) (at u within {0..d})"
      using vderiv[OF sol, of W] u
      unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have fd: "((\<lambda>_. 1) has_derivative (\<lambda>h. 0)) (at u within {0..d})"
      by (rule has_derivative_const)
    have div: "((\<lambda>u. 1 / (p u W)) has_derivative
        (\<lambda>h. (0 * (p u W) - 1 * (h *\<^sub>R ((p u W)\<^sup>2 / 2500))) / ((p u W) * (p u W))))
        (at u within {0..d})"
      by (rule has_derivative_divide'[OF fd wd]) (rule wpos[OF u])
    have wne: "p u W \<noteq> 0" by (rule wpos[OF u])
    have diveq: "\<And>h. (0 * (p u W) - 1 * (h *\<^sub>R ((p u W)\<^sup>2 / 2500))) / ((p u W) * (p u W))
        = - h / 2500"
    proof -
      fix h :: real
      have rearr: "h * ((p u W) * (p u W) / 2500) = (h / 2500) * ((p u W) * (p u W))"
        by (simp add: times_divide_eq_left times_divide_eq_right)
      have wwne: "(p u W) * (p u W) \<noteq> 0" using wne by (auto simp: mult_eq_0_iff)
      have first: "(0 * (p u W) - 1 * (h *\<^sub>R ((p u W)\<^sup>2 / 2500))) / ((p u W) * (p u W))
          = - (h * ((p u W)\<^sup>2 / 2500)) / ((p u W) * (p u W))"
        by (simp add: real_scaleR_def)
      have second: "- (h * ((p u W)\<^sup>2 / 2500)) / ((p u W) * (p u W))
          = - ((h / 2500) * ((p u W) * (p u W))) / ((p u W) * (p u W))"
        by (simp only: power2_eq_square rearr)
      have third: "- ((h / 2500) * ((p u W) * (p u W))) / ((p u W) * (p u W))
          = - (h / 2500)"
        using wwne by simp
      from first second third show
        "(0 * (p u W) - 1 * (h *\<^sub>R ((p u W)\<^sup>2 / 2500))) / ((p u W) * (p u W))
          = - h / 2500"
        by simp
    qed
    have div0: "((\<lambda>u. 1 / (p u W)) has_derivative (\<lambda>h. - h / 2500)) (at u within {0..d})"
    proof (rule has_derivative_eq_rhs[OF div])
      show "(\<lambda>h. (0 * (p u W) - 1 * (h *\<^sub>R ((p u W)\<^sup>2 / 2500))) / ((p u W) * (p u W)))
          = (\<lambda>h. - h / 2500)"
        by (rule ext) (rule diveq)
    qed
    have cu: "((\<lambda>u. u / 2500) has_derivative (\<lambda>h. h *\<^sub>R (1 / 2500))) (at u within {0..d})"
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_divide)
       apply (rule has_derivative_ident)
      by (simp add: real_scaleR_def)
    have "((\<lambda>u. 1 / (p u W) + u / 2500) has_derivative
        (\<lambda>h. - h / 2500 + h *\<^sub>R (1 / 2500))) (at u within {0..d})"
      by (rule has_derivative_add[OF div0 cu])
    then show "((\<lambda>u. 1 / (p u W) + u / 2500) has_derivative (\<lambda>h. h *\<^sub>R 0))
        (at u within {0..d})"
      by (simp add: real_scaleR_def)
  qed
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  have "(1 / (p 0 W) + 0 / 2500) = (1 / (p t W) + t / 2500)"
    by (rule mvt_real_eq[OF der d0 _ t], simp)
  with w0 show ?thesis by simp
qed

lemma W_upper:
  assumes sol: "ODEsol (ODE f) p d" and t: "t \<in> {0..d}" and w0: "0 < p 0 W"
  shows "p t W \<le> (p 0 W) / (1 - (p 0 W) * t / 2500)"
proof -
  have inv: "1 / (p t W) = 1 / (p 0 W) - t / 2500"
    by (rule W_inv[OF sol t w0])
  have wpos: "0 < p t W" by (rule W_pos[OF sol t w0])
  have base: "(1 / (p 0 W) - t / 2500) * p t W = 1"
    using inv wpos by (simp add: divide_simps)
  have scale: "(p 0 W) * (1 / (p 0 W) - t / 2500) = 1 - (p 0 W) * t / 2500"
    using w0 by (simp add: field_simps)
  have bound_eq: "(1 - (p 0 W) * t / 2500) * p t W = (p 0 W)"
  proof -
    have "(1 - (p 0 W) * t / 2500) * p t W =
        ((p 0 W) * (1 / (p 0 W) - t / 2500)) * p t W"
      by (simp only: scale)
    also have "\<dots> = (p 0 W) * ((1 / (p 0 W) - t / 2500) * p t W)"
      by (simp add: algebra_simps)
    also have "\<dots> = (p 0 W) * 1" using base by simp
    finally show ?thesis by simp
  qed
  have Bpos: "0 < 1 - (p 0 W) * t / 2500"
  proof (rule ccontr)
    assume "\<not> (0 < 1 - (p 0 W) * t / 2500)"
    then have Bnonpos: "1 - (p 0 W) * t / 2500 \<le> 0" by simp
    then have Bnp: "1 - (p 0 W) * t / 2500 \<le> 0" by simp
    have wpnn: "0 \<le> p t W" using wpos by simp
    from Bnp wpnn have "(1 - (p 0 W) * t / 2500) * p t W \<le> 0"
      by (rule mult_nonpos_nonneg)
    with bound_eq w0 show False by simp
  qed
  from bound_eq Bpos show ?thesis
    by (simp add: divide_simps mult.commute)
qed

end

interpretation mass_field_mass: mass_field lander_mass_field
  by unfold_locales simp_all

interpretation mass_field_clock: mass_field lander_mass_clock_field
  by unfold_locales simp_all


subsection \<open>The Fc = M * W invariant\<close>

text \<open>Single-run differential certificate: the relation \<^term>\<open>s Fc = s M * s W\<close>
is propagated by the field; its Lie derivative vanishes exactly on the
pointwise relation Fc*W = M*W^2, which is implied by
Fc = M*W together with the guard \<^term>\<open>0 < s M\<close>.\<close>

lemma (in mass_field) Fc_MW_invariant:
  assumes sol: "ODEsol (ODE f) p d"
    and lie: "\<And>u. u \<in> {0..<d} \<Longrightarrow> p u Fc * p u W = p u M * (p u W)\<^sup>2"
    and init: "p 0 Fc = p 0 M * p 0 W"
  shows "\<forall>t\<in>{0..d}. p t Fc = p t M * p t W"
proof (intro ballI)
  fix t assume t: "t \<in> {0..d}"
  have der: "\<forall>u\<in>{0..d}. ((\<lambda>u. p u Fc - p u M * p u W)
      has_derivative
      (\<lambda>h. 0 - h * (p u M * (p u W)\<^sup>2 - p u Fc * p u W) / 2500)) (at u within {0..d})"
  proof (intro ballI)
    fix u assume u: "u \<in> {0..d}"
    have vd: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {0..d}"
      using vderiv[OF sol] by simp
    have fd: "((\<lambda>u. p u Fc) has_derivative (\<lambda>h. h *\<^sub>R 0)) (at u within {0..d})"
      using vd[of Fc] u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have md: "((\<lambda>u. p u M) has_derivative (\<lambda>h. h *\<^sub>R (-(p u Fc) / 2500)))
        (at u within {0..d})"
      using vd[of M] u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have wd: "((\<lambda>u. p u W) has_derivative (\<lambda>h. h *\<^sub>R ((p u W)\<^sup>2 / 2500)))
        (at u within {0..d})"
      using vd[of W] u unfolding has_vderiv_on_def has_vector_derivative_def by simp
    have pd: "((\<lambda>u. p u M * p u W) has_derivative
        (\<lambda>h. h * (p u M * (p u W)\<^sup>2 - p u Fc * p u W) / 2500)) (at u within {0..d})"
      apply (rule has_derivative_eq_rhs)
       apply (rule has_derivative_mult[OF md wd])
      by (simp add: real_scaleR_def algebra_simps power2_eq_square
          diff_divide_distrib)
    show "((\<lambda>u. p u Fc - p u M * p u W) has_derivative
        (\<lambda>h. 0 - h * (p u M * (p u W)\<^sup>2 - p u Fc * p u W) / 2500)) (at u within {0..d})"
      by (rule has_derivative_eq_rhs[OF has_derivative_diff[OF fd pd]], simp)
  qed
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  have zerocond: "\<forall>tt\<in>{0..<d}. \<forall>h. 0 - h * (p tt M * (p tt W)\<^sup>2
      - p tt Fc * p tt W) / 2500 = 0"
  proof (intro ballI allI)
    fix tt h assume tt: "tt \<in> {0..<d}"
    from lie[of tt] tt have eq: "p tt Fc * p tt W = p tt M * (p tt W)\<^sup>2" by simp
    show "0 - h * (p tt M * (p tt W)\<^sup>2 - p tt Fc * p tt W) / 2500 = 0"
      using eq by (simp add: algebra_simps)
  qed
  have "p 0 Fc - p 0 M * p 0 W = p t Fc - p t M * p t W"
    by (rule mvt_real_eq[OF der d0 zerocond t])
  with init show "p t Fc = p t M * p t W" by simp
qed

lemmas mass_Fc_MW_invariant = mass_field_mass.Fc_MW_invariant
lemmas mass_clock_Fc_MW_invariant = mass_field_clock.Fc_MW_invariant

lemma mass_lie_from_inv:
  fixes p :: "real \<Rightarrow> state" and d :: real
  assumes inv: "\<forall>t\<in>{0..d}. p t Fc = p t M * p t W \<and> 0 < p t M"
  shows "\<And>u. u \<in> {0..<d} \<Longrightarrow> p u Fc * p u W = p u M * (p u W)\<^sup>2"
proof -
  fix u assume u: "u \<in> {0..<d}"
  then have ud: "u \<in> {0..d}" by auto
  from inv[rule_format, OF ud] obtain fc mpos where
    fc: "p u Fc = p u M * p u W" and mpos: "0 < p u M" by blast+
  from fc mpos have "p u W = p u Fc / p u M" by (simp add: field_simps)
  with fc mpos show "p u Fc * p u W = p u M * (p u W)\<^sup>2"
    by (simp add: algebra_simps power2_eq_square divide_simps)
qed


subsection \<open>Low observation simulation (mass field to normalized field)\<close>

definition lander_norm_clock_field :: "var \<Rightarrow> state \<Rightarrow> real" where
  "lander_norm_clock_field =
    ((\<lambda>_ _. 0)(V := (\<lambda>s. s W - 3.732),
                 W := (\<lambda>s. (s W)\<^sup>2 / 2500),
                 T := (\<lambda>_. 1)))"

lemma norm_clock_field_simps [simp]:
  "lander_norm_clock_field V s = s W - 3.732"
  "lander_norm_clock_field W s = (s W)\<^sup>2 / 2500"
  "lander_norm_clock_field T s = 1"
  "x \<noteq> V \<Longrightarrow> x \<noteq> W \<Longrightarrow> x \<noteq> T \<Longrightarrow> lander_norm_clock_field x s = 0"
  unfolding lander_norm_clock_field_def by simp_all

lemma norm_field_hide:
  "x \<noteq> M \<Longrightarrow> lander_norm_clock_field x (s(M := v)) = lander_norm_clock_field x s"
  by (cases "x = V"; cases "x = W"; cases "x = T") simp_all

definition mass_hide :: "(real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> state" where
  "mass_hide p t = (p t)(M := p 0 M)"

lemma mass_low_sim:
  fixes p :: "real \<Rightarrow> state" and d :: real
  assumes sol: "ODEsol (ODE lander_mass_clock_field) p d"
    and invm: "\<exists>e>0. \<forall>t\<in>{-e..d+e}. p t Fc = p t M * p t W \<and> 0 < p t M"
  shows "ODEsol (ODE lander_norm_clock_field) (mass_hide p) d"
    and "\<And>t x. x \<noteq> M \<Longrightarrow> mass_hide p t x = p t x"
proof -
  let ?q = "mass_hide p"
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  have qM: "\<And>t. ?q t M = p 0 M" unfolding mass_hide_def by simp
  have qoth: "\<And>t x. x \<noteq> M \<Longrightarrow> ?q t x = p t x"
    unfolding mass_hide_def by simp
  show qoth': "\<And>t x. x \<noteq> M \<Longrightarrow> ?q t x = p t x" by (rule qoth)
  have qMfun: "(\<lambda>t. ?q t M) = (\<lambda>_. p 0 M)" by (rule ext) (rule qM)
  from sol [unfolded ODEsol_def] obtain e1 where e1: "e1 > 0"
    and bigvec: "((\<lambda>t. state2vec (p t)) has_vderiv_on
      (\<lambda>t. ODE2Vec (ODE lander_mass_clock_field) (p t))) {-e1..d+e1}" by blast
  have bigderiv: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (p t))) {-e1..d+e1}"
    using has_vderiv_on_proj[OF bigvec] by (simp add: state2vec_def)
  from invm obtain e' where e'0: "e' > 0"
    and invbig: "\<forall>t\<in>{-e'..d+e'}. p t Fc = p t M * p t W \<and> 0 < p t M" by blast
  define e where "e = min (min e' e1) 1"
  have e0: "e > 0" using e'0 e1 unfolding e_def by simp
  have ele: "e \<le> e'" "e \<le> e1" "e \<le> 1" unfolding e_def by (auto simp: min_def)
  have inv: "\<forall>t\<in>{-e..d+e}. p t Fc = p t M * p t W \<and> 0 < p t M"
  proof (intro ballI)
    fix t assume t: "t \<in> {-e..d+e}"
    have "t \<in> {-e'..d+e'}" using t ele by auto
    with invbig show "p t Fc = p t M * p t W \<and> 0 < p t M" by blast
  qed
  have vderiv: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (p t))) {-e..d+e}"
  proof -
    fix x
    have sub: "{-e..d+e} \<subseteq> {-e1..d+e1}" using ele by auto
    from has_vderiv_on_subset[OF bigderiv[of x] sub] show
      "((\<lambda>t. p t x) has_vderiv_on
      (\<lambda>t. lander_mass_clock_field x (p t))) {-e..d+e}" .
  qed
  have qM0: "((\<lambda>t. ?q t M) has_vderiv_on (\<lambda>t. 0)) {-e..d+e}"
    unfolding qMfun by (simp add: has_vderiv_on_const)
  show "ODEsol (ODE lander_norm_clock_field) ?q d"
  proof (rule ODEsol_from_components)
    show "0 \<le> d" by (rule d0)
    show "0 < e" by (rule e0)
    fix x
    show "((\<lambda>t. ?q t x) has_vderiv_on (\<lambda>t. lander_norm_clock_field x (?q t))) {-e..d+e}"
    proof (cases "x = M")
      case True
      then show ?thesis
        using qM0 by (simp add: norm_clock_field_simps)
    next
      case False
      have fun_eq: "(\<lambda>t. ?q t x) = (\<lambda>t. p t x)" by (rule ext) (rule qoth, rule False)
      have base: "((\<lambda>t. p t x) has_vderiv_on
          (\<lambda>t. lander_mass_clock_field x (p t))) {-e..d+e}"
        by (rule vderiv[of x])
      have rate_eq: "\<And>t. t \<in> {-e..d+e} \<Longrightarrow>
          lander_mass_clock_field x (p t) = lander_norm_clock_field x (?q t)"
      proof -
        fix t assume t: "t \<in> {-e..d+e}"
        from inv[rule_format, OF t] have
          fc: "p t Fc = p t M * p t W" and mpos: "0 < p t M" by blast+
        show "lander_mass_clock_field x (p t) = lander_norm_clock_field x (?q t)"
        proof (cases "x = V")
          case True
          with fc mpos have "lander_mass_clock_field x (p t) = p t W - 3.732"
            by (simp add: divide_simps)
          with True False show ?thesis
            by (simp add: norm_field_hide mass_hide_def)
        next
          case xV: False
          show ?thesis
          proof (cases "x = W")
            case True
            with False xV show ?thesis
              by (simp add: norm_field_hide mass_hide_def power2_eq_square)
          next
            case xW: False
            show ?thesis
            proof (cases "x = T")
              case True
              with False xV xW show ?thesis by simp
            next
              case xT: False
              with False xV xW show ?thesis
                by (cases "x = Fc") (simp_all add: norm_field_hide mass_hide_def)
            qed
          qed
        qed
      qed
      have step1: "((\<lambda>t. p t x) has_vderiv_on
          (\<lambda>t. lander_norm_clock_field x (?q t))) {-e..d+e}"
        by (rule vderiv_on_cong_rates[OF base rate_eq])
      show ?thesis
        unfolding fun_eq by (rule step1)
    qed
  qed
qed

text \<open>The simulation preserves the low observation of a wait block:
the observer reads only the plant's (V,W) curve, and the mass is hidden.\<close>

lemma mass_low_obs_sim:
  fixes p :: "real \<Rightarrow> state" and d :: real
  shows "lander_obs_block (WaitBlk d (\<lambda>t. State (mass_hide p t)) ({}, {})) =
         lander_obs_block (WaitBlk d (\<lambda>t. State (p t)) ({}, {}))"
proof -
  have br: "\<And>q. restrict (lander_low_gstate \<circ> (\<lambda>\<tau>\<in>{0..d}. State (q \<tau>))) {0..d}
      = restrict (lander_low_gstate \<circ> (\<lambda>t. State (q t))) {0..d}"
    by (rule ext) (simp add: restrict_apply)
  have core: "restrict (lander_low_gstate \<circ> (\<lambda>t. State (mass_hide p t))) {0..d}
      = restrict (lander_low_gstate \<circ> (\<lambda>t. State (p t))) {0..d}"
    by (rule ext)
       (auto simp: restrict_apply mass_hide_def lander_low_gstate.simps)
  have "restrict (lander_low_gstate \<circ> (\<lambda>\<tau>\<in>{0..d}. State (mass_hide p \<tau>))) {0..d}
      = restrict (lander_low_gstate \<circ> (\<lambda>\<tau>\<in>{0..d}. State (p \<tau>))) {0..d}"
    by (simp only: br core)
  then show ?thesis by (simp add: WaitBlk_def)
qed

end
