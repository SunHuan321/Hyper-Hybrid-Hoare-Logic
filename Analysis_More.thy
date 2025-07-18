theory Analysis_More
  imports Ordinary_Differential_Equations.Flow
begin


subsection \<open>Some results about derivatives\<close>

text \<open>Projection of has_vector_derivative onto components.\<close>
lemma has_vector_derivative_proj:
  assumes "(p has_vector_derivative q t) (at t within D)"
  shows "((\<lambda>t. p t $ i) has_vector_derivative q t $ i) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def 
  apply (simp add: bounded_linear_scaleR_left)
  using tendsto_vec_nth by fastforce

lemma has_vderiv_on_proj:
  assumes "(p has_vderiv_on q) D"
  shows "((\<lambda>t. p t $ i) has_vderiv_on (\<lambda>t. q t $ i)) D"
  using assms unfolding has_vderiv_on_def 
  by (simp add: has_vector_derivative_proj)

lemma has_vector_derivative_projI:
  assumes "\<forall>i. ((\<lambda>t. p t $ i) has_vector_derivative q $ i) (at t within D)"
  shows "(p has_vector_derivative q) (at t within D)"
  using assms unfolding has_vector_derivative_def has_derivative_def
  apply (auto simp add: bounded_linear_scaleR_left)
  by (auto intro: vec_tendstoI)

lemma has_vdriv_on_projI:
  assumes "\<forall>i. ((\<lambda>t. p t $ i) has_vderiv_on (\<lambda>t. q t $ i)) D"
  shows "(p has_vderiv_on q) D"
  using assms has_vderiv_on_def has_vector_derivative_projI by metis

lemma has_derivative_coords [simp,derivative_intros]:
  "((\<lambda>t. t$i) has_derivative (\<lambda>t. t$i)) (at x)"
  unfolding has_derivative_def by auto

lemma has_vector_derivative_divide[derivative_intros]:
  fixes a:: "'a::real_normed_field"
  shows "(f has_vector_derivative x) F \<Longrightarrow> ((\<lambda>x. f x / a) has_vector_derivative (x/a)) F"
  unfolding divide_inverse by(fact has_vector_derivative_mult_left)

lemma has_derivative_divide[derivative_intros]:
  fixes a:: "'a::real_normed_field"
  shows "(f has_derivative g) F \<Longrightarrow> ((\<lambda>x. f x / a) has_derivative (\<lambda>x. g x / a)) F"
  unfolding divide_inverse by(fact has_derivative_mult_left)


text \<open>If the derivative is always 0, then the function is always 0.\<close>
lemma mvt_real_eq:
  fixes p :: "real \<Rightarrow> real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. \<forall>s. q t s = 0"
    and "x \<in> {0 .. d}"
  shows "p 0 = p x" 
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_subset less_eq_real_def order_less_le_trans)
    then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by force
qed

text \<open>If the derivative is always non-negative, then the function is increasing.\<close>
lemma mvt_real_ge:
  fixes p :: "real \<Rightarrow>real"
 assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
  and "d \<ge> 0"
  and "\<forall>t\<in>{0 ..<d}. \<forall>s\<ge>0. q t s \<ge> 0"
  and "x \<in> {0 .. d}"
  shows "p 0 \<le> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_subset in_mono order_refl)
  then show ?thesis
  using assms
  using mvt_simple[of 0 x p q]
  by (smt atLeastAtMost_iff atLeastLessThan_iff greaterThanLessThan_iff)
qed

text \<open>If the derivative is always non-positive, then the function is decreasing.\<close>
lemma mvt_real_le:
  fixes p :: "real \<Rightarrow>real"
  assumes "\<forall>t\<in>{0 .. d}. (p has_derivative q t) (at t within {0 .. d}) "
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. \<forall>s\<ge>0 . q t s \<le> 0"
    and "x \<in> {0 .. d}"
  shows "p 0 \<ge> p x"
proof -
  have "\<forall>t\<in>{0 .. x}. (p has_derivative q t) (at t within {0 .. x})"
    using assms 
    by (meson atLeastAtMost_iff atLeastatMost_subset_iff has_derivative_subset in_mono order_refl)
  then obtain xa where "xa\<in>{0<..<x}" " p x - p 0 = q xa (x - 0)" if "x>0"
    using  mvt_simple[of 0 x p q] 
    using atLeastAtMost_iff by blast
  then have "p x \<le> p 0" if "x > 0"
    using assms(2-4)
    by (metis atLeastAtMost_iff atLeastLessThan_iff diff_0_right greaterThanLessThan_iff
              le_iff_diff_le_0 less_eq_real_def order.strict_trans2)
  then show ?thesis
    using assms by fastforce
qed


lemma real_inv_le:
  fixes p :: "real \<Rightarrow> real" and con :: real
  assumes "\<forall>t\<in>{-e..d+e}. (p has_derivative q t) (at t within {-e..d+e})"
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. (p t = con \<longrightarrow> q t 1 < 0)"
    and "p 0 \<le> con "
    and "x \<in> {0 .. d}"
    and "e > 0"
  shows "p x \<le> con" 
proof (rule ccontr) 
  assume a:" \<not> p x \<le> con"
  have 1:"p x > con"
    using a by auto
  have 2:"\<forall>t\<in>{0 .. d}. continuous (at t within {-e<..<d+e}) p"
    using assms has_derivative_subset
    using has_derivative_continuous 
    by (smt atLeastAtMost_iff continuous_within_subset greaterThanLessThan_subseteq_atLeastAtMost_iff greaterThan_iff)
  have 3:"\<forall>t\<in>{0 .. d}. isCont p t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<d+e}" p]
      using 2 assms(5) assms(6) by auto
    done
  have 4:"{y. p y = con \<and> y \<in> {0 .. x}} \<noteq> {}"
    using IVT[of p 0 con x] using 3 1 assms 
    by auto
  have 5: "{y. p y = con \<and> y \<in> {0 .. x}} = ({0 .. x} \<inter> p -` {con})"
    by auto
  have 6: "closed ({0 .. x} \<inter> p -` {con})"
    using 3 assms(5) apply simp
    apply (rule continuous_closed_preimage)
      apply auto
    by (simp add: continuous_at_imp_continuous_on)
  have 7: "compact {0 .. x}"
    using assms
    by blast
  have 8: "compact {y. p y = con \<and> y \<in> {0 .. x}}"
    apply auto
    using 4 5 6 7 
    by (smt Collect_cong Int_left_absorb atLeastAtMost_iff compact_Int_closed)
  obtain t where t1:"t \<in> {y. p y = con \<and> y \<in> {0 .. x}}" and t2:"\<forall> tt\<in> {y. p y = con \<and> y \<in> {0 .. x}}. tt \<le>t"
    using compact_attains_sup[of "{y. p y = con \<and> y \<in> {0 .. x}}"] 4 8 
    by blast
  have 9:"t<x"
    using t1 1 
    using leI by fastforce
  have 10:"p tt > con" if "tt\<in>{t<..x}" for tt
  proof(rule ccontr)
    assume "\<not> con < p tt"
    then have not:"p tt \<le>con" by auto
    have "\<exists> t' \<in> {t<..x}. p t' = con"
    proof(cases "p tt = con")
      case True
      then show ?thesis using that by auto
    next
      case False
      then have "p tt < con"
        using not by auto
      then have "{y. p y = con \<and> y \<in> {tt .. x}} \<noteq> {}"
        using IVT[of p tt con x] using 3 1 assms that t1 
        by auto
      then show ?thesis using that by auto
    qed
    then show False using t1 t2 9 
      using atLeastAtMost_iff greaterThanAtMost_iff by auto
  qed     
  have 11:"(p has_derivative q t) (at t within {-e..d+e})"
    using assms t1 by auto
  then have 12:"\<forall>s . q t s = q t 1 * s"
    using has_derivative_bounded_linear[of p "q t" "(at t within {-e..d+e})"]
    using real_bounded_linear by auto
  have 13:"(p has_real_derivative q t 1) (at t within {-e..d+e})"
    using 11 12 
    by (metis has_derivative_imp_has_field_derivative mult.commute)
  have 14:"q t 1 < 0" using t1 assms 9 by auto
  have 15:"\<exists>dd>0. \<forall>h>0. t + h \<in> {-e..d+e} \<longrightarrow> h < dd \<longrightarrow> p (t + h) < p t"
    using has_real_derivative_neg_dec_right[of p "q t 1" t "{-e..d+e}"] 13 14 
    by auto
  then obtain dd where d1:"\<forall>h>0. t + h \<in> {-e..d+e} \<longrightarrow> h < dd \<longrightarrow> p (t + h) < p t" and d2:"dd>0" by auto
  then have 16:"min (dd/2) (x-t)/2 < dd" and "min (dd/2) (x-t)/2 > 0"
    using 9 by auto
  then have 17:"(t + min (dd/2) (x-t)/2)> t" "(t + min (dd/2) (x-t)/2) < x" 
    apply auto
    using d2 9
     by (smt field_sum_of_halves)
   then have 18:"p (t + min (dd/2) (x-t)/2) < p t"
    using d1 t1 16 assms(5) assms(6) by auto
  have 19:"p (t + min (dd/2) (x-t)/2)>con" using 10 17 by auto
  show False using 18 19 t1
    by auto 
  qed


lemma real_inv_ge:
  fixes p :: "real \<Rightarrow> real" and con :: real
  assumes "\<forall>t\<in>{-e..d+e}. (p has_derivative q t) (at t within {-e..d+e})"
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. (p t = con \<longrightarrow> q t 1 > 0)"
    and "p 0 \<ge> con "
    and "x \<in> {0 .. d}"
    and "e > 0"
  shows "p x \<ge> con" 
proof (rule ccontr) 
  assume a:" \<not> p x \<ge> con"
  have 1:"p x < con"
    using a by auto
  have " \<forall>t\<in>{- e..d + e}. (p has_derivative q t) (at t within {- e<..<d + e})"
    using assms has_derivative_subset
    by (smt greaterThanLessThan_subseteq_atLeastAtMost_iff)
  then have " \<forall>t\<in>{0..d}. (p has_derivative q t) (at t within {- e<..<d + e})"
    using assms by auto
  then have 2:"\<forall>t\<in>{0 .. d}. continuous (at t within {-e<..<d+e}) p"
    using has_derivative_continuous 
    by blast
  have 3:"\<forall>t\<in>{0 .. d}. isCont p t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<d+e}" p]
      using 2 assms(5) assms(6) by auto
    done
  have 4:"{y. p y = con \<and> y \<in> {0 .. x}} \<noteq> {}"
    using IVT2[of p x con 0] using 3 1 assms 
    by auto
  have 5: "{y. p y = con \<and> y \<in> {0 .. x}} = ({0 .. x} \<inter> p -` {con})"
    by auto
  have 6: "closed ({0 .. x} \<inter> p -` {con})"
    using 3 assms(5) apply simp
    apply (rule continuous_closed_preimage)
      apply auto
    by (simp add: continuous_at_imp_continuous_on)
  have 7: "compact {0 .. x}"
    using assms
    by blast
  have 8: "compact {y. p y = con \<and> y \<in> {0 .. x}}"
    apply auto
    using 4 5 6 7 
    by (smt Collect_cong Int_left_absorb atLeastAtMost_iff compact_Int_closed)
  obtain t where t1:"t \<in> {y. p y = con \<and> y \<in> {0 .. x}}" and t2:"\<forall> tt\<in> {y. p y = con \<and> y \<in> {0 .. x}}. tt \<le>t"
    using compact_attains_sup[of "{y. p y = con \<and> y \<in> {0 .. x}}"] 4 8 
    by blast
  have 9:"t<x"
    using t1 1 
    using leI by fastforce
  have 10:"p tt < con" if "tt\<in>{t<..x}" for tt
  proof(rule ccontr)
    assume "\<not> con > p tt"
    then have not:"p tt \<ge> con" by auto
    have "\<exists> t' \<in> {t<..x}. p t' = con"
    proof(cases "p tt = con")
      case True
      then show ?thesis using that by auto
    next
      case False
      then have "p tt > con"
        using not by auto
      then have "{y. p y = con \<and> y \<in> {tt .. x}} \<noteq> {}"
        using IVT2[of p x con tt] using 3 1 assms that t1 
        by auto
      then show ?thesis using that by auto
    qed
    then show False using t1 t2 9 
      using atLeastAtMost_iff greaterThanAtMost_iff by auto
  qed     
  have 11:"(p has_derivative q t) (at t within {-e..d+e})"
    using assms t1 by auto
  then have 12:"\<forall>s . q t s = q t 1 * s"
    using has_derivative_bounded_linear[of p "q t" "(at t within {-e..d+e})"]
    using real_bounded_linear by auto
  have 13:"(p has_real_derivative q t 1) (at t within {-e..d+e})"
    using 11 12 
    by (metis has_derivative_imp_has_field_derivative mult.commute)
  have 14:"q t 1 > 0" using t1 assms 9 by auto
  have 15:"\<exists>dd>0. \<forall>h>0. t + h \<in> {-e..d+e} \<longrightarrow> h < dd \<longrightarrow> p (t + h) > p t"
    using has_real_derivative_pos_inc_right[of p "q t 1" t "{-e..d+e}"] 13 14 
    by auto
  then obtain dd where d1:"\<forall>h>0. t + h \<in> {-e..d+e} \<longrightarrow> h < dd \<longrightarrow> p (t + h) > p t" and d2:"dd>0" by auto
  then have 16:"min (dd/2) (x-t)/2 < dd" and "min (dd/2) (x-t)/2 > 0"
    using 9 by auto
  then have 17:"(t + min (dd/2) (x-t)/2)> t" "(t + min (dd/2) (x-t)/2) < x" 
    apply auto
    using d2 9
     by (smt field_sum_of_halves)
   then have 18:"p (t + min (dd/2) (x-t)/2) > p t"
    using d1 t1 16 assms(5) assms(6) by auto
  have 19:"p (t + min (dd/2) (x-t)/2)< con" using 10 17 by auto
  show False using 18 19 t1
    by auto 
qed

lemma real_inv_l:
  fixes p :: "real \<Rightarrow> real" and con :: real
  assumes "\<forall>t\<in>{-e..d+e}. (p has_derivative q t) (at t within {-e..d+e})"
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. (p t \<le> con \<longrightarrow> q t 1 < 0)"
    and "p 0 < con "
    and "x \<in> {0 .. d}"
    and "e > 0"
  shows "p x < con"
proof (rule ccontr) 
  assume a:" \<not> p x < con"
  have 1:"p x \<ge> con"
    using a by auto
  have 2:"\<forall>t\<in>{0 .. d}. continuous (at t within {-e<..<d+e}) p"
    using assms has_derivative_subset
    using has_derivative_continuous 
    by (smt atLeastAtMost_iff continuous_within_subset greaterThanLessThan_subseteq_atLeastAtMost_iff greaterThan_iff)
  have 3:"\<forall>t\<in>{0 .. d}. isCont p t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<d+e}" p]
      using 2 assms(5) assms(6) by auto
    done
  have 4:"{y. p y = con \<and> y \<in> {0 .. x}} \<noteq> {}"
    using IVT[of p 0 con x] using 3 1 assms 
    by auto
  have 5: "{y. p y = con \<and> y \<in> {0 .. x}} = ({0 .. x} \<inter> p -` {con})"
    by auto
  have 6: "closed ({0 .. x} \<inter> p -` {con})"
    using 3 assms(5) apply simp
    apply (rule continuous_closed_preimage)
      apply auto
    by (simp add: continuous_at_imp_continuous_on)
  have 7: "compact {0 .. x}"
    using assms
    by blast
  have 8: "compact {y. p y = con \<and> y \<in> {0 .. x}}"
    apply auto
    using 4 5 6 7 
    by (smt Collect_cong Int_left_absorb atLeastAtMost_iff compact_Int_closed)
  obtain t where t1:"t \<in> {y. p y = con \<and> y \<in> {0 .. x}}" and t2:"\<forall> tt\<in> {y. p y = con \<and> y \<in> {0 .. x}}. tt \<ge> t"
    using compact_attains_inf[of "{y. p y = con \<and> y \<in> {0 .. x}}"] 4 8 
    by blast
  have 9:"t > 0"
    using t1 1 assms(4) 
    using less_eq_real_def by auto
  have 10:"p tt < con" if "tt\<in>{0..<t}" for tt
  proof(rule ccontr)
    assume "\<not> p tt < con"
    then have not:"p tt \<ge> con" by auto
    have "\<exists> t' \<in> {0..<t}. p t' = con"
    proof(cases "p tt = con")
      case True
      then show ?thesis using that by auto
    next
      case False
      then have "p tt > con"
        using not by auto
      then have "{y. p y = con \<and> y \<in> {0 .. tt}} \<noteq> {}"
        using IVT[of p 0 con tt] using 3 1 assms that t1 
        by auto
      then show ?thesis using that by auto
    qed
    then show False using t1 t2 9 
      using atLeastAtMost_iff greaterThanAtMost_iff by auto
  qed     
  have 11:"(p has_derivative q y) (at y within {0..t})" if "y \<in> {0 ..t}"for y
    apply(rule has_derivative_subset [where s = "{-e<..<d+e}"])
    using assms that t1
    apply auto 
    by (smt atLeastAtMost_iff at_within_Icc_at has_derivative_at_withinI)
  have 12:"\<exists> tt \<in> {0<..<t} . p t - p 0 = q tt t "
    using mvt_simple[of 0 t p q] 9 11
    by auto
  obtain tt where tt1:"p t - p 0 = q tt t" and tt2:"tt \<in> {0<..<t}"
    using 12 by auto
  have 13:"\<forall>s . q tt s = q tt 1 * s"
    using has_derivative_bounded_linear[of p "q tt" "(at tt within {0..t})"]
    using real_bounded_linear 11 tt2 by auto
  have 14:"p t - p 0 = q tt 1 * t" using tt1 13 
    by metis
  have 15:"q tt 1 > 0" using 14 assms(4) t1 9 
    by (metis (mono_tags, lifting) diff_gt_0_iff_gt mem_Collect_eq zero_less_mult_pos2)
  then show False using assms(3) 10[of tt] tt2 
    by (smt "10" a assms(5) atLeastAtMost_iff atLeastLessThan_iff greaterThanLessThan_iff)
qed


lemma real_inv_g:
  fixes p :: "real \<Rightarrow> real" and con :: real
  assumes "\<forall>t\<in>{-e..d+e}. (p has_derivative q t) (at t within {-e..d+e})"
    and "d \<ge> 0"
    and "\<forall>t\<in>{0 ..<d}. (p t \<ge> con \<longrightarrow> q t 1 \<ge> 0)"
    and "p 0 > con "
    and "x \<in> {0 .. d}"
    and "e > 0"
  shows "p x > con" 
proof (rule ccontr) 
  assume a:" \<not> p x > con"
  have 1:"p x \<le> con"
    using a by auto
  have 2:"\<forall>t\<in>{0 .. d}. continuous (at t within {-e<..<d+e}) p"
    using assms has_derivative_subset
    using has_derivative_continuous 
    by (smt atLeastAtMost_iff continuous_within_subset greaterThanLessThan_subseteq_atLeastAtMost_iff greaterThan_iff)
  have 3:"\<forall>t\<in>{0 .. d}. isCont p t"
    apply auto subgoal for t
      using continuous_within_open[of t "{-e<..<d+e}" p]
      using 2 assms(5) assms(6) by auto
    done
  have 4:"{y. p y = con \<and> y \<in> {0 .. x}} \<noteq> {}"
    using IVT2[of p x con 0] using 3 1 assms 
    by auto
  have 5: "{y. p y = con \<and> y \<in> {0 .. x}} = ({0 .. x} \<inter> p -` {con})"
    by auto
  have 6: "closed ({0 .. x} \<inter> p -` {con})"
    using 3 assms(5) apply simp
    apply (rule continuous_closed_preimage)
      apply auto
    by (simp add: continuous_at_imp_continuous_on)
  have 7: "compact {0 .. x}"
    using assms
    by blast
  have 8: "compact {y. p y = con \<and> y \<in> {0 .. x}}"
    apply auto
    using 4 5 6 7 
    by (smt Collect_cong Int_left_absorb atLeastAtMost_iff compact_Int_closed)
  obtain t where t1:"t \<in> {y. p y = con \<and> y \<in> {0 .. x}}" and t2:"\<forall> tt\<in> {y. p y = con \<and> y \<in> {0 .. x}}. tt \<ge> t"
    using compact_attains_inf[of "{y. p y = con \<and> y \<in> {0 .. x}}"] 4 8 
    by blast
  have 9:"t > 0"
    using t1 1 assms(4) 
    using less_eq_real_def by auto
  have 10:"p tt > con" if "tt\<in>{0..<t}" for tt
  proof(rule ccontr)
    assume "\<not> p tt > con"
    then have not:"p tt \<le> con" by auto
    have "\<exists> t' \<in> {0..<t}. p t' = con"
    proof(cases "p tt = con")
      case True
      then show ?thesis using that by auto
    next
      case False
      then have "p tt < con"
        using not by auto
      then have "{y. p y = con \<and> y \<in> {0 .. tt}} \<noteq> {}"
        using IVT2[of p tt con 0] using 3 1 assms that t1 
        by auto
      then show ?thesis using that by auto
    qed
    then show False using t1 t2 9 
      using atLeastAtMost_iff greaterThanAtMost_iff by auto
  qed     
  have 11:"(p has_derivative q y) (at y within {0..t})" if "y \<in> {0 ..t}"for y
    apply(rule has_derivative_subset [where s = "{-e<..<d+e}"])
    using assms that t1
    apply auto 
    by (smt atLeastAtMost_iff at_within_Icc_at has_derivative_at_withinI)
  have 12:"\<exists> tt \<in> {0<..<t} . p t - p 0 = q tt t "
    using mvt_simple[of 0 t p q] 9 11
    by auto
  obtain tt where tt1:"p t - p 0 = q tt t" and tt2:"tt \<in> {0<..<t}"
    using 12 by auto
  have 13:"\<forall>s . q tt s = q tt 1 * s"
    using has_derivative_bounded_linear[of p "q tt" "(at tt within {0..t})"]
    using real_bounded_linear 11 tt2 by auto
  have 14:"p t - p 0 = q tt 1 * t" using tt1 13 
    by metis
  have 15:"q tt 1 < 0" using 14 assms(4) t1 9 
    by (metis (mono_tags, lifting) less_iff_diff_less_0 mem_Collect_eq mult_less_0_iff not_less_iff_gr_or_eq)
  then show False using assms(3) 10[of tt] tt2 
    by (smt "1" "10" assms(5) atLeastAtMost_iff atLeastLessThan_iff greaterThanLessThan_iff) 
qed


subsection \<open>Definition of states\<close>

text \<open>Variable names\<close>
type_synonym var = char

text \<open>State\<close>
type_synonym state = "var \<Rightarrow> real"
text \<open>Expressions\<close>
type_synonym exp = "state \<Rightarrow> real"

text \<open>Predicates\<close>
type_synonym fform = "state \<Rightarrow> bool"

text \<open>States as a vector\<close>
type_synonym vec = "real^(var)"

text \<open>Conversion between state and vector\<close>
definition state2vec :: "state \<Rightarrow> vec" where
  "state2vec s = (\<chi> x. s x)"

definition vec2state :: "vec \<Rightarrow> state" where
  "(vec2state v) x = v $ x"

lemma vec_state_map1[simp]: "vec2state (state2vec s) = s"
  unfolding vec2state_def state2vec_def by auto

lemma vec_state_map2[simp]: "state2vec (vec2state s) = s"
  unfolding vec2state_def state2vec_def by auto

text \<open>Conversion between state pair and vector\<close>
definition state2vec_Pair :: "(state \<times> state) \<Rightarrow> (real^var) \<times> (real^var)"
  where "state2vec_Pair ss = (state2vec (fst ss), state2vec (snd ss))"

definition vec2state_Pair :: "(real^var) \<times> (real^var) \<Rightarrow> (state \<times> state)"
  where "vec2state_Pair vv = (vec2state (fst vv), vec2state (snd vv))"

lemma vec_state_map1_Pair[simp]: "vec2state_Pair (state2vec_Pair s) = s"
  unfolding vec2state_Pair_def state2vec_Pair_def by auto

lemma vec_state_map2_Pair[simp]: "state2vec_Pair (vec2state_Pair s) = s"
  unfolding vec2state_Pair_def state2vec_Pair_def by auto

text \<open>Conversion between k-states and vector\<close>

definition state2vec_k :: "(('k :: finite) \<Rightarrow> state) \<Rightarrow> real^('k \<times> var)"
  where "state2vec_k ss = (\<chi> x. ss (fst x) (snd x))"

definition vec2state_k :: "real^(('k :: finite) \<times> char) \<Rightarrow>('k \<Rightarrow> state) "
  where "(vec2state_k V) k v = V $ (k, v)"

lemma vec_state_map1_k[simp]: "vec2state_k (state2vec_k s) = s"
  unfolding vec2state_k_def state2vec_k_def by auto

lemma vec_state_map2_k[simp]: "state2vec_k (vec2state_k s) = s"
  unfolding vec2state_k_def state2vec_k_def by auto

(*
lemma "(\<lambda>t. state2vec_k (ps k t) $ (a, b)) = (\<lambda>t. ps k t a b)"
*)

subsection \<open>Definition of ODEs\<close>
datatype ODE =
  ODE "var \<Rightarrow> exp"

text \<open>Given ODE and a state, find the derivative vector.\<close>
fun ODE2Vec :: "ODE \<Rightarrow> state \<Rightarrow> vec" where
  "ODE2Vec (ODE f) s = state2vec (\<lambda>a. f a s)"

text \<open>Given the same ODE and two state, find the derivative vector pair.\<close>
fun ODE2Vec_Pair :: "ODE \<Rightarrow> (state \<times> state) \<Rightarrow> (real^var) \<times> (real^var)" where
  "ODE2Vec_Pair ode ss = (ODE2Vec ode (fst ss), ODE2Vec ode (snd ss))"

text \<open>Given the same ODE and k-state, find the derivative vector pair.\<close>
fun ODE2Vec_k :: "ODE \<Rightarrow> (('k :: finite) \<Rightarrow> state) \<Rightarrow> (real^('k \<times> var))" where
  "ODE2Vec_k (ODE f) ss = state2vec_k (\<lambda>k. \<lambda>x. f x (ss k))"


text \<open>History p on time {0 .. d} is a solution to ode.\<close>
definition ODEsol :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> real \<Rightarrow> bool" where
  "ODEsol ode p d = (d \<ge> 0 \<and> (\<exists>\<epsilon>>0. ((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-\<epsilon> .. d+\<epsilon>}))"

lemma finite_arg_min:
  fixes ds :: "'k::finite \<Rightarrow> real"
  shows "\<exists>k. \<forall>k'. ds k \<le> ds k'"
proof -
  let ?S = "range ds"
  have "finite ?S" by simp
  then have "?S \<noteq> {}" by auto
  then have "Min ?S \<in> ?S"
    using \<open>finite ?S\<close> by simp
  then obtain k where "ds k = Min ?S"
    by force
  then show ?thesis
    by (metis Min_le \<open>finite (range ds)\<close> rangeI)
qed

lemma ODEsol_k:
  fixes ps :: "('k :: finite) \<Rightarrow> real \<Rightarrow> state"
  assumes "\<forall>k. ODEsol ode (ps k) d"
  shows "\<exists>e > 0. (\<forall>k. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) {-e .. d+e})"
proof-
  from assms have "\<forall>k. \<exists>e > 0. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) {-e .. d+e}"
    using ODEsol_def by blast
  then obtain es where 1: "(\<forall>k. es k > 0 \<and> ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) {-es k .. d+es k})"
    by metis
  obtain k' where 2: "\<forall>k. es k' \<le> es k"
    using finite_arg_min[of es] by blast
  let ?e = "es k'"
  have "\<forall>k. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) {-?e .. d+?e}"
    by (metis "1" "2" add_le_cancel_left atLeastatMost_subset_iff has_vderiv_on_subset le_imp_neg_le)
  with 1 show ?thesis
    by blast
qed


lemma ODEsol_le: "\<lbrakk>ODEsol ode p d; t \<le> d; t \<ge> 0\<rbrakk> \<Longrightarrow> ODEsol ode p t"
  apply (simp add: ODEsol_def)
  by (meson add_le_cancel_right atLeastatMost_subset_iff dual_order.refl has_vderiv_on_subset)

text \<open>History p on time {0 ..} is a solution to ode.\<close>
definition ODEsolInf :: "ODE \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> bool" where
  "ODEsolInf ode p = (\<exists>\<epsilon>>0. ((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-\<epsilon> ..})"

subsection \<open>More theorems about derivatives\<close>

lemma has_vderiv_on_Pair:
  assumes "(f has_vderiv_on f') S"
      and "(g has_vderiv_on g') S"
    shows "((\<lambda>x. (f x, g x)) has_vderiv_on (\<lambda>x. (f' x, g' x))) S"
  using assms
  by (auto simp: has_vderiv_on_def intro!: derivative_eq_intros)

lemma derivative_exp [simp, derivative_intros]:
  "(exp has_derivative (*) (exp (x :: real))) (at x)"
  using DERIV_exp unfolding has_field_derivative_def
  by auto

lemma derivative_exp_const [derivative_intros]:
  fixes c :: real
  shows "((\<lambda>x. exp (c * x)) has_derivative (\<lambda>xa. xa * c * exp (c * x))) (at x)"
proof-
  have 1: "((*) c has_derivative (\<lambda>x. x * c)) (at x)"
    apply (rule has_derivative_eq_rhs)
     apply (auto intro!: derivative_intros)[1]
    by auto
  show ?thesis using has_derivative_exp[OF 1] 
    by auto
  qed

lemma SOME_const_vderiv [derivative_intros, simp]:
  fixes p :: " real \<Rightarrow> bool"
  assumes "(f has_vderiv_on f') S"
  shows "((\<lambda>t. (SOME k. p k) * f t) has_vderiv_on (\<lambda>t. (SOME k . p k) * f' t)) S"
  apply (rule has_vderiv_on_eq_rhs)
   apply (rule has_vderiv_on_mult)
    apply (auto intro: derivative_intros)[1]
  using assms apply auto
  done

subsection \<open>Further results in analysis\<close>

lemma ODEsol_old:
  assumes "ODEsol ode p d"
  shows "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 .. d}"
proof-
  obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-e .. d+e}"
    using assms(1) unfolding ODEsol_def by blast
  then show ?thesis 
    using e(1) has_vderiv_on_subset[OF e(2)] by auto
qed

lemma ODEsol_old_Pair:
  assumes "ODEsol ode p1 d"
      and "ODEsol ode p2 d"
  shows "((\<lambda>t. state2vec_Pair (p1 t, p2 t)) has_vderiv_on (\<lambda>t. ODE2Vec_Pair ode (p1 t, p2 t))) {0 .. d}"
proof-
  from assms have "((\<lambda>t. state2vec (p1 t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p1 t))) {0 .. d}"  
                  "((\<lambda>t. state2vec (p2 t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p2 t))) {0 .. d}"
    using ODEsol_old[of ode p1 d] ODEsol_old[of ode p2 d] by auto
  then show ?thesis
    unfolding state2vec_Pair_def
    using has_vderiv_on_Pair[of "\<lambda>t. state2vec (p1 t)" "\<lambda>t. ODE2Vec ode (p1 t)" "{0 .. d}"
    "\<lambda>t. state2vec (p2 t)" "\<lambda>t. ODE2Vec ode (p2 t)"]
    by auto
qed

lemma ODEsol_old_k':
  assumes "\<forall>k. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) D"
  shows "((\<lambda>t. state2vec_k (\<lambda>k. ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec_k ode (\<lambda>k. ps k t))) D"
proof-
   obtain f where "ode = ODE f" 
    by (meson ODE2Vec.elims)
  from assms have "\<forall>k. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (ps k t))) D"
    using ODEsol_old by blast
  then have "\<forall>k i. ((\<lambda>x. ps k x i) has_vderiv_on (\<lambda>x. f i (ps k x))) D"
    using ODE2Vec.simps \<open>ode = ODE f\<close> has_vderiv_on_proj state2vec_def by fastforce
  then show ?thesis
    using has_vdriv_on_projI[of "\<lambda>t. state2vec_k (\<lambda>k. ps k t)" "\<lambda>t. ODE2Vec_k ode (\<lambda>k. ps k t)" "D"]
    \<open>ode = ODE f\<close> state2vec_k_def 
    by (smt (z3) ODE2Vec_k.simps has_vderiv_on_def has_vector_derivative_transform vec_lambda_beta)
qed

lemma ODEsol_old_k:
  assumes "\<forall>k. ODEsol ode (ps k) d"
  shows "((\<lambda>t. state2vec_k (\<lambda>k. ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec_k ode (\<lambda>k. ps k t))) {0 .. d}"
  using ODEsol_old_k'[of ps ode "{0 .. d}"] assms ODEsol_old
  by blast

lemma ODEsolInf_old:
   assumes "ODEsolInf ode p"
   shows "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {0 ..}"
proof-
  obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-e ..}"
    using assms(1) unfolding ODEsolInf_def by blast
  then show ?thesis 
    using e(1) has_vderiv_on_subset[OF e(2)] by auto
qed

lemma ODEsol_merge:
  assumes "ODEsol ode p d"
    and "ODEsol ode p2 d2"
    and "p2 0 = p d"
  shows "ODEsol ode (\<lambda>\<tau>. if \<tau> < d then p \<tau> else p2 (\<tau> - d)) (d + d2)"
  unfolding ODEsol_def
  apply auto
  subgoal 
    using assms(1,2) unfolding ODEsol_def by auto
  subgoal
  proof-
    have step1:"d\<ge>0 \<and> d2\<ge>0"
      using assms unfolding ODEsol_def by auto
    then have step2:"{0 .. d+d2} = {0 .. d}\<union>{d .. d+d2}"
      by auto
    have step3:"({0..d} \<union> closure {d..d + d2} \<inter> closure {0..d}) = {0..d}"
      using step1 by auto
    have step4:"({d..d + d2} \<union> closure {d..d + d2} \<inter> closure {0..d}) = {d..d+d2}"
      using step1 by auto
    obtain e1 where e1: "e1 > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-e1 .. d+e1}"
      using assms(1) unfolding ODEsol_def by blast
    obtain e2 where e2: "e2 > 0" "((\<lambda>t. state2vec (p2 t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p2 t))) {-e2 .. d2+e2}"
      using assms(2) unfolding ODEsol_def by blast
    obtain e where e: "e > 0" "e < e1" "e < e2"
      using e1(1) e2(1) field_lbound_gt_zero by auto
    then have stepe:"{0 .. d2+e}\<subseteq>{- e2..d2 + e2}" "{-e .. d}\<subseteq>{- e1..d + e1}" "{- e..d + d2 + e} = {- e..d} \<union> {d..d + d2 + e}"
      using step1  by auto
    have stepclo1:"({- e..d} \<union> closure {d..d + d2 + e} \<inter> closure {- e..d}) = {- e..d}"
      using e step1 by auto 
    have stepclo2:" ({d..d + d2 + e} \<union> closure {d..d + d2 + e} \<inter> closure {- e..d}) = {d..d + d2 + e}"
      using e step1 by auto
    have stepclo3: "x \<in> closure {d..d + d2 + e} \<Longrightarrow>
          x \<in> closure {- e..d} \<Longrightarrow> x = d" for x
      using e step1  by auto
    have step5: "((\<lambda>t. t - d) has_vderiv_on (\<lambda>t. 1)) {d .. d+d2+e}"
      by (auto intro!: derivative_intros)
    then have step6: "((\<lambda>t. state2vec (p2 (t-d))) has_vderiv_on (\<lambda>t. ODE2Vec ode (p2 (t-d)))) {d .. d+d2+e}"
      using has_vderiv_on_compose2[of "(\<lambda>t. state2vec (p2 t))" "(\<lambda>t. ODE2Vec ode (p2 (t)))" "{0 .. d2+e}" "(\<lambda>t. (t-d))" "(\<lambda>t. 1)" "{d .. d+d2+e}"]
      using e2 e unfolding ODEsol_def
      using has_vderiv_on_subset[OF e2(2) stepe(1)] by auto
     have step7:" ((\<lambda>t. if t \<in> {-e..d} then state2vec (p t) else state2vec (p2 (t - d))) has_vderiv_on
     (\<lambda>t. if t \<in> {-e..d} then ODE2Vec ode (p t) else ODE2Vec ode (p2 (t - d)))){-e..d + d2+e}"
      using has_vderiv_on_If[of "{-e .. d+d2+e}" "{-e .. d}" "{d .. d+d2+e}" "(\<lambda>t. state2vec (p t))" "(\<lambda>t. ODE2Vec ode (p t))" "(\<lambda>t. state2vec (p2 (t-d)))" "(\<lambda>t. ODE2Vec ode (p2 (t-d)))"]
      using step1 step2 step3 step4 step6 stepclo1 stepclo2 stepclo3
      using has_vderiv_on_subset[OF e1(2) stepe(2)] e stepe assms(3)
      by auto
    show ?thesis
      apply(rule exI[where x=e])
      using has_vderiv_eq[of "(\<lambda>t. if t \<in> {-e..d} then state2vec (p t) else state2vec (p2 (t - d)))" "(\<lambda>t. if t \<in> {-e..d} then ODE2Vec ode (p t) else ODE2Vec ode (p2 (t - d)))" "{-e..d + d2+e}" "(\<lambda>t. state2vec (if t < d then p t else p2 (t - d)))" "(\<lambda>t. ODE2Vec ode (if t < d then p t else p2 (t - d)))" "{-e..d + d2+e}"]
      using step7
      using assms(3) step1 e
      by auto
  qed
  done

lemma ODEsol_split:
  assumes "ODEsol ode p d"
    and "0 < t1" and "t1 < d"
  shows "ODEsol ode p t1"
        "ODEsol ode (\<lambda>t. p (t + t1)) (d - t1)"
  subgoal
  proof-
    obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-e .. d+e}"
      using assms(1) unfolding ODEsol_def by blast
    then show ?thesis unfolding ODEsol_def
    using has_vderiv_on_subset[of "(\<lambda>t. state2vec (p t))" " (\<lambda>t. ODE2Vec ode (p t))" "{-e .. d+e}" "{-e..t1+e}"]
    using assms unfolding ODEsol_def by auto
qed
  subgoal
    unfolding ODEsol_def apply auto
    subgoal using assms by auto
    subgoal 
    proof-
      obtain e where e: "e > 0" "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec ode (p t))) {-e .. d+e}"
        using assms(1) unfolding ODEsol_def by blast
      have step1:"((\<lambda>t. state2vec (p (t))) has_vderiv_on (\<lambda>t. ODE2Vec ode (p (t)))) {t1-e..d+e}"
        using has_vderiv_on_subset[of "(\<lambda>t. state2vec (p t))" " (\<lambda>t. ODE2Vec ode (p t))" "{-e..d+e}" "{t1-e..d+e}"]
        using e assms  by auto
      have step2:"((\<lambda>t.(t+t1)) has_vderiv_on (\<lambda>t. 1)) {-e..d-t1+e}"
        by (auto intro!: derivative_intros)
      have step3:"t \<in> {- e..d - t1 + e} \<Longrightarrow> t + t1 \<in> {t1 - e..d + e}" for t
        using e assms by auto
      show ?thesis
        apply (rule exI[where x=e])
        apply auto 
        subgoal using e by auto
        using has_vderiv_on_compose2[of "(\<lambda>t. state2vec (p (t)))" "(\<lambda>t. ODE2Vec ode (p (t)))" "{t1-e..d+e}" "(\<lambda>t.(t+t1))" "(\<lambda>t. 1)" " {-e..d-t1+e}"]
        using step1 step2 step3 by auto
    qed
    done
  done

end
