theory ContinuousInv
  imports Logic
begin

lemma chainrule_Pair:
  assumes "\<forall>x. ((\<lambda>vv. g (vec2state_Pair vv)) has_derivative g' (vec2state_Pair x)) (at x within UNIV)"
    and "ODEsol ode p1 d" 
    and "ODEsol ode p2 d"
    and "t \<in> {0 .. d}"
  shows "((\<lambda>t. g (p1 t, p2 t)) has_derivative (\<lambda>s. g' (p1 t, p2 t) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))) (at t within {0..d})"
proof-
  have 1: "(\<And>x. x \<in> UNIV \<Longrightarrow> ((\<lambda>vv. g (vec2state_Pair vv)) has_derivative g' (vec2state_Pair x)) (at x))"
    using assms(1) by auto
  have 2: "0 \<le> t \<and> t \<le> d"
    using assms(4) by auto
  have 3: "((\<lambda>t. state2vec_Pair (p1 t, p2 t)) has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))) 
           (at t within {0..d})"
    using 2 assms(3) using ODEsol_old_Pair[OF assms(2)]unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def 
    by auto
  show ?thesis
  using 1 2 3 has_derivative_in_compose2[of UNIV "(\<lambda>vv. g (vec2state_Pair vv))" "(\<lambda>vv. g' (vec2state_Pair vv))" 
        "(\<lambda>t. state2vec_Pair (p1 t, p2 t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))"]
  by auto
qed

lemma chainrule_k:
  assumes "\<forall>x. ((\<lambda>v. g (vec2state_k v)) has_derivative g' (vec2state_k x)) (at x within UNIV)"
    and "\<forall>k. ODEsol ode (ps k) d"
    and "t \<in> {0 .. d}"
  shows "((\<lambda>t. g (\<lambda>i. ps i t)) has_derivative (\<lambda>s. g' (\<lambda>i. ps i t) (s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t)))) (at t within {0..d})"
  using has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state_k v))" "(\<lambda>v. g' (vec2state_k v))" 
        "(\<lambda>t. state2vec_k (\<lambda>i. ps i t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))"]
proof -
  have 1: "(\<And>x. x \<in> UNIV \<Longrightarrow> ((\<lambda>v. g (vec2state_k v)) has_derivative g' (vec2state_k x)) (at x))"
    using assms(1) by auto
  have 2: "0 \<le> t \<and> t \<le> d"
    using assms(3) by auto
  have 3: "((\<lambda>t. state2vec_k (\<lambda>i. ps i t)) has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))) (at t within {0..d})"
    using 2 assms(2) using ODEsol_old_k[OF assms(2)]unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def by auto
  show ?thesis
  using 1 2 3 has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state_k v))" "(\<lambda>v. g' (vec2state_k v))" 
        "(\<lambda>t. state2vec_k (\<lambda>i. ps i t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))"]
  by auto
qed


theorem Valid_inv_Pair:
  fixes inv :: "(state \<times> state) \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>vv. inv (vec2state_Pair vv)) has_derivative G' x) (at x within UNIV)"
      and "\<forall>ss. ((b (fst ss) \<and> b (snd ss)) \<longrightarrow> G' (state2vec_Pair ss) (ODE2Vec_Pair ode ss) = 0)"
      and "\<forall>ss. inv ss = r \<longrightarrow> (\<not>b (fst ss) \<longleftrightarrow> \<not> b (snd ss))"
    shows "\<Turnstile> {(\<lambda>S. (\<forall>es \<in> S. b (pproj es)) \<and>
               (\<forall>es1 es2. (es1 \<in> S \<and> es2 \<in> S \<and> lproj es1 x = 1 \<and> lproj es2 x = 2) \<longrightarrow> 
                inv (pproj es1, pproj es2) = r \<and> P (tproj es1) (tproj es2)))} 
              Cont ode b 
              {(\<lambda>S. \<forall>es1 es2. (es1 \<in> S \<and> es2 \<in> S \<and> lproj es1 x = 1 \<and> lproj es2 x = 2) \<longrightarrow> 
               (\<exists>p1 p2 d tr1 tr2. (tproj es1 = tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})] \<and>
                        tproj es2 = tr2 @ [WaitBlk d (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})] \<and>
                        (\<forall>t\<in>{0..d}. inv (p1 t, p2 t) = r) \<and> P tr1 tr2)))}"
  unfolding hyper_hoare_triple_def
  apply (intro allI impI)
  subgoal for S es1 es2
  proof-
    assume a0: "(\<forall>es\<in>S. b (pproj es)) \<and> (\<forall>es1 es2. es1 \<in> S \<and> es2 \<in> S \<and> lproj es1 x = 1 \<and> lproj es2 x = 2 
    \<longrightarrow> inv (pproj es1, pproj es2) = r \<and> P (tproj es1) (tproj es2))"
    and a1: "es1 \<in> sem (Cont ode b) S \<and> es2 \<in> sem (Cont ode b) S \<and> lproj es1 x = 1 \<and> lproj es2 x = 2"
    from a1 have "\<exists>es1' tr1. (es1' \<in> S \<and> big_step (Cont ode b) (pproj es1') tr1 (pproj es1) \<and>
                  lproj es1'  = (lproj es1) \<and> (tproj es1) = (tproj es1') @ tr1)"
                 "\<exists>es2' tr2. (es2' \<in> S \<and> big_step (Cont ode b) (pproj es2') tr2 (pproj es2) \<and>
                  lproj es2'  = (lproj es2) \<and> (tproj es2) = (tproj es2') @ tr2)"
      using in_sem[of es1 "Cont ode b" S] in_sem[of es2 "Cont ode b" S] 
      by (metis fst_eqD lproj_def pproj_def sndI tproj_def)+
    then obtain es1' es2' tr1 tr2 where b1 : 
      "es1' \<in> S \<and> big_step (Cont ode b) (pproj es1') tr1 (pproj es1) \<and>
        lproj es1'  = (lproj es1) \<and> (tproj es1) = (tproj es1') @ tr1"
      "es2' \<in> S \<and> big_step (Cont ode b) (pproj es2') tr2 (pproj es2) \<and>
       lproj es2'  = (lproj es2) \<and> (tproj es2) = (tproj es2') @ tr2"
      by auto 
    with a1 have b2: "lproj es1' x = 1" "lproj es2' x = 2"
      by auto
    with a0 b1 have b3: "inv (pproj es1', pproj es2') = r" "P (tproj es1') (tproj es2')"
      "b (pproj es1')" "b (pproj es2')"
      by blast+
    with b1 have "(\<exists>p1 d1. d1 > 0 \<and> ODEsol ode p1 d1 \<and> (\<forall>t. t \<ge> 0 \<and> t < d1 \<longrightarrow> b (p1 t)) \<and> 
    \<not>b (p1 d1) \<and> p1 0 = (pproj es1') \<and> tr1 = [WaitBlk d1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})])"
    "(\<exists>p2 d2. d2 > 0 \<and> ODEsol ode p2 d2 \<and> (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<and> 
    \<not>b (p2 d2) \<and> p2 0 = (pproj es2') \<and> tr2 = [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})])"
      by (smt (verit, del_insts) contE)+
    then obtain p1 p2 d1 d2 where b4: 
      "d1 > 0 \<and> ODEsol ode p1 d1 \<and> (\<forall>t. t \<ge> 0 \<and> t < d1 \<longrightarrow> b (p1 t)) \<and> 
       \<not>b (p1 d1) \<and> p1 0 = (pproj es1') \<and> tr1 = [WaitBlk d1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})]"
      "d2 > 0 \<and> ODEsol ode p2 d2 \<and> (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<and> 
       \<not>b (p2 d2) \<and> p2 0 = (pproj es2') \<and> tr2 = [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]"
      by auto
    let ?d = "min d1 d2"
    from b3(1) b4 have b5: "\<forall>t. t \<ge> 0 \<and> t < ?d \<longrightarrow> b (p1 t) \<and> b (p2 t)" "inv (p1 0, p2 0) = r"
      by auto
    from b4 have b6: "\<not> b (p1 ?d) \<or> \<not> b (p2 ?d)"
      by linarith
    from b4 have "ODEsol ode p1 ?d" "ODEsol ode p2 ?d"
      using ODEsol_le[of ode p1 d1 ?d] ODEsol_le[of ode p2 d2 ?d]
      by auto
    then have 1: "\<forall>t \<in> {0 .. ?d}. ((\<lambda>t. inv (p1 t, p2 t)) has_derivative 
    (\<lambda>s. G' (state2vec_Pair (p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))) (at t within {0 .. ?d})"
      using chainrule_Pair[of inv "\<lambda>x. G'(state2vec_Pair x)" ode p1 ?d p2] assms(1)
      by auto
    then have 2: "\<forall>s. G' (state2vec_Pair (p1 t, p2 t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)) = 
              s *\<^sub>R G' (state2vec_Pair (p1 t, p2 t)) (1 *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))" if "t\<in>{0 .. ?d}" for t
      unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))"]
      by (smt (verit) assms(1) has_derivative_def linear_simps(5) real_scaleR_def scaleR_scaleR)
    have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4: "\<forall>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)) = 
    s *\<^sub>R G' (state2vec_Pair(p1 t, p2 t)) (ODE2Vec_Pair ode (p1 t, p2 t))" if "t\<in>{0 .. ?d}" for t
      using 2 3 that by auto
    have 5: "\<forall>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))= 0" if "t\<in>{0 ..<?d}" for t
      using 4 assms(2) b5 that by auto
    then have 6: "\<forall>t\<in>{0..?d}. inv (p1 t, p2 t) = r"
      using mvt_real_eq[of ?d "(\<lambda>t. inv(p1 t, p2 t))""\<lambda>t. (\<lambda>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))"]
      using 1 5 b5 by auto
    then have "inv (p1 ?d, p2 ?d) = r"
      using ODEsol_def \<open>ODEsol ode p2 (min d1 d2)\<close> atLeastAtMost_iff by blast
    with b6 assms(3) have 7: "\<not> b (p1 ?d) \<and> \<not> b (p2 ?d)"
      by simp
    with b4 have "d1 = d2"
      by (metis linorder_not_le min_def order_le_less)
    then show ?thesis
      using b1 b3 b4 6
      by auto
  qed
  done

theorem Valid_inv_Pair_forall:
  fixes inv :: "(state \<times> state) \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>vv. inv (vec2state_Pair vv)) has_derivative G' x) (at x within UNIV)"
      and "\<forall>ss. ((b (fst ss) \<and> b (snd ss)) \<longrightarrow> G' (state2vec_Pair ss) (ODE2Vec_Pair ode ss) = 0)"
      and "\<forall>ss. inv ss = r \<longrightarrow> (\<not>b (fst ss) \<longleftrightarrow> \<not> b (snd ss))"
    shows "\<Turnstile> {(\<lambda>S. (\<forall>es \<in> S. b (pproj es)) \<and> (\<forall>es1 \<in> S. \<forall>es2 \<in> S. P (tproj es1) (tproj es2)) \<and> 
               (\<forall>es1 es2. (es1 \<in> S \<and> es2 \<in> S) \<longrightarrow> inv (pproj es1, pproj es2) = r ))} 
              Cont ode b 
              {(\<lambda>S. \<forall>es1 es2. (es1 \<in> S \<and> es2 \<in> S) \<longrightarrow> 
               (\<exists>p1 p2 d tr1 tr2. (tproj es1 = tr1 @ [WaitBlk d (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})] \<and>
                        tproj es2 = tr2 @ [WaitBlk d (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})] \<and>
                        (\<forall>t\<in>{0..d}. inv (p1 t, p2 t) = r) \<and> P tr1 tr2)))}"
  unfolding hyper_hoare_triple_def
  apply (intro allI impI)
  subgoal for S es1 es2
  proof-
    assume a0: "(\<forall>es\<in>S. b (pproj es)) \<and> (\<forall>es1\<in>S. \<forall>es2\<in>S. P (tproj es1) (tproj es2)) 
                \<and> (\<forall>es1 es2. es1 \<in> S \<and> es2 \<in> S \<longrightarrow> inv (pproj es1, pproj es2) = r)"
    and a1: "es1 \<in> sem (Cont ode b) S \<and> es2 \<in> sem (Cont ode b) S"
    from a1 have "\<exists>es1' tr1. (es1' \<in> S \<and> big_step (Cont ode b) (pproj es1') tr1 (pproj es1) \<and>
                  lproj es1'  = (lproj es1) \<and> (tproj es1) = (tproj es1') @ tr1)"
                 "\<exists>es2' tr2. (es2' \<in> S \<and> big_step (Cont ode b) (pproj es2') tr2 (pproj es2) \<and>
                  lproj es2'  = (lproj es2) \<and> (tproj es2) = (tproj es2') @ tr2)"
      using in_sem[of es1 "Cont ode b" S] in_sem[of es2 "Cont ode b" S] 
      by (metis fst_eqD lproj_def pproj_def sndI tproj_def)+
    then obtain es1' es2' tr1 tr2 where b1 : 
      "es1' \<in> S \<and> big_step (Cont ode b) (pproj es1') tr1 (pproj es1) \<and>
        lproj es1'  = (lproj es1) \<and> (tproj es1) = (tproj es1') @ tr1"
      "es2' \<in> S \<and> big_step (Cont ode b) (pproj es2') tr2 (pproj es2) \<and>
       lproj es2'  = (lproj es2) \<and> (tproj es2) = (tproj es2') @ tr2"
      by auto 
    with a0 have b3: "inv (pproj es1', pproj es2') = r" "P (tproj es1') (tproj es2')"
      "b (pproj es1')" "b (pproj es2')"
      by blast+
    with b1 have "(\<exists>p1 d1. d1 > 0 \<and> ODEsol ode p1 d1 \<and> (\<forall>t. t \<ge> 0 \<and> t < d1 \<longrightarrow> b (p1 t)) \<and> 
    \<not>b (p1 d1) \<and> p1 0 = (pproj es1') \<and> tr1 = [WaitBlk d1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})])"
    "(\<exists>p2 d2. d2 > 0 \<and> ODEsol ode p2 d2 \<and> (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<and> 
    \<not>b (p2 d2) \<and> p2 0 = (pproj es2') \<and> tr2 = [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})])"
      by (smt (verit, del_insts) contE)+
    then obtain p1 p2 d1 d2 where b4: 
      "d1 > 0 \<and> ODEsol ode p1 d1 \<and> (\<forall>t. t \<ge> 0 \<and> t < d1 \<longrightarrow> b (p1 t)) \<and> 
       \<not>b (p1 d1) \<and> p1 0 = (pproj es1') \<and> tr1 = [WaitBlk d1 (\<lambda>\<tau>. State (p1 \<tau>)) ({}, {})]"
      "d2 > 0 \<and> ODEsol ode p2 d2 \<and> (\<forall>t. t \<ge> 0 \<and> t < d2 \<longrightarrow> b (p2 t)) \<and> 
       \<not>b (p2 d2) \<and> p2 0 = (pproj es2') \<and> tr2 = [WaitBlk d2 (\<lambda>\<tau>. State (p2 \<tau>)) ({}, {})]"
      by auto
    let ?d = "min d1 d2"
    from b3(1) b4 have b5: "\<forall>t. t \<ge> 0 \<and> t < ?d \<longrightarrow> b (p1 t) \<and> b (p2 t)" "inv (p1 0, p2 0) = r"
      by auto
    from b4 have b6: "\<not> b (p1 ?d) \<or> \<not> b (p2 ?d)"
      by linarith
    from b4 have "ODEsol ode p1 ?d" "ODEsol ode p2 ?d"
      using ODEsol_le[of ode p1 d1 ?d] ODEsol_le[of ode p2 d2 ?d]
      by auto
    then have 1: "\<forall>t \<in> {0 .. ?d}. ((\<lambda>t. inv (p1 t, p2 t)) has_derivative 
    (\<lambda>s. G' (state2vec_Pair (p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))) (at t within {0 .. ?d})"
      using chainrule_Pair[of inv "\<lambda>x. G'(state2vec_Pair x)" ode p1 ?d p2] assms(1)
      by auto
    then have 2: "\<forall>s. G' (state2vec_Pair (p1 t, p2 t)) ((s *\<^sub>R 1) *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)) = 
              s *\<^sub>R G' (state2vec_Pair (p1 t, p2 t)) (1 *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))" if "t\<in>{0 .. ?d}" for t
      unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))"]
      by (smt (verit) assms(1) has_derivative_def linear_simps(5) real_scaleR_def scaleR_scaleR)
    have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4: "\<forall>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)) = 
    s *\<^sub>R G' (state2vec_Pair(p1 t, p2 t)) (ODE2Vec_Pair ode (p1 t, p2 t))" if "t\<in>{0 .. ?d}" for t
      using 2 3 that by auto
    have 5: "\<forall>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t))= 0" if "t\<in>{0 ..<?d}" for t
      using 4 assms(2) b5 that by auto
    then have 6: "\<forall>t\<in>{0..?d}. inv (p1 t, p2 t) = r"
      using mvt_real_eq[of ?d "(\<lambda>t. inv(p1 t, p2 t))""\<lambda>t. (\<lambda>s. G' (state2vec_Pair(p1 t, p2 t)) (s *\<^sub>R ODE2Vec_Pair ode (p1 t, p2 t)))"]
      using 1 5 b5 by auto
    then have "inv (p1 ?d, p2 ?d) = r"
      using ODEsol_def \<open>ODEsol ode p2 (min d1 d2)\<close> atLeastAtMost_iff by blast
    with b6 assms(3) have 7: "\<not> b (p1 ?d) \<and> \<not> b (p2 ?d)"
      by simp
    with b4 have "d1 = d2"
      by (metis linorder_not_le min_def order_le_less)
    then show ?thesis
      using b1 b3 b4 6
      by auto
  qed
  done

lemma in_sem_k: "\<lbrakk>\<forall>k. ess k \<in> sem C S\<rbrakk> \<Longrightarrow>
      \<exists>ess' trs. (\<forall>k. ess' k \<in> S \<and> big_step C (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
proof-
  assume a0: "\<forall>k. ess k \<in> sem C S"
  then have "\<forall>k. (\<exists>es tr. es \<in> S \<and> big_step C (pproj es) tr (pproj (ess k)) \<and> 
             (lproj es) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj es) @ tr)"
    apply (simp add: in_sem lproj_def tproj_def pproj_def)
    by blast
  then show ?thesis
    by metis
qed

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

definition ex2s_k :: "('k \<Rightarrow> ('lvar, 'lval) exstate) \<Rightarrow> ('k \<Rightarrow> state)" where
  "ex2s_k ess k = pproj (ess k)"

theorem Valid_inv_k:
  fixes inv :: "(('k :: finite) \<Rightarrow> state) \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state_k v)) has_derivative G' x) (at x within UNIV)"
      and "\<forall>ss. ((\<forall>k. b (ss k)) \<longrightarrow> G' (state2vec_k ss) (ODE2Vec_k ode ss) = 0)"
      and "\<forall>ss. inv ss = r \<longrightarrow> (\<exists>k. \<not> b (ss k)) \<longrightarrow> (\<forall>k'. \<not> b (ss k'))"
    shows "\<Turnstile> {(\<lambda>S. (\<forall>es \<in> S. b (pproj es)) \<and> 
               (\<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> inv (ex2s_k ess) = r \<and> 
                P (\<lambda>k. tproj (ess k))))} 
              Cont ode b 
              {(\<lambda>S. \<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> 
               (\<exists>ps d trs. (\<forall>k. tproj (ess k) = (trs k) @ [WaitBlk d (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})] \<and> 
               (\<forall>t\<in>{0..d}. inv (\<lambda>k. ps k t) = r) \<and> P trs)))}"
  unfolding hyper_hoare_triple_def
  apply (intro allI impI)
  subgoal for S ess
  proof-
    assume a0: "(\<forall>es\<in>S. b (pproj es)) \<and> (\<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> inv (ex2s_k ess) = r \<and> P (\<lambda>k. tproj (ess k)))"
       and a1: " \<forall>k. ess k \<in> sem (Cont ode b) S \<and> lproj (ess k) x = k"
    from a1 have "\<exists>ess' trs. (\<forall>k. ess' k \<in> S \<and> big_step (Cont ode b) (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
      using in_sem_k[of ess "Cont ode b" S] by auto
    then obtain ess' trs where b1 : "(\<forall>k. ess' k \<in> S \<and> big_step (Cont ode b) (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
      by auto
    with a1 have b2: "\<forall>k. ess' k \<in> S \<and> lproj (ess' k) x = k"
      by auto
    with a0 have b3: "inv (ex2s_k ess') = r" "P (\<lambda>k. tproj (ess' k))"
      by blast+
    with a0 b1 have "\<forall>k. (\<exists>p d. d > 0 \<and> ODEsol ode p d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> 
    \<not>b (p d) \<and> p 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      by (smt (verit, best) contE)
    then have "\<exists>ps ds. (\<forall>k. ds k > 0 \<and> ODEsol ode (ps k) (ds k) \<and> (\<forall>t. t \<ge> 0 \<and> t < ds k \<longrightarrow> b (ps k t)) \<and> 
    \<not>b (ps k (ds k)) \<and> ps k 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk (ds k) (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})])"
      by metis
    then obtain ps ds where b4: "\<forall>k. ds k > 0 \<and> ODEsol ode (ps k) (ds k) \<and> (\<forall>t. t \<ge> 0 \<and> t < ds k \<longrightarrow> b (ps k t)) \<and> 
    \<not>b (ps k (ds k)) \<and> ps k 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk (ds k) (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})]"
      by auto
    then have "\<exists>k'. \<forall>k. ds k \<ge> ds k'"
      using finite_arg_min[of ds] by blast
    then obtain k' where b5: "\<forall>k. ds k \<ge> ds k'" by auto
    let ?d = "ds k'"
    from b4 b5 have b6: "\<forall>k t. t \<ge> 0 \<and> t < ?d \<longrightarrow> b (ps k t)" 
      using order_less_le_trans by blast
    from b3 b4 have b7: "inv (\<lambda>k. ps k 0) = r"
      by (metis (no_types, lifting) ex2s_k_def ext)
    from b4 b5 have "\<forall>k. ODEsol ode (ps k) ?d"
      by (meson ODEsol_le order_less_le)    
    then have 1: "\<forall>t \<in> {0 .. ds k'}. ((\<lambda>t. inv (\<lambda>k. ps k t)) has_derivative 
         (\<lambda>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)))) (at t within {0 .. ?d})"
      using chainrule_k[of inv "\<lambda>x. G'(state2vec_k x)" ode ps ?d ] assms(1)
      by auto
    then have 2: "\<forall>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)) = 
                 s *\<^sub>R G' (state2vec_k (\<lambda>k. ps k t)) (1 *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t))" if "t\<in>{0 .. ?d}" for t
      unfolding has_derivative_def bounded_linear_def 
      using that linear_iff[of "(\<lambda>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)))"]
      using assms(1) linear_simps(5) by fastforce      
    have 3: "\<forall>s. (s *\<^sub>R 1) = s" by simp
    have 4: "\<forall>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)) = 
             s *\<^sub>R G' (state2vec_k (\<lambda>k. ps k t)) (1 *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t))" if "t\<in>{0 .. ?d}" for t
      using 2 3 that by auto
    have 5: "\<forall>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)) = 0" if "t\<in>{0 ..<?d}" for t
      using 4 assms(2) b6 that by auto
    then have 6: "\<forall>t\<in>{0..?d}. inv (\<lambda>k. ps k t) = r"
      using mvt_real_eq[of ?d "(\<lambda>t. inv (\<lambda>k. ps k t))""\<lambda>t. (\<lambda>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)))"]
      using 1 5 b7 by auto
    with b4 have "inv (\<lambda>k. ps k ?d) = r"
      by (meson ODEsol_def atLeastAtMost_iff b4 dual_order.refl)
    with assms(3) b4 have "\<forall>k. \<not> b (ps k ?d)"
      by blast
    with b4 b5 have "\<forall>k. ds k = ?d"
      by (metis order_less_le)
    with b1 b4 b3(2) 6 show ?thesis
      apply (rule_tac x = ps in exI, rule_tac x = ?d in exI, rule_tac x = "(\<lambda>k. tproj (ess' k))" in exI)
      by metis
  qed
  done






(*

definition state2vec_k :: "(('k :: finite) \<Rightarrow> state) \<Rightarrow> real^('k \<times> var)"
  where "state2vec_k ss = (\<chi> x. ss (fst x) (snd x))"

definition vec2state_k :: "real^(('k :: finite) \<times> char) \<Rightarrow>('k \<Rightarrow> state) "
  where "(vec2state_k V) k v = V $ (k, v)"

lemma vec_state_map1_k[simp]: "vec2state_k (state2vec_k s) = s"
  unfolding vec2state_k_def state2vec_k_def by auto

lemma vec_state_map2_k[simp]: "state2vec_k (vec2state_k s) = s"
  unfolding vec2state_k_def state2vec_k_def by auto

text \<open>Mutiple traces\<close>
thm sum_divide_distrib

fun ODE2Vec_k :: "ODE \<Rightarrow> (('k :: finite) \<Rightarrow> state) \<Rightarrow> (real^('k \<times> var))" where
  "ODE2Vec_k (ODE f) ss = state2vec_k (\<lambda>k. \<lambda>x. f x (ss k))"

lemma "ODEsol (ODE f) (ps k) d \<Longrightarrow> 
      ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec (ODE f) (ps k t))) {0..d}"
  using ODEsol_old[of "ODE f" "ps k" d] by auto

lemma ODEsol_old_k:
  "\<lbrakk>\<forall>k. ((\<lambda>t. state2vec (ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec (ODE f) (ps k t))) {0..d}\<rbrakk> 
  \<Longrightarrow> ((\<lambda>t. state2vec_k (\<lambda>k. ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec_k (ODE f) (\<lambda>k. ps k t))) {0 .. d}"
  apply (simp add: state2vec_k_def ODEsol_old)

lemma ODEsol_old_k:
  assumes "\<forall>k. ODEsol ode (ps k) d"
  shows "((\<lambda>t. state2vec_k (\<lambda>k. ps k t)) has_vderiv_on (\<lambda>t. ODE2Vec_k ode (\<lambda>k. ps k t))) {0 .. d}"
proof-
  have "\<exists>f. ode = ODE f"
    by (meson ODE.exhaust)

lemma chainrule_k:
  assumes "\<forall>x. ((\<lambda>v. g (vec2state_k v)) has_derivative g' (vec2state_k x)) (at x within UNIV)"
    and "\<forall>k. ODEsol ode (ps k) d"
    and "t \<in> {0 .. d}"
  shows "((\<lambda>t. g (\<lambda>i. ps i t)) has_derivative (\<lambda>s. g' (\<lambda>i. ps i t) (s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t)))) (at t within {0..d})"
  using has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state_k v))" "(\<lambda>v. g' (vec2state_k v))" 
        "(\<lambda>t. state2vec_k (\<lambda>i. ps i t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))"]
proof -
  have 1: "(\<And>x. x \<in> UNIV \<Longrightarrow> ((\<lambda>v. g (vec2state_k v)) has_derivative g' (vec2state_k x)) (at x))"
    using assms(1) by auto
  have 2: "0 \<le> t \<and> t \<le> d"
    using assms(3) by auto
  have 3: "((\<lambda>t. state2vec_k (\<lambda>i. ps i t)) has_derivative (\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))) (at t within {0..d})"
    using 2 assms(2) using ODEsol_old_k[OF assms(2)]unfolding ODEsol_def has_vderiv_on_def has_vector_derivative_def by auto
  show ?thesis
  using 1 2 3 has_derivative_in_compose2[of UNIV "(\<lambda>v. g (vec2state_k v))" "(\<lambda>v. g' (vec2state_k v))" 
        "(\<lambda>t. state2vec_k (\<lambda>i. ps i t))" "{0 .. d}" t "(\<lambda>s. s *\<^sub>R ODE2Vec_k ode (\<lambda>i. ps i t))"]
  by auto
qed


definition k_sem where
  "k_sem C states states' \<longleftrightarrow> (\<forall>i. (fst (states i) = fst (states' i) \<and> 
   (snd (states' i)) \<in> sem C (snd (states i))))"

lemma k_semI:
  assumes "\<And>i. (fst (states i) = fst (states' i) \<and> (snd (states' i)) \<in> sem C (snd (states i)) )"
  shows "k_sem C states states'"
  by (simp add: assms k_sem_def)

lemma k_semE:
  assumes "k_sem C states states'"
  shows "fst (states i) = fst (states' i) \<and> (snd (states' i)) \<in> sem C (snd (states i))"
  using assms k_sem_def by fastforce

definition ess2ss :: "('k \<Rightarrow> ('lvar, 'lval) exstate) \<Rightarrow> ('k \<Rightarrow> state)" where
  "ess2ss ess k = pproj (ess k)"

lemma in_sem_k: "\<lbrakk>\<forall>k. ess k \<in> sem C S\<rbrakk> \<Longrightarrow>
      \<exists>ess' trs. (\<forall>k. ess' k \<in> S \<and> big_step C (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
proof-
  assume a0: "\<forall>k. ess k \<in> sem C S"
  then have "\<forall>k. (\<exists>es tr. es \<in> S \<and> big_step C (pproj es) tr (pproj (ess k)) \<and> 
             (lproj es) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj es) @ tr)"
    apply (simp add: in_sem lproj_def tproj_def pproj_def)
    by blast
  then show ?thesis
    by metis
qed

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

theorem Valid_inv:
  fixes inv :: "(('k :: finite) \<Rightarrow> state) \<Rightarrow> real"
  assumes "\<forall>x. ((\<lambda>v. inv (vec2state_k v)) has_derivative G' x) (at x within UNIV)"
      and "\<forall>ss. ((\<forall>k. b (ss k)) \<longrightarrow> G' (state2vec_k ss) (ODE2Vec_k ode ss) = 0)"
      and "\<forall>ss. inv ss = r \<longrightarrow> (\<exists>k. \<not> b (ss k)) \<longrightarrow> (\<forall>k'. \<not> b (ss k'))"
    shows "\<Turnstile> {(\<lambda>S. (\<forall>es \<in> S. tproj es = [] \<and> b (pproj es)) \<and> 
               (\<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> inv (ess2ss ess) = r))} 
              Cont ode b 
              {(\<lambda>S. \<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> 
               (\<exists>ps d. (\<forall>k. tproj (ess k) = [WaitBlk d (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})] \<and> 
               (\<forall>t\<in>{0..d}. inv (\<lambda>k. ps k t) = r))))}"
  unfolding hyper_hoare_triple_def
  apply (intro allI impI)
  subgoal for S ess
  proof-
    assume a0: "(\<forall>es\<in>S. tproj es = [] \<and> b (pproj es)) \<and> (\<forall>ess. (\<forall>k. ess k \<in> S \<and> lproj (ess k) x = k) \<longrightarrow> inv (ess2ss ess) = r)"
       and a1: " \<forall>k. ess k \<in> sem (Cont ode b) S \<and> lproj (ess k) x = k"
    from a1 have "\<exists>ess' trs. (\<forall>k. ess' k \<in> S \<and> big_step (Cont ode b) (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
      using in_sem_k[of ess "Cont ode b" S] by auto
    then obtain ess' trs where b1 : "(\<forall>k. ess' k \<in> S \<and> big_step (Cont ode b) (pproj (ess' k)) (trs k) (pproj (ess k)) \<and>
      (lproj (ess' k)) = (lproj (ess k)) \<and> (tproj (ess k)) = (tproj (ess' k)) @ (trs k))"
      by auto
    with a1 have b2: "\<forall>k. ess' k \<in> S \<and> lproj (ess' k) x = k"
      by auto
    with a0 have b3: "inv (ess2ss ess') = r" "\<forall>k. tproj (ess' k) = [] \<and> b (pproj (ess' k))"
      by blast+
    with b1 have "\<forall>k. (\<exists>p d. d > 0 \<and> ODEsol ode p d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> 
    \<not>b (p d) \<and> p 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})])"
      by (smt (verit, del_insts) contE)
    then have "\<exists>ps ds. (\<forall>k. ds k > 0 \<and> ODEsol ode (ps k) (ds k) \<and> (\<forall>t. t \<ge> 0 \<and> t < ds k \<longrightarrow> b (ps k t)) \<and> 
    \<not>b (ps k (ds k)) \<and> ps k 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk (ds k) (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})])"
      by metis
    then obtain ps ds where b4: "\<forall>k. ds k > 0 \<and> ODEsol ode (ps k) (ds k) \<and> (\<forall>t. t \<ge> 0 \<and> t < ds k \<longrightarrow> b (ps k t)) \<and> 
    \<not>b (ps k (ds k)) \<and> ps k 0 = (pproj (ess' k)) \<and> trs k = [WaitBlk (ds k) (\<lambda>\<tau>. State (ps k \<tau>)) ({}, {})]"
      by auto
    then have "\<exists>k'. \<forall>k. ds k \<ge> ds k'"
      using finite_arg_min[of ds] by blast
    then obtain k' where "\<forall>k. ds k \<ge> ds k'" by auto
    have "\<forall>t \<in> {0 .. ds k'}. ((\<lambda>t. inv (\<lambda>k. ps k t)) has_derivative 
         (\<lambda>s. G' (state2vec_k (\<lambda>k. ps k t)) (s *\<^sub>R ODE2Vec_k ode (\<lambda>k. ps k t)))) (at t within {0 .. ds k'})"
*)
    
end
