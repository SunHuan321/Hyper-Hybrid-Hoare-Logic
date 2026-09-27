theory HybridLoops
  imports H3L_Core.HybridSyntacticAssertions
begin

section \<open>Synchronized Guarded Control Flow\<close>

definition lnot :: "fform \<Rightarrow> fform" where
  "lnot b \<sigma> \<longleftrightarrow> \<not> b \<sigma>"

definition if_then_else :: "fform \<Rightarrow> proc \<Rightarrow> proc \<Rightarrow> proc" where
  "if_then_else b C1 C2 = IChoice (Assume b; C1) (Assume (lnot b); C2)"

definition while_cond :: "fform \<Rightarrow> proc \<Rightarrow> proc" where
  "while_cond b C = (Rep (Assume b; C)); Assume (lnot b)"

definition low_exp where
  "low_exp b S \<longleftrightarrow> (\<forall>\<phi>\<in>S. \<forall>\<phi>'\<in>S. b (pproj \<phi>) = b (pproj \<phi>'))"

definition holds_forall where
  "holds_forall b S \<longleftrightarrow> (\<forall>\<phi>\<in>S. b (pproj \<phi>))"

definition emp where
  "emp S \<longleftrightarrow> S = {}"

definition exists_nat where
  "exists_nat I S \<longleftrightarrow> (\<exists>n. I n S)"

lemma sem_empty [simp]:
  "sem C {} = {}"
  by (auto simp add: sem_def)

lemma low_exp_lnot:
  "low_exp b S \<longleftrightarrow> low_exp (lnot b) S"
  by (simp add: lnot_def low_exp_def)

lemma holds_forall_empty:
  "holds_forall b {}"
  by (simp add: holds_forall_def)

lemma low_exp_two_cases:
  assumes "low_exp b S"
  shows "holds_forall b S \<or> holds_forall (lnot b) S"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: holds_forall_empty)
next
  case False
  then obtain \<phi> where "\<phi> \<in> S"
    by blast
  show ?thesis
  proof (cases "b (pproj \<phi>)")
    case True
    then have "\<And>\<psi>. \<psi> \<in> S \<Longrightarrow> b (pproj \<psi>)"
      using assms \<open>\<phi> \<in> S\<close> unfolding low_exp_def by metis
    then show ?thesis
      by (simp add: holds_forall_def)
  next
    case False
    then have "\<And>\<psi>. \<psi> \<in> S \<Longrightarrow> lnot b (pproj \<psi>)"
      using assms \<open>\<phi> \<in> S\<close> unfolding low_exp_def lnot_def by metis
    then show ?thesis
      by (simp add: holds_forall_def)
  qed
qed

lemma sem_assume_low_exp:
  assumes "holds_forall b S"
  shows "sem (Assume b) S = S"
    and "sem (Assume (lnot b)) S = {}"
  using assms
  by (fastforce simp add: assume_sem holds_forall_def lnot_def pproj_def)+

lemma sem_assume_low_exp_seq:
  assumes "holds_forall b S"
  shows "sem (Assume b; C) S = sem C S"
    and "sem (Assume (lnot b); C) S = {}"
  using assms by (simp_all add: sem_assume_low_exp sem_seq)

lemma lnot_involution:
  "lnot (lnot b) = b"
  by (rule ext) (simp add: lnot_def)

lemma sem_if_then_else:
  shows "holds_forall b S \<Longrightarrow> sem (if_then_else b C1 C2) S = sem C1 S"
    and "holds_forall (lnot b) S \<Longrightarrow> sem (if_then_else b C1 C2) S = sem C2 S"
proof -
  assume asm: "holds_forall b S"
  then show "sem (if_then_else b C1 C2) S = sem C1 S"
    by (simp add: if_then_else_def sem_assume_low_exp_seq sem_if)
next
  assume asm: "holds_forall (lnot b) S"
  have "sem (Assume b; C1) S = {}"
    using sem_assume_low_exp_seq(2)[OF asm, of C1] by (simp add: lnot_involution)
  moreover have "sem (Assume (lnot b); C2) S = sem C2 S"
    using sem_assume_low_exp_seq(1)[OF asm, of C2] .
  ultimately show "sem (if_then_else b C1 C2) S = sem C2 S"
    by (simp add: if_then_else_def sem_if)
qed

theorem if_synchronized:
  assumes "\<Turnstile> {conj P (holds_forall b)} C1 {Q}"
      and "\<Turnstile> {conj P (holds_forall (lnot b))} C2 {Q}"
    shows "\<Turnstile> {conj P (low_exp b)} if_then_else b C1 C2 {Q}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume asm0: "conj P (low_exp b) S"
  show "Q (sem (if_then_else b C1 C2) S)"
  proof (cases "holds_forall b S")
    case True
    then show ?thesis
      by (metis asm0 assms(1) conj_def hyper_hoare_tripleE sem_if_then_else(1))
  next
    case False
    then have "holds_forall (lnot b) S"
      using asm0 conj_def low_exp_two_cases by blast
    then show ?thesis
      by (metis asm0 assms(2) conj_def hyper_hoare_tripleE sem_if_then_else(2))
  qed
qed

subsection \<open>Synchronized While\<close>

lemma while_synchronized_rec:
  assumes "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} (Assume b; C) {conj (I (Suc n)) (low_exp b)}"
      and "conj (I 0) (low_exp b) S"
    shows "conj (I n) (low_exp b) (iterate_sem n (Assume b; C) S) \<or>
           holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
  using assms
proof (induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then have rec: "conj (I n) (low_exp b) (iterate_sem n (Assume b; C) S) \<or>
      holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
    by blast
  show ?case
  proof (cases "conj (I n) (holds_forall b) (iterate_sem n (Assume b; C) S)")
    case True
    then show ?thesis
      using Suc.prems(1) hyper_hoare_tripleE by fastforce
  next
    case False
    then have "holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
      by (metis conj_def low_exp_two_cases rec)
    then have "iterate_sem (Suc n) (Assume b; C) S = {}"
      by (metis iterate_sem.simps(2) lnot_involution sem_assume_low_exp_seq(2))
    then show ?thesis
      by (simp add: holds_forall_empty)
  qed
qed

lemma false_then_empty_later:
  assumes "holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
      and "m > n"
    shows "iterate_sem m (Assume b; C) S = {}"
proof -
  have aux: "\<And>T. holds_forall (lnot b) T \<Longrightarrow> sem (Assume b; C) T = {}"
  proof -
    fix T assume h: "holds_forall (lnot b) T"
    have "sem (Assume (lnot (lnot b)); C) T = {}"
      using sem_assume_low_exp_seq(2)[where b = "lnot b" and C = C and S = T, OF h] .
    then show "sem (Assume b; C) T = {}" by (simp add: lnot_involution)
  qed
  have tail: "\<And>k. iterate_sem (n + Suc k) (Assume b; C) S = {}"
  proof -
    fix k
    show "iterate_sem (n + Suc k) (Assume b; C) S = {}"
    proof (induct k)
      case 0
      have "iterate_sem (n + Suc 0) (Assume b; C) S
          = sem (Assume b; C) (iterate_sem n (Assume b; C) S)" by simp
      also have "\<dots> = {}" using assms(1) aux by blast
      finally show ?case by simp
    next
      case (Suc k)
      have "iterate_sem (n + Suc (Suc k)) (Assume b; C) S
          = sem (Assume b; C) (iterate_sem (n + Suc k) (Assume b; C) S)" by simp
      also have "\<dots> = sem (Assume b; C) {}" using Suc by simp
      also have "\<dots> = {}" by simp
      finally show ?case .
    qed
  qed
  obtain k where km: "m - n = Suc k"
    using assms(2) by (cases "m - n") auto
  from tail have "iterate_sem (n + Suc k) (Assume b; C) S = {}" .
  moreover have "m = n + Suc k" using assms(2) km by simp
  ultimately show ?thesis by simp
qed

lemma sem_union_swap:
  "sem C (\<Union>x\<in>S. f x) = (\<Union>x\<in>S. sem C (f x))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix y assume "y \<in> ?A"
    then obtain x where "x \<in> S" "y \<in> sem C (f x)"
      using UN_iff in_sem[of y C] by force
    then show "y \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
    by (simp add: SUP_least SUP_upper sem_monotonic)
qed

lemma split_union_triple:
  "(\<Union>(m::nat). f m) =
    (\<Union>m\<in>{m |m. m < n}. f m) \<union> f n \<union> (\<Union>m\<in>{m |m. m > n}. f m)"
    (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
    by blast
  show "?A \<subseteq> ?B"
  proof
    fix x assume "x \<in> ?A"
    then obtain m where "x \<in> f m"
      by blast
    then have "m < n \<or> m = n \<or> m > n"
      by force
    then show "x \<in> ?B"
      using \<open>x \<in> f m\<close> by auto
  qed
qed

lemma while_synchronized_case_1:
  assumes "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b; C) S)"
      and "holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
    shows "sem (while_cond b C) S = iterate_sem n (Assume b; C) S"
proof -
  have later_empty: "\<And>m. m > n \<Longrightarrow> iterate_sem m (Assume b; C) S = {}"
    using assms(2) false_then_empty_later by blast
  have rep_split:
    "sem (Rep (Assume b; C)) S =
      (\<Union>m\<in>{m |m. m < n}. iterate_sem m (Assume b; C) S) \<union>
      iterate_sem n (Assume b; C) S \<union>
      (\<Union>m\<in>{m |m. m > n}. iterate_sem m (Assume b; C) S)"
    using split_union_triple[where n = n and f = "\<lambda>m. iterate_sem m (Assume b; C) S"]
      sem_while[of "Assume b; C" S] by simp
  have after_empty:
    "sem (Assume (lnot b)) (\<Union>m\<in>{m |m. m < n}. iterate_sem m (Assume b; C) S) = {}"
    using assms(1) by (simp add: sem_union_swap sem_assume_low_exp(2))
  have "sem (Rep (Assume b; C)) S =
      (\<Union>m\<in>{m |m. m < n}. iterate_sem m (Assume b; C) S) \<union>
      iterate_sem n (Assume b; C) S"
    using rep_split later_empty by auto
  then have "sem (while_cond b C) S =
      sem (Assume (lnot b))
        ((\<Union>m\<in>{m |m. m < n}. iterate_sem m (Assume b; C) S) \<union>
          iterate_sem n (Assume b; C) S)"
    by (simp add: while_cond_def sem_seq)
  also have "... =
      sem (Assume (lnot b)) (\<Union>m\<in>{m |m. m < n}. iterate_sem m (Assume b; C) S) \<union>
      sem (Assume (lnot b)) (iterate_sem n (Assume b; C) S)"
    by (simp add: sem_union)
  also have "... = sem (Assume (lnot b)) (iterate_sem n (Assume b; C) S)"
    using after_empty by simp
  finally have "sem (while_cond b C) S =
      sem (Assume (lnot b)) (iterate_sem n (Assume b; C) S)" .
  then show ?thesis
    using assms(2) sem_assume_low_exp(1) by blast
qed

lemma while_synchronized_case_2:
  assumes "\<And>m. holds_forall b (iterate_sem m (Assume b; C) S)"
  shows "sem (while_cond b C) S = {}"
proof -
  have "holds_forall b (sem (Rep (Assume b; C)) S)"
    using assms by (auto simp add: sem_while holds_forall_def)
  then show ?thesis
    by (simp add: while_cond_def sem_seq sem_assume_low_exp(2))
qed

theorem while_synchronized:
  assumes "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} C {conj (I (Suc n)) (low_exp b)}"
  shows "\<Turnstile> {conj (I 0) (low_exp b)} while_cond b C
    {conj (disj (exists_nat I) emp) (holds_forall (lnot b))}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume asm0: "conj (I 0) (low_exp b) S"
  have triple: "\<And>n. \<Turnstile> {conj (I n) (holds_forall b)} (Assume b; C)
    {conj (I (Suc n)) (low_exp b)}"
  proof (rule hyper_hoare_tripleI)
    fix n S
    assume "conj (I n) (holds_forall b) S"
    then have "sem (Assume b) S = S"
      by (simp add: conj_def sem_assume_low_exp(1))
    then show "conj (I (Suc n)) (low_exp b) (sem (Assume b; C) S)"
      using hyper_hoare_tripleE[OF assms] \<open>conj (I n) (holds_forall b) S\<close>
      by (simp add: sem_seq)
  qed
  show "conj (disj (exists_nat I) emp) (holds_forall (lnot b)) (sem (while_cond b C) S)"
  proof (cases "\<forall>m. holds_forall b (iterate_sem m (Assume b; C) S)")
    case True
    then have "sem (while_cond b C) S = {}"
      using while_synchronized_case_2[of b C S] by blast
    then show ?thesis
      by (simp add: conj_def disj_def emp_def holds_forall_empty)
  next
    case False
    then have not_all_guard:
      "\<not> (\<forall>m. holds_forall b (iterate_sem m (Assume b; C) S))"
      by simp
    have "\<exists>n. (\<forall>m. m < n \<longrightarrow> holds_forall b (iterate_sem m (Assume b; C) S)) \<and>
      holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
    proof (cases "\<exists>n. \<not> holds_forall b (iterate_sem n (Assume b; C) S) \<and>
        iterate_sem n (Assume b; C) S \<noteq> {}")
      case True
      then obtain n where n_def:
        "\<not> holds_forall b (iterate_sem n (Assume b; C) S)"
        "iterate_sem n (Assume b; C) S \<noteq> {}"
        by blast
      then have false_n: "holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
      proof -
        have "conj (I n) (low_exp b) (iterate_sem n (Assume b; C) S) \<or>
              holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
          by (rule while_synchronized_rec[OF triple asm0])
        with n_def(1) low_exp_two_cases show ?thesis unfolding conj_def by blast
      qed
      have true_before: "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b; C) S)"
      proof (rule ccontr)
        fix m
        assume "m < n" "\<not> holds_forall b (iterate_sem m (Assume b; C) S)"
        then have "holds_forall (lnot b) (iterate_sem m (Assume b; C) S)"
        proof -
          have "conj (I m) (low_exp b) (iterate_sem m (Assume b; C) S) \<or>
                holds_forall (lnot b) (iterate_sem m (Assume b; C) S)"
            by (rule while_synchronized_rec[OF triple asm0])
          with low_exp_two_cases show ?thesis unfolding conj_def by blast
        qed
        then have "iterate_sem n (Assume b; C) S = {}"
          using \<open>m < n\<close> false_then_empty_later by blast
        then show False
          using n_def(2) by simp
      qed
      then show ?thesis
        using false_n by blast
    next
      case False
      then have "\<And>n. holds_forall b (iterate_sem n (Assume b; C) S)"
        using holds_forall_empty by fastforce
      then show ?thesis
        using not_all_guard by blast
    qed
    then obtain n where before: "\<And>m. m < n \<Longrightarrow> holds_forall b (iterate_sem m (Assume b; C) S)"
      and exit: "holds_forall (lnot b) (iterate_sem n (Assume b; C) S)"
      by blast
    have sem_eq: "sem (while_cond b C) S = iterate_sem n (Assume b; C) S"
      using before exit by (rule while_synchronized_case_1)
    have inv_n: "I n (iterate_sem n (Assume b; C) S)"
    proof (cases n)
      case 0
      then show ?thesis
        using asm0 by (simp add: conj_def)
    next
      case (Suc k)
      have rec: "conj (I k) (low_exp b) (iterate_sem k (Assume b; C) S) \<or>
        holds_forall (lnot b) (iterate_sem k (Assume b; C) S)"
        using while_synchronized_rec[OF triple asm0, of k] .
      then show ?thesis
      proof
        assume rec_true: "conj (I k) (low_exp b) (iterate_sem k (Assume b; C) S)"
        have "conj (I k) (holds_forall b) (iterate_sem k (Assume b; C) S)"
          using rec_true before[of k] Suc by (simp add: conj_def)
        then have "conj (I (Suc k)) (low_exp b) (sem (Assume b; C) (iterate_sem k (Assume b; C) S))"
          using triple[of k] hyper_hoare_tripleE by blast
        then have "I (Suc k) (sem (Assume b; C) (iterate_sem k (Assume b; C) S))"
          by (simp add: conj_def)
        then show ?thesis
          using Suc by simp
      next
        assume false_k: "holds_forall (lnot b) (iterate_sem k (Assume b; C) S)"
        then have "iterate_sem n (Assume b; C) S = {}"
          using Suc false_then_empty_later by blast
        have "\<And>m. holds_forall b (iterate_sem m (Assume b; C) S)"
        proof -
          fix m
          show "holds_forall b (iterate_sem m (Assume b; C) S)"
          proof (cases "m < n")
            case True
            then show ?thesis
              using before by blast
          next
            case False
            then consider "m = n" | "m > n"
              by linarith
            then show ?thesis
            proof cases
              case 1
              then show ?thesis
                using \<open>iterate_sem n (Assume b; C) S = {}\<close> holds_forall_empty by simp
            next
              case 2
              then have "iterate_sem m (Assume b; C) S = {}"
                using exit false_then_empty_later by blast
              then show ?thesis
                by (simp add: holds_forall_empty)
            qed
          qed
        qed
        then show ?thesis
          using not_all_guard by blast
      qed
    qed
    then show ?thesis
      unfolding conj_def disj_def exists_nat_def using sem_eq exit inv_n by simp
  qed
qed

theorem WhileSync_simpler:
  assumes "\<Turnstile> {conj I (holds_forall b)} C {conj I (low_exp b)}"
  shows "\<Turnstile> {conj I (low_exp b)} while_cond b C
    {conj (disj I emp) (holds_forall (lnot b))}"
  using assms while_synchronized[of "\<lambda>n. I" b C]
  by (simp add: disj_def exists_nat_def conj_def hyper_hoare_triple_def)

end
