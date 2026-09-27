theory PhaseG_GNI_witness
  imports PhaseG_GNI_hybrid
begin

(* Verified F2 three-run solution surgery for decoupled ODE fields.
   The witness p3 combines the H-components of p1 and L-components of p2. *)

section \<open>F2, three-run version: witness surgery for decoupled ODEs\<close>

text \<open>
For GNI's \<^bold>\<open>\<forall>\<forall>\<exists>\<close> shape one must, given runs 1 and 2, produce a THIRD
solution carrying run 1's high inputs and run 2's low trajectory.  For a
field whose variables decompose into disjoint low/high blocks with
block-local dynamics (\<open>decoupled\<close>), the surgery \<open>p3 := H-parts of p1,
L-parts of p2\<close> is again a solution, solves the same exit guard whenever the
guard is low, and coincides with \<open>p2\<close> on all low variables throughout --
exactly the GNI witness obligation for continuous evolution.\<close>

definition decoupled :: "var set \<Rightarrow> var set \<Rightarrow> (var \<Rightarrow> state \<Rightarrow> real) \<Rightarrow> bool" where
  "decoupled L H f \<longleftrightarrow>
     L \<inter> H = {} \<and> L \<union> H = UNIV \<and>
     (\<forall>x\<in>L. \<forall>s s'. (\<forall>y\<in>L. s y = s' y) \<longrightarrow> f x s = f x s') \<and>
     (\<forall>x\<in>H. \<forall>s s'. (\<forall>y\<in>H. s y = s' y) \<longrightarrow> f x s = f x s')"

definition surgery :: "var set \<Rightarrow> var set \<Rightarrow> (real \<Rightarrow> state) \<Rightarrow> (real \<Rightarrow> state)
    \<Rightarrow> real \<Rightarrow> state" where
  "surgery L H p1 p2 t x = (if x \<in> H then p1 t x else p2 t x)"

lemma decoupled_disjoint [simp]: "decoupled L H f \<Longrightarrow> x \<in> L \<Longrightarrow> x \<notin> H"
  by (auto simp: decoupled_def)

lemma surgery_L [simp]: "y \<in> L \<Longrightarrow> decoupled L H f \<Longrightarrow>
    surgery L H p1 p2 t y = p2 t y"
  by (simp add: surgery_def decoupled_disjoint)

lemma surgery_H [simp]: "y \<in> H \<Longrightarrow> surgery L H p1 p2 t y = p1 t y"
  by (simp add: surgery_def)

lemma decoupled_agree_L:
  assumes dec: "decoupled L H f"
  shows "\<forall>y\<in>L. surgery L H p1 p2 t y = p2 t y"
  using dec by (auto simp: surgery_L)

lemma decoupled_agree_H:
  assumes dec: "decoupled L H f"
  shows "\<forall>y\<in>H. surgery L H p1 p2 t y = p1 t y"
  using dec by (auto simp: surgery_H)

lemma decoupled_cover:
  assumes "decoupled L H f"
  shows "L \<union> H = UNIV"
  using assms unfolding decoupled_def by blast

lemma decoupled_field_L:
  assumes dec: "decoupled L H f" and xL: "x \<in> L"
    and agree: "\<forall>y\<in>L. s y = s' y"
  shows "f x s = f x s'"
  using assms unfolding decoupled_def by blast

lemma decoupled_field_H:
  assumes dec: "decoupled L H f" and xH: "x \<in> H"
    and agree: "\<forall>y\<in>H. s y = s' y"
  shows "f x s = f x s'"
  using assms unfolding decoupled_def by blast

lemma surgery_0:
  "surgery L H p1 p2 0 x = (if x \<in> H then p1 0 x else p2 0 x)"
  by (simp add: surgery_def)

lemma ODEsol_component_ext:
  assumes sol: "ODEsol (ODE f) p d"
  obtains e where "e > 0"
    and "\<And>x. ((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {-e..d+e}"
proof -
  from sol [unfolded ODEsol_def] obtain e where e: "e > 0"
    "((\<lambda>t. state2vec (p t)) has_vderiv_on (\<lambda>t. ODE2Vec (ODE f) (p t))) {-e..d+e}"
    by blast
  have c: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on (\<lambda>t. f x (p t))) {-e..d+e}"
    using has_vderiv_on_proj [OF e(2)] by (simp add: state2vec_def)
  from e(1) c that show ?thesis by blast
qed

theorem surgery_decoupled:
  assumes dec: "decoupled L H f"
      and sol1: "ODEsol (ODE f) p1 d" and sol2: "ODEsol (ODE f) p2 d"
  shows "ODEsol (ODE f) (surgery L H p1 p2) d"
    and "\<And>t x. x \<in> L \<Longrightarrow> surgery L H p1 p2 t x = p2 t x"
    and "\<And>t x. x \<in> H \<Longrightarrow> surgery L H p1 p2 t x = p1 t x"
proof -
  have cover: "L \<union> H = UNIV" by (rule decoupled_cover[OF dec])
  show loweq: "\<And>t x. x \<in> L \<Longrightarrow> surgery L H p1 p2 t x = p2 t x"
    using dec by (simp add: surgery_L)
  show higheq: "\<And>t x. x \<in> H \<Longrightarrow> surgery L H p1 p2 t x = p1 t x"
    by (simp add: surgery_def)
  from sol1 obtain e1 where e1: "e1 > 0"
    and c1: "\<And>x. ((\<lambda>t. p1 t x) has_vderiv_on (\<lambda>t. f x (p1 t))) {-e1..d+e1}"
    using ODEsol_component_ext by blast
  from sol2 obtain e2 where e2: "e2 > 0"
    and c2: "\<And>x. ((\<lambda>t. p2 t x) has_vderiv_on (\<lambda>t. f x (p2 t))) {-e2..d+e2}"
    using ODEsol_component_ext by blast
  define e where "e = min e1 e2"
  have ep: "e > 0" using e1 e2 by (simp add: e_def)
  have sub1: "{-e..d+e} \<subseteq> {-e1..d+e1}" by (auto simp: e_def)
  have sub2: "{-e..d+e} \<subseteq> {-e2..d+e2}" by (auto simp: e_def)
  have comp: "\<And>x. ((\<lambda>t. surgery L H p1 p2 t x) has_vderiv_on
      (\<lambda>t. f x (surgery L H p1 p2 t))) {-e..d+e}"
  proof -
    fix x
    have xc: "x \<in> L \<or> x \<in> H" using cover by blast
    then show "((\<lambda>t. surgery L H p1 p2 t x) has_vderiv_on
      (\<lambda>t. f x (surgery L H p1 p2 t))) {-e..d+e}"
    proof (elim disjE)
      assume xL: "x \<in> L"
      have fr: "(\<lambda>t. surgery L H p1 p2 t x) = (\<lambda>t. p2 t x)"
        by (rule ext) (simp add: loweq xL)
      have gr: "(\<lambda>t. f x (surgery L H p1 p2 t)) = (\<lambda>t. f x (p2 t))"
      proof (rule ext)
        fix t
        have agree: "\<forall>y\<in>L. surgery L H p1 p2 t y = p2 t y"
          by (rule decoupled_agree_L[OF dec])
        show "f x (surgery L H p1 p2 t) = f x (p2 t)"
          by (rule decoupled_field_L[OF dec xL agree])
      qed
      have base: "((\<lambda>t. p2 t x) has_vderiv_on (\<lambda>t. f x (p2 t))) {-e..d+e}"
        by (rule has_vderiv_on_subset [OF c2 [of x] sub2])
      show ?thesis unfolding fr gr by (rule base)
    next
      assume xH: "x \<in> H"
      have fr: "(\<lambda>t. surgery L H p1 p2 t x) = (\<lambda>t. p1 t x)"
        by (rule ext) (simp add: higheq xH)
      have gr: "(\<lambda>t. f x (surgery L H p1 p2 t)) = (\<lambda>t. f x (p1 t))"
      proof (rule ext)
        fix t
        have agree: "\<forall>y\<in>H. surgery L H p1 p2 t y = p1 t y"
          by (rule decoupled_agree_H[OF dec])
        show "f x (surgery L H p1 p2 t) = f x (p1 t)"
          by (rule decoupled_field_H[OF dec xH agree])
      qed
      have base: "((\<lambda>t. p1 t x) has_vderiv_on (\<lambda>t. f x (p1 t))) {-e..d+e}"
        by (rule has_vderiv_on_subset [OF c1 [of x] sub1])
      show ?thesis unfolding fr gr by (rule base)
    qed
  qed
  have d0: "0 \<le> d" using sol1 unfolding ODEsol_def by simp
  show "ODEsol (ODE f) (surgery L H p1 p2) d"
    by (rule ODEsol_from_components[OF d0 ep comp])
qed

lemma surgery_low_wait_obs:
  assumes dec: "decoupled L H f" and low: "l \<in> L"
  shows "obs_block_c l (WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})) =
    obs_block_c l (WaitBlk d (\<lambda>t. State (p2 t)) ({}, {}))"
proof -
  have curve: "low_curve l (\<lambda>t\<in>{0..d}. State (surgery L H p1 p2 t)) =
      low_curve l (\<lambda>t\<in>{0..d}. State (p2 t))"
    using dec low by (rule_tac ext) (simp add: low_curve_def surgery_L)
  show ?thesis by (simp add: obs_block_c_def WaitBlk_def curve)
qed

theorem cont_witness_decoupled:
  assumes dec: "decoupled L H f"
    and sol1: "ODEsol (ODE f) p1 d" and sol2: "ODEsol (ODE f) p2 d"
    and pos: "0 < d"
    and guard_low: "\<And>s s'. (\<forall>x\<in>L. s x = s' x) \<Longrightarrow> b s = b s'"
    and inside2: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p2 t)"
    and exit2: "\<not> b (p2 d)"
  shows "big_step (Cont (ODE f) b) (surgery L H p1 p2 0)
      [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})]
      (surgery L H p1 p2 d)"
proof -
  have sol3: "ODEsol (ODE f) (surgery L H p1 p2) d"
    by (rule surgery_decoupled(1)[OF dec sol1 sol2])
  have guard_eq: "\<And>t. b (surgery L H p1 p2 t) = b (p2 t)"
  proof -
    fix t
    have agree: "\<forall>x\<in>L. surgery L H p1 p2 t x = p2 t x"
      by (rule decoupled_agree_L[OF dec])
    show "b (surgery L H p1 p2 t) = b (p2 t)"
      by (rule guard_low[OF agree])
  qed
  have inside3: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (surgery L H p1 p2 t)"
    using inside2 guard_eq by simp
  have exit3: "\<not> b (surgery L H p1 p2 d)" using exit2 guard_eq by simp
  show ?thesis by (rule ContB2[OF pos sol3 inside3 exit3 refl])
qed

theorem cont_witness_in_sem_decoupled:
  fixes S :: "(('lvar, 'lval) exstate) set"
  assumes dec: "decoupled L H f"
    and sol1: "ODEsol (ODE f) p1 d" and sol2: "ODEsol (ODE f) p2 d"
    and pos: "0 < d"
    and guard_low: "\<And>s s'. (\<forall>x\<in>L. s x = s' x) \<Longrightarrow> b s = b s'"
    and inside2: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p2 t)"
    and exit2: "\<not> b (p2 d)"
    and source: "(sl, surgery L H p1 p2 0, tr) \<in> S"
    and low: "l \<in> L"
  shows "(sl, surgery L H p1 p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})])
      \<in> sem (Cont (ODE f) b) S"
    and "low_obs_c l (sl, surgery L H p1 p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})]) =
      low_obs_c l (sl2, p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (p2 t)) ({}, {})])"
proof -
  have step: "big_step (Cont (ODE f) b) (surgery L H p1 p2 0)
      [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})]
      (surgery L H p1 p2 d)"
    by (rule cont_witness_decoupled[OF dec sol1 sol2 pos guard_low inside2 exit2])
  show "(sl, surgery L H p1 p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})])
      \<in> sem (Cont (ODE f) b) S"
    using source step by (auto simp: in_sem)
  have low_value: "surgery L H p1 p2 d l = p2 d l"
    by (rule surgery_L[OF low dec])
  have low_wait: "obs_block_c l (WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})) =
      obs_block_c l (WaitBlk d (\<lambda>t. State (p2 t)) ({}, {}))"
    by (rule surgery_low_wait_obs[OF dec low])
  show "low_obs_c l (sl, surgery L H p1 p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})]) =
      low_obs_c l (sl2, p2 d,
      tr @ [WaitBlk d (\<lambda>t. State (p2 t)) ({}, {})])"
    by (simp add: low_obs_c_def pproj_def tproj_def obs_tr_c_def low_value low_wait)
qed


subsection \<open>Complete set-level GNI for decoupled, constant-low dynamics\<close>

text \<open>
Final mile of the F2 three-run programme: a closed \<^const>\<open>gni_obs_c\<close>
theorem for a single \<open>Cont\<close>.  The witness for a pair of runs is the
surgery run of \<^theory_text>\<open>cont_witness_in_sem_decoupled\<close>; the common
duration and the common low trajectory come from the low block having
constant dynamics (\<open>low_const_field\<close>, covering clocks and
constant-velocity low variables), which makes every run's low components
equal to \<open>c x + k x \<cdot> t\<close> and the low exit guard a single function
of time.\<close>

definition low_const_field :: "var set \<Rightarrow> (var \<Rightarrow> state \<Rightarrow> real) \<Rightarrow> bool" where
  "low_const_field L f \<longleftrightarrow> (\<forall>x\<in>L. \<exists>k. \<forall>s. f x s = k)"

lemma sem_cont_disj:
  assumes m: "\<phi> \<in> sem (Cont (ODE f) b) S"
  shows "(\<exists>a bb tt. (a, bb, tt) \<in> S \<and> \<not> b bb \<and> \<phi> = (a, bb, tt))
     \<or> (\<exists>a bb tt p d. (a, bb, tt) \<in> S \<and> 0 < d \<and> ODEsol (ODE f) p d
          \<and> (\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t)) \<and> \<not> b (p d) \<and> p 0 = bb
          \<and> \<phi> = (a, p d, tt @ [WaitBlk d (\<lambda>t. State (p t)) ({}, {})]))"
proof -
  obtain a bb tt where pd: "\<phi> = (a, bb, tt)" by (metis prod.exhaust)
  from m pd have mem: "(a, bb, tt) \<in> sem (Cont (ODE f) b) S" by simp
  from mem [unfolded sem_ode] pd show ?thesis by blast
qed

lemma sem_cont_instE:
  assumes m: "\<phi> \<in> sem (Cont (ODE f) b) S"
      and nb: "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> \<not> b bb"
  obtains a bb tt where "(a, bb, tt) \<in> S" "\<phi> = (a, bb, tt)"
proof -
  from sem_cont_disj [OF m] show ?thesis
  proof (elim disjE exE conjE)
    fix a0 b0 t0
    assume s0: "(a0, b0, t0) \<in> S" and nb0: "\<not> b b0" and sh0: "\<phi> = (a0, b0, t0)"
    from s0 sh0 show ?thesis by (rule that)
  next
    fix a0 b0 t0 p d0
    assume src: "(a0, b0, t0) \<in> S" and pos: "0 < d0"
      and ins: "\<forall>t. 0 \<le> t \<and> t < d0 \<longrightarrow> b (p t)" and p0: "p 0 = b0"
      and "\<phi> = (a0, p d0, t0 @ [WaitBlk d0 (\<lambda>t. State (p t)) ({}, {})])"
    have "b b0" using ins [rule_format, of 0] pos p0 by simp
    with nb src show ?thesis by blast
  qed
qed

lemma sem_cont_waitE:
  assumes m: "\<phi> \<in> sem (Cont (ODE f) b) S"
      and ab: "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> b bb"
  obtains a bb tt p d where "(a, bb, tt) \<in> S" "0 < d" "ODEsol (ODE f) p d"
    "(\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (p t))" "\<not> b (p d)" "p 0 = bb"
    "\<phi> = (a, p d, tt @ [WaitBlk d (\<lambda>t. State (p t)) ({}, {})])"
proof -
  from sem_cont_disj [OF m] show ?thesis
  proof (elim disjE exE conjE)
    fix a0 b0 t0
    assume src: "(a0, b0, t0) \<in> S" and nb0: "\<not> b b0" and "\<phi> = (a0, b0, t0)"
    have "b b0" using ab src by blast
    with nb0 show ?thesis by blast
  next
    fix a0 b0 t0 p d0
    assume "(a0, b0, t0) \<in> S" "0 < d0" "ODEsol (ODE f) p d0"
      "\<forall>t. 0 \<le> t \<and> t < d0 \<longrightarrow> b (p t)" "\<not> b (p d0)" "p 0 = b0"
      "\<phi> = (a0, p d0, t0 @ [WaitBlk d0 (\<lambda>t. State (p t)) ({}, {})])"
    then show ?thesis by (rule that)
  qed
qed

theorem cont_gni_obs_decoupled_set:
  assumes dec: "decoupled L H f"
      and lowf: "low_const_field L f"
      and guard_low: "\<And>s s'. (\<forall>x\<in>L. s x = s' x) \<Longrightarrow> b s = b s'"
      and lL: "LL2 \<in> L"
      and Lconst: "\<And>\<phi> x. \<phi> \<in> S \<Longrightarrow> x \<in> L \<Longrightarrow> pproj \<phi> x = c x"
      and tconst: "t_const_at tr S"
      and cross: "\<And>l1 q1 l2 q2. (l1, q1, tr) \<in> S \<Longrightarrow> (l2, q2, tr) \<in> S \<Longrightarrow>
        (l1, \<lambda>x. if x \<in> H then q1 x else q2 x, tr) \<in> S"
  shows "gni_obs_c HI LO LL2 (sem (Cont (ODE f) b) (S :: ((char, real) exstate) set))"
proof -
  define k where "k = (\<lambda>x. SOME kk. \<forall>s. f x s = kk)"
  have kI: "\<And>x s. x \<in> L \<Longrightarrow> f x s = k x"
  proof -
    fix x s assume xL: "x \<in> L"
    from lowf [unfolded low_const_field_def, rule_format, OF xL]
    have ex: "\<exists>kk. \<forall>s. f x s = kk" .
    from ex have allk: "\<forall>s. f x s = (SOME kk. \<forall>s. f x s = kk)"
      by (rule someI_ex)
    then show "f x s = k x" unfolding k_def by simp
  qed
  have lowtraj: "\<And>p d t x. ODEsol (ODE f) p d \<Longrightarrow> t \<in> {0..d} \<Longrightarrow> x \<in> L \<Longrightarrow>
      p t x = p 0 x + k x * t"
  proof -
    fix p d t x assume sol: "ODEsol (ODE f) p d" and td: "t \<in> {0..d}" and xL: "x \<in> L"
    have rate: "\<And>s. f x s = k x" using kI xL by simp
    from ODEsol_component_affine [OF sol rate td]
    show "p t x = p 0 x + k x * t" by simp
  qed
  have bunif: "\<And>q1 q2 l1 l2 t1 t2. (l1, q1, t1) \<in> S \<Longrightarrow> (l2, q2, t2) \<in> S \<Longrightarrow> b q1 = b q2"
  proof -
    fix q1 q2 l1 l2 t1 t2
    assume s1: "(l1, q1, t1) \<in> S" and s2: "(l2, q2, t2) \<in> S"
    show "b q1 = b q2"
    proof (rule guard_low)
      show "\<forall>x\<in>L. q1 x = q2 x"
      proof
        fix x assume xL: "x \<in> L"
        have e1: "pproj (l1, q1, t1) x = c x" using Lconst s1 xL by simp
        have e2: "pproj (l2, q2, t2) x = c x" using Lconst s2 xL by simp
        from e1 e2 show "q1 x = q2 x" by (simp add: pproj_def)
      qed
    qed
  qed
  show ?thesis
  proof (unfold gni_obs_c_def, rule ballI, rule ballI, rule impI)
    fix \<phi>1 \<phi>2
    assume m1: "\<phi>1 \<in> sem (Cont (ODE f) b) S"
       and m2: "\<phi>2 \<in> sem (Cont (ODE f) b) S"
       and loeq: "lproj \<phi>1 LO = lproj \<phi>2 LO"
    have unif: "(\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> \<not> b bb)
             \<or> (\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> b bb)"
    proof (cases "\<exists>\<phi>0. \<phi>0 \<in> S")
      case False
      then show ?thesis by auto
    next
      case True
      then obtain \<phi>0 where "\<phi>0 \<in> S" by blast
      then obtain a0 b0 t0 where mem0: "(a0, b0, t0) \<in> S"
        by (metis prod.exhaust)
      show ?thesis
      proof (cases "b b0")
        case True
        have ballb: "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> b bb"
        proof (intro allI impI)
          fix a bb tt assume src: "(a, bb, tt) \<in> S"
          then show "b bb" using bunif [OF src mem0] True by simp
        qed
        then show ?thesis by blast
      next
        case False
        have ballnb: "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> \<not> b bb"
        proof (intro allI impI)
          fix a bb tt assume src: "(a, bb, tt) \<in> S"
          then show "\<not> b bb" using bunif [OF src mem0] False by simp
        qed
        then show ?thesis by blast
      qed
    qed
    show "\<exists>\<phi>3 \<in> sem (Cont (ODE f) b) S. lproj \<phi>3 HI = lproj \<phi>1 HI
          \<and> lproj \<phi>3 LO = lproj \<phi>2 LO
          \<and> low_obs_c LL2 \<phi>3 = low_obs_c LL2 \<phi>2"
    proof (cases "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> \<not> b bb")
      case True
      from sem_cont_instE [OF m1 True] obtain a1 b1 t1 where
        s1: "(a1, b1, t1) \<in> S" "\<phi>1 = (a1, b1, t1)" by blast
      from sem_cont_instE [OF m2 True] obtain a2 b2 t2 where
        s2: "(a2, b2, t2) \<in> S" "\<phi>2 = (a2, b2, t2)" by blast
      have "tproj (a1, b1, t1) = tr"
        using tconst [unfolded t_const_at_def, rule_format, OF s1(1)] .
      then have t1tr: "t1 = tr" by (simp add: tproj_def)
      have "tproj (a2, b2, t2) = tr"
        using tconst [unfolded t_const_at_def, rule_format, OF s2(1)] .
      then have t2tr: "t2 = tr" by (simp add: tproj_def)
      have b1L: "b1 LL2 = c LL2" using Lconst [OF s1(1) lL] by (simp add: pproj_def)
      have b2L: "b2 LL2 = c LL2" using Lconst [OF s2(1) lL] by (simp add: pproj_def)
      have obs1: "low_obs_c LL2 \<phi>1 = (c LL2, obs_tr_c LL2 tr)"
        by (simp add: s1(2) t1tr low_obs_c_def pproj_def tproj_def b1L)
      have obs2: "low_obs_c LL2 \<phi>2 = (c LL2, obs_tr_c LL2 tr)"
        by (simp add: s2(2) t2tr low_obs_c_def pproj_def tproj_def b2L)
      show ?thesis
        by (rule_tac x = "\<phi>1" in bexI, simp add: obs1 obs2 loeq, rule m1)
    next
      case False
      from unif False have allb: "\<forall>a bb tt. (a, bb, tt) \<in> S \<longrightarrow> b bb" by blast
      from sem_cont_waitE [OF m1 allb] obtain a1 b1 t1 p1 d1 where
        st1: "(a1, b1, t1) \<in> S" "0 < d1" "ODEsol (ODE f) p1 d1"
          "(\<forall>t. 0 \<le> t \<and> t < d1 \<longrightarrow> b (p1 t))" "\<not> b (p1 d1)" "p1 0 = b1"
          "\<phi>1 = (a1, p1 d1, t1 @ [WaitBlk d1 (\<lambda>t. State (p1 t)) ({}, {})])" by blast
      from sem_cont_waitE [OF m2 allb] obtain a2 b2 t2 p2 d2 where
        st2: "(a2, b2, t2) \<in> S" "0 < d2" "ODEsol (ODE f) p2 d2"
          "(\<forall>t. 0 \<le> t \<and> t < d2 \<longrightarrow> b (p2 t))" "\<not> b (p2 d2)" "p2 0 = b2"
          "\<phi>2 = (a2, p2 d2, t2 @ [WaitBlk d2 (\<lambda>t. State (p2 t)) ({}, {})])" by blast
      have "tproj (a1, b1, t1) = tr"
        using tconst [unfolded t_const_at_def, rule_format, OF st1(1)] .
      then have t1tr: "t1 = tr" by (simp add: tproj_def)
      have "tproj (a2, b2, t2) = tr"
        using tconst [unfolded t_const_at_def, rule_format, OF st2(1)] .
      then have t2tr: "t2 = tr" by (simp add: tproj_def)
      have d12: "d1 = d2"
      proof (rule ccontr)
        assume ne: "d1 \<noteq> d2"
        then have lt: "d1 < d2 \<or> d2 < d1" by auto
        then show False
        proof
          assume lt12: "d1 < d2"
          have beq: "b (p1 d1) = b (p2 d1)"
          proof (rule guard_low)
            show "\<forall>x\<in>L. p1 d1 x = p2 d1 x"
            proof
              fix x assume xL: "x \<in> L"
              have e1: "p1 d1 x = c x + k x * d1"
              proof -
                have "p1 d1 x = p1 0 x + k x * d1"
                  using lowtraj [OF st1(3) _ xL] by (metis atLeastAtMost_iff)
                also have "p1 0 x = c x"
                  using st1(6) Lconst [OF st1(1) xL] by (simp add: pproj_def)
                finally show "p1 d1 x = c x + k x * d1" .
              qed
              have e2: "p2 d1 x = c x + k x * d1"
              proof -
                have "d1 \<in> {0..d2}" using lt12 by auto
                then have "p2 d1 x = p2 0 x + k x * d1"
                  using lowtraj [OF st2(3) _ xL] by blast
                also have "p2 0 x = c x"
                  using st2(6) Lconst [OF st2(1) xL] by (simp add: pproj_def)
                finally show "p2 d1 x = c x + k x * d1" .
              qed
              from e1 e2 show "p1 d1 x = p2 d1 x" by simp
            qed
          qed
          have "b (p2 d1)" using st2(4) [rule_format, of d1] lt12 by simp
          with beq st1(5) show False by simp
        next
          assume lt21: "d2 < d1"
          have beq: "b (p1 d2) = b (p2 d2)"
          proof (rule guard_low)
            show "\<forall>x\<in>L. p1 d2 x = p2 d2 x"
            proof
              fix x assume xL: "x \<in> L"
              have e1: "p1 d2 x = c x + k x * d2"
              proof -
                have "d2 \<in> {0..d1}" using lt21 by auto
                then have "p1 d2 x = p1 0 x + k x * d2"
                  using lowtraj [OF st1(3) _ xL] by blast
                also have "p1 0 x = c x"
                  using st1(6) Lconst [OF st1(1) xL] by (simp add: pproj_def)
                finally show "p1 d2 x = c x + k x * d2" .
              qed
              have e2: "p2 d2 x = c x + k x * d2"
              proof -
                have "p2 d2 x = p2 0 x + k x * d2"
                  using lowtraj [OF st2(3) _ xL] by (metis atLeastAtMost_iff)
                also have "p2 0 x = c x"
                  using st2(6) Lconst [OF st2(1) xL] by (simp add: pproj_def)
                finally show "p2 d2 x = c x + k x * d2" .
              qed
              from e1 e2 show "p1 d2 x = p2 d2 x" by simp
            qed
          qed
          have "b (p1 d2)" using st1(4) [rule_format, of d2] lt21 by simp
          with beq st2(5) show False by simp
        qed
      qed
      have s1r: "(a1, b1, tr) \<in> S" using st1(1) t1tr by simp
      have s2r: "(a2, b2, tr) \<in> S" using st2(1) t2tr by simp
      have src3: "(a1, \<lambda>x. if x \<in> H then b1 x else b2 x, tr) \<in> S"
        by (rule cross [OF s1r s2r])
      have surg0: "surgery L H p1 p2 0 = (\<lambda>x. if x \<in> H then b1 x else b2 x)"
        by (rule ext) (simp add: surgery_0 st1(6) st2(6))
      have surg_src: "(a1, surgery L H p1 p2 0, tr) \<in> S"
        using surg0 src3 by simp
      have sol1d2: "ODEsol (ODE f) p1 d2" using st1(3) d12 by simp
      note wit = cont_witness_in_sem_decoupled
        [OF dec sol1d2 st2(3) st2(2) guard_low st2(4) st2(5) surg_src lL]
      obtain wmem wobs where
        wmem: "(a1, surgery L H p1 p2 d2,
               tr @ [WaitBlk d2 (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})])
               \<in> sem (Cont (ODE f) b) S"
        and wobs: "low_obs_c LL2 (a1, surgery L H p1 p2 d2,
               tr @ [WaitBlk d2 (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {})]) =
             low_obs_c LL2 (a2, p2 d2, tr @ [WaitBlk d2 (\<lambda>t. State (p2 t)) ({}, {})])"
        using wit by blast
      show ?thesis
        by (rule_tac x = "(a1, surgery L H p1 p2 d2,
               tr @ [WaitBlk d2 (\<lambda>t. State (surgery L H p1 p2 t)) ({}, {}))]" in bexI,
            simp add: st1(7) st2(7) t1tr t2tr loeq lproj_def wobs, rule wmem)
    qed
  qed
qed

end
