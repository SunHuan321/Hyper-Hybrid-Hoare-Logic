theory PhaseG_Concrete_Scale
  imports PhaseG_Parallel_Scale
begin

section \<open>The unbounded mass-sensitive parallel lander\<close>

definition Plant0 :: proc where
  "Plant0 = Interrupt (ODE lander_mass_field) (\<lambda>s. 0 < s M)
    [(''p2c''[!](\<lambda>s. s V),
      Cm (''p2c''[!](\<lambda>s. s W));
      Cm (''m2c''[!](\<lambda>s. s M));
      Cm (''c2p''[?]W);
      Fc ::= (\<lambda>s. s M * s W))]"

definition Ctrl0 :: proc where
  "Ctrl0 = Wait (\<lambda>_. Period);
    Cm (''p2c''[?]V);
    Cm (''p2c''[?]W);
    Cm (''m2c''[?]M);
    Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
    Cm (''c2p''[!](\<lambda>s. s Fc / s M))"

definition Lander0 :: pproc where
  "Lander0 = Parallel (Single (Rep Plant0))
    {''p2c'', ''m2c'', ''c2p''} (Single (Rep Ctrl0))"

subsection \<open>Plant ODE scaling\<close>

lemma mass_scale_rate_field:
  assumes nz: "k \<noteq> 0"
  shows "lander_mass_field x (mass_scale k s) =
    (if x = M \<or> x = Fc then k * lander_mass_field x s
     else lander_mass_field x s)"
proof (cases "x = M")
  case True
  then show ?thesis by simp
next
  case m: False
  show ?thesis
  proof (cases "x = Fc")
    case True
    with m show ?thesis by simp
  next
    case f: False
    show ?thesis
    proof (cases "x = V")
      case True
      with m f nz show ?thesis by simp
    next
      case v: False
      show ?thesis
      proof (cases "x = W")
        case True
        with m f v show ?thesis by simp
      next
        case w: False
        with m f v w show ?thesis by simp
      qed
    qed
  qed
qed

theorem mass_scale_plant_ODEsol:
  assumes pos: "0 < k" and sol: "ODEsol (ODE lander_mass_field) p d"
  shows "ODEsol (ODE lander_mass_field) (\<lambda>t. mass_scale k (p t)) d"
proof -
  have nz: "k \<noteq> 0" using pos by simp
  from ODEsol_component_ext[OF sol] obtain e where e: "0 < e"
    and comp: "\<And>x. ((\<lambda>t. p t x) has_vderiv_on
      (\<lambda>t. lander_mass_field x (p t))) {-e..d+e}" by blast
  have d0: "0 \<le> d" using sol unfolding ODEsol_def by simp
  show ?thesis
  proof (rule ODEsol_from_components[OF d0 e])
    fix x
    show "((\<lambda>t. mass_scale k (p t) x) has_vderiv_on
      (\<lambda>t. lander_mass_field x (mass_scale k (p t)))) {-e..d+e}"
    proof (cases "x = M \<or> x = Fc")
      case True
      have der: "((\<lambda>t. k * p t x) has_vderiv_on
        (\<lambda>t. k * lander_mass_field x (p t))) {-e..d+e}"
        by (rule has_vderiv_on_scale_const[OF comp[of x]])
      have feq: "(\<lambda>t. mass_scale k (p t) x) = (\<lambda>t. k * p t x)"
        by (rule ext) (rule mass_scale_selected[OF True])
      have req: "(\<lambda>t. lander_mass_field x (mass_scale k (p t))) =
          (\<lambda>t. k * lander_mass_field x (p t))"
        by (rule ext) (simp add: mass_scale_rate_field[OF nz] True)
      show ?thesis unfolding feq req by (rule der)
    next
      case False
      have xM: "x \<noteq> M" and xF: "x \<noteq> Fc" using False by auto
      have feq: "(\<lambda>t. mass_scale k (p t) x) = (\<lambda>t. p t x)"
        by (rule ext) (simp add: xM xF)
      have req: "(\<lambda>t. lander_mass_field x (mass_scale k (p t))) =
          (\<lambda>t. lander_mass_field x (p t))"
        by (rule ext) (simp add: mass_scale_rate_field[OF nz] False)
      show ?thesis unfolding feq req by (rule comp[of x])
    qed
  qed
qed

subsection \<open>Syntax-directed scaling certificates\<close>

definition scale_ok :: "real \<Rightarrow> proc \<Rightarrow> bool" where
  "scale_ok k C \<longleftrightarrow> (\<forall>s tr s'. big_step C s tr s'
     \<longrightarrow> big_step C (mass_scale k s) (scale_trace k tr)
       (mass_scale k s'))"

lemma scale_trace_append [simp]:
  "scale_trace k (a @ b) = scale_trace k a @ scale_trace k b"
  unfolding scale_trace_def by simp

lemma scale_ok_skip: "scale_ok k Skip"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step Skip s tr s'"
  from run have tr: "tr = []" and s': "s' = s"
    by (auto elim: skipE)
  have b: "big_step Skip (mass_scale k s) [] (mass_scale k s)"
    by (rule skipB)
  show "big_step Skip (mass_scale k s) (scale_trace k tr) (mass_scale k s')"
    using b tr s' by simp
qed

lemma scale_ok_assign:
  assumes eq: "\<And>s. mass_scale k (s(x := e s)) =
    (mass_scale k s)(x := e (mass_scale k s))"
  shows "scale_ok k (x ::= e)"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (x ::= e) s tr s'"
  from run have tr: "tr = []" and s': "s' = s(x := e s)"
    by (auto elim: assignE)
  have b: "big_step (x ::= e) (mass_scale k s) []
    ((mass_scale k s)(x := e (mass_scale k s)))"
    by (rule assignB)
  show "big_step (x ::= e) (mass_scale k s) (scale_trace k tr)
    (mass_scale k s')"
    using b tr s' eq[of s] by simp
qed

lemma scale_ok_send:
  assumes eq: "\<And>s. e (mass_scale k s) = scale_comm_value k ch (e s)"
  shows "scale_ok k (Cm (ch[!]e))"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (Cm (ch[!]e)) s tr s'"
  from run have cases:
    "(tr = [OutBlock ch (e s)] \<and> s' = s) \<or>
     (\<exists>d>0. tr = [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
       OutBlock ch (e s)] \<and> s' = s)"
    by (auto elim: sendE)
  from cases show "big_step (Cm (ch[!]e)) (mass_scale k s) (scale_trace k tr)
    (mass_scale k s')"
  proof (elim disjE)
    assume z: "tr = [OutBlock ch (e s)] \<and> s' = s"
    have b: "big_step (Cm (ch[!]e)) (mass_scale k s)
      [OutBlock ch (e (mass_scale k s))] (mass_scale k s)"
      by (rule sendB1)
    show ?thesis using z b eq[of s]
      by (simp add: scale_trace_def)
  next
    assume w: "\<exists>d>0. tr = [WaitBlk d (\<lambda>_. State s) ({ch}, {}),
       OutBlock ch (e s)] \<and> s' = s"
    from w obtain d where dp: "0 < d"
      and tr: "tr = [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)]"
      and s': "s' = s" by blast
    have b: "big_step (Cm (ch[!]e)) (mass_scale k s)
      [WaitBlk d (\<lambda>_. State (mass_scale k s)) ({ch}, {}),
       OutBlock ch (e (mass_scale k s))] (mass_scale k s)"
      by (rule sendB2[OF dp])
    show ?thesis using b eq[of s] tr s'
      by (simp add: scale_trace_def scale_block_WaitBlk)
  qed
qed

lemma scale_ok_receive:
  assumes eq: "\<And>s v. mass_scale k (s(x := v)) =
    (mass_scale k s)(x := scale_comm_value k ch v)"
  shows "scale_ok k (Cm (ch[?]x))"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (Cm (ch[?]x)) s tr s'"
  from run have cases:
    "(\<exists>v. tr = [InBlock ch v] \<and> s' = s(x := v)) \<or>
     (\<exists>d>0. \<exists>v. tr = [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
       InBlock ch v] \<and> s' = s(x := v))"
    by (metis receiveE)
  from cases show "big_step (Cm (ch[?]x)) (mass_scale k s) (scale_trace k tr)
    (mass_scale k s')"
  proof (elim disjE)
    assume z: "\<exists>v. tr = [InBlock ch v] \<and> s' = s(x := v)"
    from z obtain v where tr: "tr = [InBlock ch v]" and s': "s' = s(x := v)"
      by blast
    have b: "big_step (Cm (ch[?]x)) (mass_scale k s)
      [InBlock ch (scale_comm_value k ch v)]
      ((mass_scale k s)(x := scale_comm_value k ch v))"
      by (rule receiveB1)
    show ?thesis using b eq[of s v] tr s'
      by (simp add: scale_trace_def)
  next
    assume w: "\<exists>d>0. \<exists>v. tr = [WaitBlk d (\<lambda>_. State s) ({}, {ch}),
       InBlock ch v] \<and> s' = s(x := v)"
    from w obtain d v where dp: "0 < d"
      and tr: "tr = [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v]"
      and s': "s' = s(x := v)" by blast
    have b: "big_step (Cm (ch[?]x)) (mass_scale k s)
      [WaitBlk d (\<lambda>_. State (mass_scale k s)) ({}, {ch}),
       InBlock ch (scale_comm_value k ch v)]
      ((mass_scale k s)(x := scale_comm_value k ch v))"
      by (rule receiveB2[OF dp])
    show ?thesis using b eq[of s v] tr s'
      by (simp add: scale_trace_def scale_block_WaitBlk)
  qed
qed

lemma scale_ok_wait:
  assumes eq: "\<And>s. e (mass_scale k s) = e s"
  shows "scale_ok k (Wait e)"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (Wait e) s tr s'"
  from run have cases:
    "(0 < e s \<and> tr = [WaitBlk (e s) (\<lambda>_. State s) ({}, {})] \<and> s' = s)
     \<or> (\<not> 0 < e s \<and> tr = [] \<and> s' = s)"
    by (auto elim: waitE)
  from cases show "big_step (Wait e) (mass_scale k s) (scale_trace k tr)
    (mass_scale k s')"
  proof (elim disjE)
    assume z: "0 < e s \<and> tr = [WaitBlk (e s) (\<lambda>_. State s) ({}, {})]
      \<and> s' = s"
    have b: "big_step (Wait e) (mass_scale k s)
      [WaitBlk (e (mass_scale k s)) (\<lambda>_. State (mass_scale k s)) ({}, {})]
      (mass_scale k s)"
      by (rule waitB1) (simp add: eq z)
    show ?thesis using z b eq[of s]
      by (simp add: scale_trace_def scale_block_WaitBlk)
  next
    assume z: "\<not> 0 < e s \<and> tr = [] \<and> s' = s"
    from z have ng: "\<not> 0 < e s" and tr: "tr = []" and s': "s' = s"
      by auto
    have b: "big_step (Wait e) (mass_scale k s) [] (mass_scale k s)"
      by (rule waitB2) (simp add: eq ng)
    show ?thesis using b tr s' by simp
  qed
qed

lemma scale_ok_seq:
  assumes a: "scale_ok k C1" and b: "scale_ok k C2"
  shows "scale_ok k (C1; C2)"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (C1; C2) s tr s'"
  from run obtain u tr1 tr2 where r1: "big_step C1 s tr1 u"
    and r2: "big_step C2 u tr2 s'" and tr: "tr = tr1 @ tr2"
    by (auto elim: seqE)
  have a': "big_step C1 (mass_scale k s) (scale_trace k tr1) (mass_scale k u)"
    using a r1 unfolding scale_ok_def by blast
  have b': "big_step C2 (mass_scale k u) (scale_trace k tr2) (mass_scale k s')"
    using b r2 unfolding scale_ok_def by blast
  show "big_step (C1; C2) (mass_scale k s) (scale_trace k tr) (mass_scale k s')"
    using seqB[OF a' b'] tr by simp
qed

lemma scale_ok_rep:
  assumes step: "scale_ok k C"
  shows "scale_ok k (Rep C)"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (Rep C) s tr s'"
  from run show "big_step (Rep C) (mass_scale k s) (scale_trace k tr)
      (mass_scale k s')"
  proof (induct "Rep C" s tr s' rule: big_step.induct)
    case (RepetitionB1 s)
    have z: "big_step (Rep C) (mass_scale k s) [] (mass_scale k s)"
      by (rule RepetitionB1)
    show ?case using z by simp
  next
    case (RepetitionB2 s tr1 s2 tr2 s3 tr)
    have a: "big_step C (mass_scale k s) (scale_trace k tr1)
        (mass_scale k s2)"
      using step RepetitionB2.hyps(1) unfolding scale_ok_def by blast
    have b: "big_step (Rep C) (mass_scale k s2) (scale_trace k tr2)
        (mass_scale k s3)" using RepetitionB2 by blast
    show ?case using big_step.RepetitionB2[OF a b refl] RepetitionB2.hyps(5)
      by simp
  qed
qed

lemma scale_ok_ctrl0:
  assumes pos: "0 < k"
  shows "scale_ok k Ctrl0"
proof -
  have wait: "scale_ok k (Wait (\<lambda>_. Period))"
    by (rule scale_ok_wait) simp
  have rv: "scale_ok k (Cm (''p2c''[?]V))"
    by (rule scale_ok_receive, rule ext)
       (simp add: mass_scale_def scale_comm_value_def)
  have rw: "scale_ok k (Cm (''p2c''[?]W))"
    by (rule scale_ok_receive, rule ext)
       (simp add: mass_scale_def scale_comm_value_def)
  have rm: "scale_ok k (Cm (''m2c''[?]M))"
    by (rule scale_ok_receive, rule ext)
       (simp add: mass_scale_def scale_comm_value_def)
  have af: "scale_ok k (Fc ::= (\<lambda>s. s M * W_upd (s V) (s W)))"
    by (rule scale_ok_assign, rule ext)
       (simp add: mass_scale_def algebra_simps)
  have sf: "scale_ok k (Cm (''c2p''[!](\<lambda>s. s Fc / s M)))"
  proof (rule scale_ok_send)
    fix s
    show "mass_scale k s Fc / mass_scale k s M =
      scale_comm_value k ''c2p'' (s Fc / s M)"
      using pos by (simp add: scale_comm_value_def)
  qed
  show ?thesis unfolding Ctrl0_def
    by (intro scale_ok_seq wait rv rw rm af sf)
qed

lemma scale_ok_plant_post0:
  "scale_ok k
    (Cm (''p2c''[!](\<lambda>s. s W));
     Cm (''m2c''[!](\<lambda>s. s M));
     Cm (''c2p''[?]W);
     Fc ::= (\<lambda>s. s M * s W))"
proof -
  have sw: "scale_ok k (Cm (''p2c''[!](\<lambda>s. s W)))"
    by (rule scale_ok_send) (simp add: scale_comm_value_def)
  have sm: "scale_ok k (Cm (''m2c''[!](\<lambda>s. s M)))"
    by (rule scale_ok_send) (simp add: scale_comm_value_def)
  have rw: "scale_ok k (Cm (''c2p''[?]W))"
    by (rule scale_ok_receive, rule ext)
       (simp add: mass_scale_def scale_comm_value_def)
  have af: "scale_ok k (Fc ::= (\<lambda>s. s M * s W))"
    by (rule scale_ok_assign, rule ext)
       (simp add: mass_scale_def algebra_simps)
  show ?thesis by (intro scale_ok_seq sw sm rw af)
qed

lemma scale_ok_interrupt_one_send:
  assumes pos: "0 < k"
    and ode_scale: "\<And>p d. ODEsol ode p d \<Longrightarrow>
      ODEsol ode (\<lambda>t. mass_scale k (p t)) d"
    and guard: "\<And>s. b (mass_scale k s) \<longleftrightarrow> b s"
    and payload: "\<And>s. e (mass_scale k s) =
      scale_comm_value k ch (e s)"
    and post: "scale_ok k P"
  shows "scale_ok k (Interrupt ode b [(Send ch e, P)])"
proof (unfold scale_ok_def, intro allI impI)
  fix s tr s'
  assume run: "big_step (Interrupt ode b [(Send ch e, P)]) s tr s'"
  from run show "big_step (Interrupt ode b [(Send ch e, P)])
      (mass_scale k s) (scale_trace k tr) (mass_scale k s')"
  proof (induct "Interrupt ode b [(Send ch e, P)]" s tr s'
      rule: big_step.induct)
    case (InterruptSendB1 i ch0 e0 p2 sa tr2 s2)
    have i0: "i = 0" and branch: "ch0 = ch" "e0 = e" "p2 = P"
      using InterruptSendB1.hyps(1,2) by auto
    have p': "big_step P (mass_scale k sa) (scale_trace k tr2)
      (mass_scale k s2)"
      using post InterruptSendB1.hyps(3) branch
      unfolding scale_ok_def by blast
    have b': "big_step (Interrupt ode b [(Send ch e, P)])
      (mass_scale k sa)
      (OutBlock ch (e (mass_scale k sa)) # scale_trace k tr2)
      (mass_scale k s2)"
    proof (rule big_step.InterruptSendB1[where i = 0])
      show "0 < length [(Send ch e, P)]" by simp
      show "[(Send ch e, P)] ! 0 = (Send ch e, P)" by simp
      show "big_step P (mass_scale k sa) (scale_trace k tr2)
        (mass_scale k s2)" by (rule p')
    qed
    show ?case using b' payload[of sa] i0 branch
      by (simp add: scale_comm_value_def)
  next
    case (InterruptSendB2 d p sa i ch0 e0 p2 rdy tr2 s2)
    have i0: "i = 0" and branch: "ch0 = ch" "e0 = e" "p2 = P"
      using InterruptSendB2.hyps(5,6) by auto
    have sol': "ODEsol ode (\<lambda>t. mass_scale k (p t)) d"
      by (rule ode_scale[OF InterruptSendB2.hyps(2)])
    have guard': "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (mass_scale k (p t))"
      using InterruptSendB2.hyps(4) guard by blast
    have p0': "mass_scale k (p 0) = mass_scale k sa"
      using InterruptSendB2.hyps(3) by simp
    have p': "big_step P (mass_scale k (p d)) (scale_trace k tr2)
      (mass_scale k s2)"
      using post InterruptSendB2.hyps(8) branch
      unfolding scale_ok_def by blast
    have b': "big_step (Interrupt ode b [(Send ch e, P)])
      (mass_scale k sa)
      (WaitBlk d (\<lambda>t. State (mass_scale k (p t))) rdy #
       OutBlock ch (e (mass_scale k (p d))) # scale_trace k tr2)
      (mass_scale k s2)"
    proof (rule big_step.InterruptSendB2[where i = 0])
      show "0 < d" by (rule InterruptSendB2.hyps(1))
      show "ODEsol ode (\<lambda>t. mass_scale k (p t)) d" by (rule sol')
      show "mass_scale k (p 0) = mass_scale k sa" by (rule p0')
      show "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (mass_scale k (p t))"
        by (rule guard')
      show "0 < length [(Send ch e, P)]" by simp
      show "[(Send ch e, P)] ! 0 = (Send ch e, P)" by simp
      show "rdy = rdy_of_echoice [(Send ch e, P)]"
        using InterruptSendB2.hyps(7) branch by simp
      show "big_step P (mass_scale k (p d)) (scale_trace k tr2)
        (mass_scale k s2)" by (rule p')
    qed
    show ?case using b' payload[of "p d"] i0 branch
      by (simp add: scale_block_WaitBlk scale_comm_value_def)
  next
    case (InterruptReceiveB1 i ch0 var p2 v sa tr2 s2)
    then show ?case by simp
  next
    case (InterruptReceiveB2 d p sa i ch0 var p2 rdy v tr2 s2)
    then show ?case by simp
  next
    case (InterruptB1 sa)
    have ng: "\<not> b (mass_scale k sa)"
      using InterruptB1.hyps guard by simp
    have b': "big_step (Interrupt ode b [(Send ch e, P)])
      (mass_scale k sa) [] (mass_scale k sa)"
      by (rule big_step.InterruptB1) (rule ng)
    show ?case using b' by simp
  next
    case (InterruptB2 d p sa s2 rdy)
    have sol': "ODEsol ode (\<lambda>t. mass_scale k (p t)) d"
      by (rule ode_scale[OF InterruptB2.hyps(2)])
    have guard': "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (mass_scale k (p t))"
      using InterruptB2.hyps(3) guard by blast
    have ex': "\<not> b (mass_scale k (p d))"
      using InterruptB2.hyps(4) guard by simp
    have p0': "mass_scale k (p 0) = mass_scale k sa"
      using InterruptB2.hyps(5) by simp
    have pd': "mass_scale k (p d) = mass_scale k s2"
      using InterruptB2.hyps(6) by simp
    have b': "big_step (Interrupt ode b [(Send ch e, P)])
      (mass_scale k sa)
      [WaitBlk d (\<lambda>t. State (mass_scale k (p t))) rdy]
      (mass_scale k s2)"
      by (rule big_step.InterruptB2[OF InterruptB2.hyps(1) sol' guard' ex'
        p0' pd' InterruptB2.hyps(7)])
    show ?case using b' by (simp add: scale_block_WaitBlk)
  qed
qed

theorem scale_ok_plant0:
  assumes pos: "0 < k"
  shows "scale_ok k Plant0"
proof -
  have guard: "\<And>s. (0 < mass_scale k s M) \<longleftrightarrow> (0 < s M)"
    using pos by (simp add: zero_less_mult_iff)
  have payload: "\<And>s. mass_scale k s V =
      scale_comm_value k ''p2c'' (s V)"
    by (simp add: scale_comm_value_def)
  have ode_cert: "\<And>p d. ODEsol (ODE lander_mass_field) p d \<Longrightarrow>
      ODEsol (ODE lander_mass_field) (\<lambda>t. mass_scale k (p t)) d"
    by (rule mass_scale_plant_ODEsol[OF pos])
  have body: "scale_ok k
    (Interrupt (ODE lander_mass_field) (\<lambda>s. 0 < s M)
      [(''p2c''[!](\<lambda>s. s V),
        Cm (''p2c''[!](\<lambda>s. s W));
        Cm (''m2c''[!](\<lambda>s. s M));
        Cm (''c2p''[?]W);
        Fc ::= (\<lambda>s. s M * s W))])"
  proof (rule scale_ok_interrupt_one_send)
    show "0 < k" by (rule pos)
  next
    fix p d
    assume sol: "ODEsol (ODE lander_mass_field) p d"
    show "ODEsol (ODE lander_mass_field)
      (\<lambda>t. mass_scale k (p t)) d" by (rule ode_cert[OF sol])
  next
    fix s
    show "(0 < mass_scale k s M) = (0 < s M)" by (rule guard)
  next
    fix s
    show "mass_scale k s V = scale_comm_value k ''p2c'' (s V)"
      by (rule payload)
  next
    show "scale_ok k
      (Cm (''p2c''[!](\<lambda>s. s W));
       Cm (''m2c''[!](\<lambda>s. s M));
       Cm (''c2p''[?]W); Fc ::= (\<lambda>s. s M * s W))"
      by (rule scale_ok_plant_post0)
  qed
  show ?thesis unfolding Plant0_def by (rule body)
qed

theorem scale_ok_lander0_components:
  assumes pos: "0 < k"
  shows "scale_ok k (Rep Plant0)" "scale_ok k (Rep Ctrl0)"
  by (rule scale_ok_rep[OF scale_ok_plant0[OF pos]],
      rule scale_ok_rep[OF scale_ok_ctrl0[OF pos]])

theorem lander0_scale_run:
  assumes pos: "0 < k"
    and run: "par_big_step Lander0
      (ParState (State sp) (State sc)) tr
      (ParState (State sp') (State sc'))"
  shows "par_big_step Lander0
    (ParState (State (mass_scale k sp)) (State (mass_scale k sc)))
    (scale_trace k tr)
    (ParState (State (mass_scale k sp')) (State (mass_scale k sc')))"
proof -
  from run[unfolded Lander0_def] obtain trp trc where
    lp: "par_big_step (Single (Rep Plant0)) (State sp) trp (State sp')"
    and lc: "par_big_step (Single (Rep Ctrl0)) (State sc) trc (State sc')"
    and cb: "combine_blocks {''p2c'', ''m2c'', ''c2p''} trp trc tr"
    by (blast elim!: ParallelE)
  from lp have rp: "big_step (Rep Plant0) sp trp sp'"
    by (auto elim: SingleE)
  from lc have rc: "big_step (Rep Ctrl0) sc trc sc'"
    by (auto elim: SingleE)
  have rp': "big_step (Rep Plant0) (mass_scale k sp)
      (scale_trace k trp) (mass_scale k sp')"
    using scale_ok_lander0_components(1)[OF pos] rp
    unfolding scale_ok_def by blast
  have rc': "big_step (Rep Ctrl0) (mass_scale k sc)
      (scale_trace k trc) (mass_scale k sc')"
    using scale_ok_lander0_components(2)[OF pos] rc
    unfolding scale_ok_def by blast
  have cb': "combine_blocks {''p2c'', ''m2c'', ''c2p''}
      (scale_trace k trp) (scale_trace k trc) (scale_trace k tr)"
    by (rule combine_blocks_scale[OF cb])
  have pp: "par_big_step (Single (Rep Plant0))
      (State (mass_scale k sp)) (scale_trace k trp)
      (State (mass_scale k sp'))" by (rule SingleB[OF rp'])
  have pc: "par_big_step (Single (Rep Ctrl0))
      (State (mass_scale k sc)) (scale_trace k trc)
      (State (mass_scale k sc'))" by (rule SingleB[OF rc'])
  show ?thesis unfolding Lander0_def
    by (rule ParallelB[OF pp pc cb'])
qed

end
