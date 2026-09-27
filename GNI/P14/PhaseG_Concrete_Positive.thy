theory PhaseG_Concrete_Positive
  imports PhaseG_Concrete_GNI
begin

section \<open>A positive-time synchronized execution\<close>

definition plant0_zero_path :: "real \<Rightarrow> real \<Rightarrow> state" where
  "plant0_zero_path m t = ((\<lambda>_. 0)(M := m))(V := -3.732 * t)"

lemma plant0_zero_path_sol:
  "ODEsol (ODE lander_mass_field) (plant0_zero_path m) Period"
proof -
  let ?D = "{-1..Period+1}"
  have id: "((\<lambda>t. t) has_vderiv_on (\<lambda>t. 1)) ?D"
    by (simp add: has_vderiv_on_id)
  have vd: "((\<lambda>t. -3.732 * t) has_vderiv_on (\<lambda>t. -3.732)) ?D"
    using has_vderiv_on_scale_const[OF id, of "-3.732"] by simp
  have comp: "\<And>x. ((\<lambda>t. plant0_zero_path m t x) has_vderiv_on
      (\<lambda>t. lander_mass_field x (plant0_zero_path m t))) ?D"
  proof -
    fix x
    show "((\<lambda>t. plant0_zero_path m t x) has_vderiv_on
      (\<lambda>t. lander_mass_field x (plant0_zero_path m t))) ?D"
    proof (cases "x = V")
      case True
      then show ?thesis using vd
        by (simp add: plant0_zero_path_def)
    next
      case v: False
      consider (m) "x = M" | (f) "x = Fc" | (w) "x = W" |
        (other) "x \<noteq> M \<and> x \<noteq> Fc \<and> x \<noteq> W" by auto
      then show ?thesis
      proof cases
        case m
        then show ?thesis using v
          by (simp add: plant0_zero_path_def has_vderiv_on_const)
      next
        case f
        then show ?thesis using v
          by (simp add: plant0_zero_path_def has_vderiv_on_const)
      next
        case w
        then show ?thesis using v
          by (simp add: plant0_zero_path_def has_vderiv_on_const)
      next
        case other
        then show ?thesis using v
          by (simp add: plant0_zero_path_def has_vderiv_on_const)
      qed
    qed
  qed
  show ?thesis
    by (rule ODEsol_from_components[OF _ _ comp])
       (simp_all add: Period_def)
qed

lemma plant0_zero_post:
  fixes m :: real
  defines "s \<equiv> plant0_zero_path m Period"
    and "w \<equiv> W_upd ((plant0_zero_path m Period) V) 0"
  shows "big_step
    (Cm (''p2c''[!](\<lambda>s. s W));
     Cm (''m2c''[!](\<lambda>s. s M));
     Cm (''c2p''[?]W);
     Fc ::= (\<lambda>s. s M * s W)) s
    [OutBlock ''p2c'' 0, OutBlock ''m2c'' m, InBlock ''c2p'' w]
    ((s(W := w))(Fc := m * w))"
proof -
  have sm: "s M = m" and sw: "s W = 0"
    unfolding s_def plant0_zero_path_def by simp_all
  have a0: "big_step (Cm (''p2c''[!](\<lambda>s. s W))) s
      [OutBlock ''p2c'' (s W)] s" by (rule sendB1)
  have a: "big_step (Cm (''p2c''[!](\<lambda>s. s W))) s
      [OutBlock ''p2c'' 0] s" using a0 sw by simp
  have b0: "big_step (Cm (''m2c''[!](\<lambda>s. s M))) s
      [OutBlock ''m2c'' (s M)] s" by (rule sendB1)
  have b: "big_step (Cm (''m2c''[!](\<lambda>s. s M))) s
      [OutBlock ''m2c'' m] s" using b0 sm by simp
  have c: "big_step (Cm (''c2p''[?]W)) s
      [InBlock ''c2p'' w] (s(W := w))" by (rule receiveB1)
  have d0: "big_step (Fc ::= (\<lambda>s. s M * s W)) (s(W := w)) []
      ((s(W := w))(Fc := (s(W := w)) M * (s(W := w)) W))"
    by (rule assignB)
  have d: "big_step (Fc ::= (\<lambda>s. s M * s W)) (s(W := w)) []
      ((s(W := w))(Fc := m * w))" using d0 sm by simp
  have cd: "big_step (Cm (''c2p''[?]W); Fc ::= (\<lambda>s. s M * s W))
      s [InBlock ''c2p'' w] ((s(W := w))(Fc := m * w))"
    using seqB[OF c d] by simp
  have bcd: "big_step
      (Cm (''m2c''[!](\<lambda>s. s M));
       Cm (''c2p''[?]W); Fc ::= (\<lambda>s. s M * s W))
      s [OutBlock ''m2c'' m, InBlock ''c2p'' w]
      ((s(W := w))(Fc := m * w))"
    using seqB[OF b cd] by simp
  show ?thesis using seqB[OF a bcd] by simp
qed

lemma ctrl0_zero_cycle:
  assumes mp: "0 < m"
  shows "\<exists>sc'. big_step Ctrl0 ((\<lambda>_. 0)(M := m))
    [WaitBlk Period (\<lambda>_. State ((\<lambda>_. 0)(M := m))) ({}, {}),
     InBlock ''p2c'' v, InBlock ''p2c'' 0,
     InBlock ''m2c'' m, OutBlock ''c2p'' (W_upd v 0)] sc'"
proof -
  let ?s = "(\<lambda>_. 0)(M := m)"
  let ?sV = "?s(V := v)"
  let ?sW = "?sV(W := 0)"
  let ?sM = "?sW(M := m)"
  let ?sF = "?sM(Fc := ?sM M * W_upd (?sM V) (?sM W))"
  let ?w = "W_upd v 0"
  have a: "big_step (Cm (''p2c''[?]V)) ?s
    [InBlock ''p2c'' v] ?sV" by (rule receiveB1)
  have b: "big_step (Cm (''p2c''[?]W)) ?sV
    [InBlock ''p2c'' 0] ?sW" by (rule receiveB1)
  have c: "big_step (Cm (''m2c''[?]M)) ?sW
    [InBlock ''m2c'' m] ?sM" by (rule receiveB1)
  have d: "big_step (Fc ::= (\<lambda>s. s M * W_upd (s V) (s W)))
    ?sM [] ?sF" by (rule assignB)
  have val: "?sF Fc / ?sF M = ?w"
    using mp by simp
  have e0: "big_step (Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?sF
    [OutBlock ''c2p'' (?sF Fc / ?sF M)] ?sF" by (rule sendB1)
  have e: "big_step (Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?sF
    [OutBlock ''c2p'' ?w] ?sF" using e0 val by simp
  have de: "big_step
    (Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
     Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?sM
    [OutBlock ''c2p'' ?w] ?sF"
    using seqB[OF d e] by simp
  have cde: "big_step
    (Cm (''m2c''[?]M);
     Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
     Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?sW
    [InBlock ''m2c'' m, OutBlock ''c2p'' ?w] ?sF"
    using seqB[OF c de] by simp
  have bcde: "big_step
    (Cm (''p2c''[?]W);
     Cm (''m2c''[?]M);
     Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
     Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?sV
    [InBlock ''p2c'' 0, InBlock ''m2c'' m, OutBlock ''c2p'' ?w] ?sF"
    using seqB[OF b cde] by simp
  have abcde: "big_step
    (Cm (''p2c''[?]V);
     Cm (''p2c''[?]W);
     Cm (''m2c''[?]M);
     Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
     Cm (''c2p''[!](\<lambda>s. s Fc / s M))) ?s
    [InBlock ''p2c'' v, InBlock ''p2c'' 0,
     InBlock ''m2c'' m, OutBlock ''c2p'' ?w] ?sF"
    using seqB[OF a bcde] by simp
  have wait: "big_step (Wait (\<lambda>_. Period)) ?s
    [WaitBlk Period (\<lambda>_. State ?s) ({}, {})] ?s"
    using waitB1[of "\<lambda>_. Period" ?s] by (simp add: Period_def)
  have all: "big_step Ctrl0 ?s
    [WaitBlk Period (\<lambda>_. State ?s) ({}, {}),
     InBlock ''p2c'' v, InBlock ''p2c'' 0,
     InBlock ''m2c'' m, OutBlock ''c2p'' ?w] ?sF"
    unfolding Ctrl0_def using seqB[OF wait abcde] by simp
  show ?thesis by (rule_tac x = ?sF in exI) (rule all)
qed

lemma plant0_zero_cycle:
  assumes mp: "0 < m"
  shows "\<exists>sp'. big_step Plant0 ((\<lambda>_. 0)(M := m))
    [WaitBlk Period (\<lambda>t. State (plant0_zero_path m t))
       ({''p2c''}, {}),
     OutBlock ''p2c'' (-3.732 * Period), OutBlock ''p2c'' 0,
     OutBlock ''m2c'' m,
     InBlock ''c2p'' (W_upd (-3.732 * Period) 0)] sp'"
proof -
  let ?s = "(\<lambda>_. 0)(M := m)"
  let ?p = "plant0_zero_path m"
  let ?v = "-3.732 * Period"
  let ?w = "W_upd ?v 0"
  let ?f = "((?p Period)(W := ?w))(Fc := m * ?w)"
  let ?post = "Cm (''p2c''[!](\<lambda>s. s W));
     Cm (''m2c''[!](\<lambda>s. s M));
     Cm (''c2p''[?]W);
     Fc ::= (\<lambda>s. s M * s W)"
  have post: "big_step ?post (?p Period)
    [OutBlock ''p2c'' 0, OutBlock ''m2c'' m,
     InBlock ''c2p'' ?w] ?f"
    using plant0_zero_post[of m]
    by (simp add: plant0_zero_path_def)
  have dp: "0 < Period" by (simp add: Period_def)
  have p0: "?p 0 = ?s"
    by (rule ext) (simp add: plant0_zero_path_def)
  have inside: "\<forall>t. 0 \<le> t \<and> t < Period \<longrightarrow> 0 < ?p t M"
    using mp by (simp add: plant0_zero_path_def)
  have intr: "big_step
    (Interrupt (ODE lander_mass_field) (\<lambda>s. 0 < s M)
      [(''p2c''[!](\<lambda>s. s V), ?post)]) ?s
    (WaitBlk Period (\<lambda>t. State (?p t)) ({''p2c''}, {}) #
     OutBlock ''p2c'' (?p Period V) #
     [OutBlock ''p2c'' 0, OutBlock ''m2c'' m,
      InBlock ''c2p'' ?w]) ?f"
  proof (rule big_step.InterruptSendB2[where i = 0])
    show "0 < Period" by (rule dp)
    show "ODEsol (ODE lander_mass_field) ?p Period"
      by (rule plant0_zero_path_sol)
    show "?p 0 = ?s" by (rule p0)
    show "\<forall>t. 0 \<le> t \<and> t < Period \<longrightarrow> 0 < ?p t M"
      by (rule inside)
    show "0 < length [(''p2c''[!](\<lambda>s. s V), ?post)]" by simp
    show "[(''p2c''[!](\<lambda>s. s V), ?post)] ! 0 =
      (''p2c''[!](\<lambda>s. s V), ?post)" by simp
    show "({''p2c''}, {}) =
      rdy_of_echoice [(''p2c''[!](\<lambda>s. s V), ?post)]" by simp
    show "big_step ?post (?p Period)
      [OutBlock ''p2c'' 0, OutBlock ''m2c'' m,
       InBlock ''c2p'' ?w] ?f" by (rule post)
  qed
  have all: "big_step Plant0 ?s
    [WaitBlk Period (\<lambda>t. State (?p t)) ({''p2c''}, {}),
     OutBlock ''p2c'' ?v, OutBlock ''p2c'' 0,
     OutBlock ''m2c'' m, InBlock ''c2p'' ?w] ?f"
    using intr unfolding Plant0_def by (simp add: plant0_zero_path_def)
  show ?thesis by (rule_tac x = ?f in exI) (rule all)
qed

theorem lander0_zero_synchronized_cycle:
  assumes mp: "0 < m"
  shows "\<exists>sp' sc' tr.
    par_big_step Lander0
      (ParState (State ((\<lambda>_. 0)(M := m)))
        (State ((\<lambda>_. 0)(M := m)))) tr
      (ParState (State sp') (State sc'))
    \<and> (\<exists>p rdy rest. tr = WaitBlk Period p rdy # rest)"
proof -
  let ?s = "(\<lambda>_. 0)(M := m)"
  let ?p = "plant0_zero_path m"
  let ?v = "-3.732 * Period"
  let ?w = "W_upd ?v 0"
  let ?chs = "{''p2c'', ''m2c'', ''c2p''}"
  let ?tp = "[WaitBlk Period (\<lambda>t. State (?p t)) ({''p2c''}, {}),
    OutBlock ''p2c'' ?v, OutBlock ''p2c'' 0,
    OutBlock ''m2c'' m, InBlock ''c2p'' ?w]"
  let ?tc = "[WaitBlk Period (\<lambda>_. State ?s) ({}, {}),
    InBlock ''p2c'' ?v, InBlock ''p2c'' 0,
    InBlock ''m2c'' m, OutBlock ''c2p'' ?w]"
  let ?tg = "[WaitBlk Period
      (\<lambda>t. ParState (State (?p t)) (State ?s)) ({''p2c''}, {}),
    IOBlock ''p2c'' ?v, IOBlock ''p2c'' 0,
    IOBlock ''m2c'' m, IOBlock ''c2p'' ?w]"
  from plant0_zero_cycle[OF mp] obtain sp' where plant:
    "big_step Plant0 ?s ?tp sp'" by blast
  from ctrl0_zero_cycle[OF mp] obtain sc' where ctrl:
    "big_step Ctrl0 ?s ?tc sc'" by blast
  have z: "combine_blocks ?chs [] [] []"
    by (rule combine_blocks_empty)
  have c4: "combine_blocks ?chs [InBlock ''c2p'' ?w]
    [OutBlock ''c2p'' ?w] [IOBlock ''c2p'' ?w]"
    by (rule combine_blocks_pair1[OF _ z]) simp
  have c3: "combine_blocks ?chs
    [OutBlock ''m2c'' m, InBlock ''c2p'' ?w]
    [InBlock ''m2c'' m, OutBlock ''c2p'' ?w]
    [IOBlock ''m2c'' m, IOBlock ''c2p'' ?w]"
    by (rule combine_blocks_pair2[OF _ c4]) simp
  have c2: "combine_blocks ?chs
    [OutBlock ''p2c'' 0, OutBlock ''m2c'' m, InBlock ''c2p'' ?w]
    [InBlock ''p2c'' 0, InBlock ''m2c'' m, OutBlock ''c2p'' ?w]
    [IOBlock ''p2c'' 0, IOBlock ''m2c'' m, IOBlock ''c2p'' ?w]"
    by (rule combine_blocks_pair2[OF _ c3]) simp
  have c1: "combine_blocks ?chs
    [OutBlock ''p2c'' ?v, OutBlock ''p2c'' 0,
     OutBlock ''m2c'' m, InBlock ''c2p'' ?w]
    [InBlock ''p2c'' ?v, InBlock ''p2c'' 0,
     InBlock ''m2c'' m, OutBlock ''c2p'' ?w]
    [IOBlock ''p2c'' ?v, IOBlock ''p2c'' 0,
     IOBlock ''m2c'' m, IOBlock ''c2p'' ?w]"
    by (rule combine_blocks_pair2[OF _ c2]) simp
  have cb: "combine_blocks ?chs ?tp ?tc ?tg"
  proof (rule combine_blocks_wait1[OF c1])
    show "compat_rdy ({''p2c''}, {}) ({}, {})" by simp
    show "(\<lambda>t. ParState (State (?p t)) (State ?s)) =
      (\<lambda>t. ParState ((\<lambda>x. State (?p x)) t)
        ((\<lambda>x. State ?s) t))" by simp
    show "({''p2c''}, {}) = merge_rdy ({''p2c''}, {}) ({}, {})"
      by simp
  qed
  have rp: "big_step (Rep Plant0) ?s ?tp sp'"
    using big_step.RepetitionB2[OF plant RepetitionB1 refl] by simp
  have rc: "big_step (Rep Ctrl0) ?s ?tc sc'"
    using big_step.RepetitionB2[OF ctrl RepetitionB1 refl] by simp
  have pp: "par_big_step (Single (Rep Plant0)) (State ?s) ?tp
    (State sp')" by (rule SingleB[OF rp])
  have pc: "par_big_step (Single (Rep Ctrl0)) (State ?s) ?tc
    (State sc')" by (rule SingleB[OF rc])
  have run: "par_big_step Lander0
    (ParState (State ?s) (State ?s)) ?tg
    (ParState (State sp') (State sc'))"
    unfolding Lander0_def by (rule ParallelB[OF pp pc cb])
  have head: "\<exists>p rdy rest. ?tg = WaitBlk Period p rdy # rest"
    by (rule_tac x = "\<lambda>t. ParState (State (?p t)) (State ?s)" in exI,
        rule_tac x = "({''p2c''}, {})" in exI,
        rule_tac x = "[IOBlock ''p2c'' ?v, IOBlock ''p2c'' 0,
          IOBlock ''m2c'' m, IOBlock ''c2p'' ?w]" in exI) simp
  have both: "par_big_step Lander0
    (ParState (State ?s) (State ?s)) ?tg
    (ParState (State sp') (State sc'))
    \<and> (\<exists>p rdy rest. ?tg = WaitBlk Period p rdy # rest)"
    by (rule conjI[OF run head])
  show ?thesis
    by (rule_tac x = sp' in exI,
        rule_tac x = sc' in exI,
        rule_tac x = ?tg in exI)
       (rule both)
qed

theorem lander0_zero_family_positive_cycle:
  "\<exists>r\<in>par_sem Lander0 lander0_zero_family.
    \<exists>p rdy rest. 0 < Period \<and>
      snd r = WaitBlk Period p rdy # rest"
proof -
  let ?m = "1::real"
  let ?s = "(\<lambda>_. 0)(M := ?m)"
  let ?lp = "(\<lambda>_. 0)(HI := ?m)"
  let ?lc = "(\<lambda>_. 0)"
  let ?i = "ExParState (ExState (?lp, ?s)) (ExState (?lc, ?s))"
  have init: "?i \<in> lander0_zero_family"
    unfolding lander0_zero_family_def
    by (rule CollectI, rule_tac x = ?m in exI) simp
  have syn: "\<exists>sp' sc' tr.
    par_big_step Lander0 (ParState (State ?s) (State ?s)) tr
      (ParState (State sp') (State sc'))
    \<and> (\<exists>p rdy rest. tr = WaitBlk Period p rdy # rest)"
    by (rule lander0_zero_synchronized_cycle) simp
  from syn obtain sp' sc' tr where
    run: "par_big_step Lander0 (ParState (State ?s) (State ?s)) tr
      (ParState (State sp') (State sc'))"
    and head: "\<exists>p rdy rest. tr = WaitBlk Period p rdy # rest"
    by blast
  let ?r = "(ExParState (ExState (?lp, sp')) (ExState (?lc, sc')), tr)"
  have mem: "?r \<in> par_sem Lander0 lander0_zero_family"
    unfolding in_par_sem
    apply (rule_tac x = ?i in exI)
    using init run by simp
  from head obtain p rdy rest where tr:
    "tr = WaitBlk Period p rdy # rest" by blast
  have dur: "0 < Period" by (simp add: Period_def)
  have obs: "\<exists>p rdy rest. 0 < Period \<and>
    snd ?r = WaitBlk Period p rdy # rest"
    by (rule_tac x = p in exI,
        rule_tac x = rdy in exI,
        rule_tac x = rest in exI)
       (simp add: dur tr)
  show ?thesis
    by (rule_tac x = ?r in bexI) (rule obs, rule mem)
qed

end
