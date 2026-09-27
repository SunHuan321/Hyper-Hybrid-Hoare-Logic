theory PhaseG_GNI_comm
  imports PhaseG_GNI_parallel
begin

section \<open>F3: explicit now/wait members for receive and interrupt\<close>

lemma recv_nowI:
  assumes src: "(a, q, tr) \<in> S"
  shows "(a, q(x := v), tr @ [InBlock ch v]) \<in> sem (Cm (ch[?]x)) S"
proof -
  have step: "big_step (Cm (ch[?]x)) q [InBlock ch v] (q(x := v))"
    by (rule receiveB1)
  from src step show ?thesis by (auto simp: in_sem)
qed

lemma recv_waitI:
  assumes src: "(a, q, tr) \<in> S" and pos: "0 < d"
  shows "(a, q(x := v),
    tr @ [WaitBlk d (\<lambda>_. State q) ({}, {ch}), InBlock ch v])
    \<in> sem (Cm (ch[?]x)) S"
proof -
  have step: "big_step (Cm (ch[?]x)) q
    [WaitBlk d (\<lambda>_. State q) ({}, {ch}), InBlock ch v] (q(x := v))"
    by (rule receiveB2[OF pos])
  from src step show ?thesis by (auto simp: in_sem)
qed

lemma interrupt_send_nowI:
  assumes src: "(a, q, tr) \<in> S"
    and idx: "i < length cs" and branch: "cs ! i = (Send ch e, p)"
    and tail: "big_step p q tr2 q'"
  shows "(a, q', tr @ (OutBlock ch (e q) # tr2))
    \<in> sem (Interrupt ode b cs) S"
proof -
  have step: "big_step (Interrupt ode b cs) q (OutBlock ch (e q) # tr2) q'"
    by (rule InterruptSendB1[OF idx branch tail])
  from src step show ?thesis by (auto simp: in_sem)
qed

lemma interrupt_send_waitI:
  assumes src: "(a, q, tr) \<in> S" and pos: "0 < d"
    and sol: "ODEsol ode sl d" and init: "sl 0 = q"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
    and idx: "i < length cs" and branch: "cs ! i = (Send ch e, p)"
    and tail: "big_step p (sl d) tr2 q'"
  shows "(a, q', tr @ (WaitBlk d (\<lambda>t. State (sl t)) (rdy_of_echoice cs)
      # OutBlock ch (e (sl d)) # tr2)) \<in> sem (Interrupt ode b cs) S"
proof -
  have step: "big_step (Interrupt ode b cs) q
    (WaitBlk d (\<lambda>t. State (sl t)) (rdy_of_echoice cs)
      # OutBlock ch (e (sl d)) # tr2) q'"
    by (rule InterruptSendB2[OF pos sol init inside idx branch refl tail])
  from src step show ?thesis by (auto simp: in_sem)
qed

lemma interrupt_recv_nowI:
  assumes src: "(a, q, tr) \<in> S"
    and idx: "i < length cs" and branch: "cs ! i = (Receive ch x, p)"
    and tail: "big_step p (q(x := v)) tr2 q'"
  shows "(a, q', tr @ (InBlock ch v # tr2))
    \<in> sem (Interrupt ode b cs) S"
proof -
  have step: "big_step (Interrupt ode b cs) q (InBlock ch v # tr2) q'"
    by (rule InterruptReceiveB1[OF idx branch tail])
  from src step show ?thesis by (auto simp: in_sem)
qed

lemma interrupt_recv_waitI:
  assumes src: "(a, q, tr) \<in> S" and pos: "0 < d"
    and sol: "ODEsol ode sl d" and init: "sl 0 = q"
    and inside: "\<forall>t. 0 \<le> t \<and> t < d \<longrightarrow> b (sl t)"
    and idx: "i < length cs" and branch: "cs ! i = (Receive ch x, p)"
    and tail: "big_step p ((sl d)(x := v)) tr2 q'"
  shows "(a, q', tr @ (WaitBlk d (\<lambda>t. State (sl t)) (rdy_of_echoice cs)
      # InBlock ch v # tr2)) \<in> sem (Interrupt ode b cs) S"
proof -
  have step: "big_step (Interrupt ode b cs) q
    (WaitBlk d (\<lambda>t. State (sl t)) (rdy_of_echoice cs)
      # InBlock ch v # tr2) q'"
    by (rule InterruptReceiveB2[OF pos sol init inside idx branch refl tail])
  from src step show ?thesis by (auto simp: in_sem)
qed

end
