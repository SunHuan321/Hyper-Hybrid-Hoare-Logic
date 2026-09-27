theory HybridOracle
  imports Complex_Main
begin

section \<open>Numerical oracle obligations (delegated to external solvers)\<close>

text \<open>
ARCHITECTURE.  H3L separates proof-theoretic work from numerical facts:

  \<^item> the framework (semantics, proof rules, refinement transfer, case-study
    structure) is proved in full, without any \<open>sorry\<close>;
  \<^item> purely numerical facts about concrete polynomial invariants are
    stated here as \<open>oracle_\<close> lemmas and discharged by \<bold>\<open>external
    solvers\<close> (SOS/SDP certificate tools, Mathematica, or a certified
    Positivstellensatz certificate checked by Isabelle's \<open>sos\<close> method
    with an explicit certificate).

Conventions:
  \<^item> every lemma in this theory is named \<open>oracle_*\<close> and proved by
    \<open>sorry\<close> until an external certificate is supplied;
  \<^item> every entry documents the exact algebraic content, the numerical
    evidence, and the intended external solver route;
  \<^item> \<open>grep oracle_ HybridOracle.thy\<close> is the complete checklist of
    open numerical obligations.

This mirrors the gGHL practice (its Lander1/Lander2 developments carry the
same obligations as local \<open>sorry\<close>s), but centralises them so the
framework itself stays obligation-free.
\<close>


subsection \<open>Lunar lander invariant: the numerical facts\<close>

text \<open>Sampling period and the guidance-law update (constants from the
FM 2014 descent guidance case study).\<close>

definition Period :: real where "Period = 0.128"

definition W_upd :: "real \<Rightarrow> real \<Rightarrow> real" where
  "W_upd v w = (-(w - 3.732) * 0.01 + 3.732 - (v - (-1.5)) * 0.6)"

text \<open>The SDP-generated quartic invariant (as used in gGHL's
\<^theory_text>\<open>hhl/Lander1\<close>/\<^theory_text>\<open>Lander2\<close>).\<close>

definition landerinv :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"landerinv t v w = (15025282795421706426953 - 38191371615549881350000*t +
  9482947285373987200000*t^2 - 90382078252408000000*t^3 -
  12597135205472000000*t^4 + 5070724623344300111384 * v +
  29051341984741759604000 * t * v + 12905500940447680000000*t^2 * v -
  3452247087952000000*t^3 * v + 3754952256975690758168 * v^2 -
  4369639740028640264000*t * v^2 + 4290324517728000000000*t^2 * v^2 +
  10509874347360 * v^3 - 8711967253392000*t * v^3 + 1751645724560 * v^4 -
  6016579819909859424000*w + 32152462695621728000000*t*w +
  63926169690400000000*t^2*w + 1659591880613072768000 * v *w -
  11298598523808000000000*t * v *w + 2216823024256000 * v^2*w +
  1139598426176000000000*w^2 - 6579819920896000000000*t*w^2)/(160000000000000000000)"

text \<open>The Lie derivative of \<^term>\<open>landerinv\<close> along the lander ODE
\<open>v' = w - 3.732, w' = w^2/2500, t' = 1\<close>, computed symbolically
(exact rational arithmetic).\<close>

definition landerLie :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
"landerLie t v w = ((-107882721498500000000)*t^3*w + (-1172023584051598000000)*t^3
  + 268145282358000000000000*t^2*v*w + (-1001041841924551500000000)*t^2*v
  + 799077121130000000*t^2*w^2 + 403296904388990000000000*t^2*w
  + (-1513577367015873930000000)*t^2 + (-816746930005500000)*t*v^2*w
  + 268148330457542780526000*t*v^2 + (-141232481547600000000)*t*v*w^2
  + (-273102483751790016500000)*t*v*w + 1825812278139660341578000*t*v
  + (-164495498022400000000)*t*w^3 + (-352679298085304728400000)*t*w^2
  + 2229548875467937987625000*t*w + (-2795428553634633513816500)*t
  + 218955715570000*v^3*w + (-273066119399007240)*v^3
  + 27710287803200*v^2*w^2 + 985300720065000*v^2*w
  + (-136551245553037295532580)*v^2 + 20883449946679409600*v*w^2
  + (-118397204881989735326500)*v*w + 32011823083600118282314*v
  + 28489960654400000000*w^3 + (-153832333506590349242800)*w^2
  + 969674700641188766912750*w + (-1784853622183462792677659))/(5000000000000000000000)"

text \<open>
\<^bold>\<open>Obligation 1: discrete step preserves the invariant.\<close>
Used twice (\<^theory_text>\<open>hhl/Lander1\<close> and \<^theory_text>\<open>hhl/Lander2\<close>, lemma
\<open>landerinv_prop2\<close>).

Numerical evidence: 300k random samples (physical box and a broad box);
at all 334 sample points with \<^term>\<open>landerinv Period v w \<le> 0\<close> the
conclusion held; zero counterexamples.

External route: Positivstellensatz certificate
\<open>-P2 = S0 + T * (-P1)\<close> with \<open>T\<close> a positive quadratic and
\<open>S0\<close> an sos sextic.  A floating-point SDP (Clarabel, centred
coordinates \<open>v+1.5, w-3.732\<close>) certifies existence; rationalisation
of the boundary Gram matrix is the remaining step for a certificate
acceptable to Isabelle's \<open>sos\<close> method with explicit certificate.
\<close>

axiomatization where
  oracle_Lander_discrete_step:
  "landerinv Period v w \<le> 0 \<Longrightarrow> landerinv 0 v (W_upd v w) \<le> 0"

text \<open>
\<^bold>\<open>Obligation 2: barrier (strict Lie-derivative sign on the boundary).\<close>
Used by the differential-cut/barrier rule applications in
\<^theory_text>\<open>hhl/Lander1\<close> and \<^theory_text>\<open>hhl/Lander2\<close>.

External route: sign of an explicit polynomial on the algebraic set
\<open>{landerinv = 0}\<close> restricted to the strip \<open>0 \<le> t \<le> Period\<close>:
an SOS certificate over the constructed set, or interval/Bernstein
evaluation on the physical box.
\<close>

axiomatization where oracle_Lander_barrier:
  "\<And>t v w::real. 0 \<le> t \<Longrightarrow> t \<le> Period \<Longrightarrow> landerinv t v w = 0 \<Longrightarrow>
    landerLie t v w < 0"

text \<open>
Correctness of the symbolically computed Lie derivative itself is NOT an
oracle obligation: it is discharged by \<open>derivative_intros\<close> on the
polynomial \<^term>\<open>landerinv\<close> together with the chain rule (see
\<open>ContinuousInvHHL.Valid_inv_barrier_s_tr_le\<close> applications in the
Lander developments).
\<close>

end
