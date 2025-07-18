theory BigStepSimple
  imports "../Language"
begin

subsection \<open>Validity\<close>

text \<open>Assertion is a predicate on states and traces\<close>

type_synonym assn = "state \<Rightarrow> trace \<Rightarrow> bool"

definition Valid :: "assn \<Rightarrow> proc \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>H\<^sub>L ({(1_)}/ (_)/ {(1_)})" 50) where
  "\<Turnstile>\<^sub>H\<^sub>L {P} c {Q} \<longleftrightarrow> (\<forall>s1 tr1 s2 tr2. P s1 tr1 \<longrightarrow> big_step c s1 tr2 s2 \<longrightarrow> Q s2 (tr1 @ tr2))"

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>A" 25) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>s tr. P s tr \<longrightarrow> Q s tr)"

lemma entails_refl [simp]:
  "P \<Longrightarrow>\<^sub>A P"
  unfolding entails_def by auto

lemma entails_trans:
  "(P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>A R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>A R)"
  unfolding entails_def by auto

lemma Valid_ex_pre:
  "(\<And>v. \<Turnstile>\<^sub>H\<^sub>L {P v} c {Q}) \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. \<exists>v. P v s t} c {Q}"
  unfolding Valid_def by auto

lemma Valid_ex_post:
  "\<exists>v. \<Turnstile>\<^sub>H\<^sub>L {P} c {Q v} \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c {\<lambda>s t. \<exists>v. Q v s t}"
  unfolding Valid_def by blast

lemma Valid_and_pre:
  "(P1 \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c {Q}) \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P1 \<and> P s t} c {Q}"
  unfolding Valid_def by auto

theorem Valid_weaken_pre:
  "P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P'} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c {Q}"
  unfolding Valid_def entails_def by blast

theorem Valid_strengthen_post:
  "Q \<Longrightarrow>\<^sub>A Q' \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c {Q'}"
  unfolding Valid_def entails_def by blast

theorem Valid_skip:
  "\<Turnstile>\<^sub>H\<^sub>L {P} Skip {P}"
  unfolding Valid_def
  by (auto elim: skipE)

theorem Valid_assign:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s. Q (s(var := e s))} var ::= e {Q}"
  unfolding Valid_def
  by (auto elim: assignE)

theorem Valid_havoc:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. \<forall>v. Q (s(var := v)) tr} var ::= * {Q}"
  unfolding Valid_def
  by (auto elim: HavocE)

theorem Valid_assume:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. b s \<longrightarrow> Q s tr} Assume b {Q}"
  unfolding Valid_def
  by (auto elim: AssumeE)

theorem Valid_send:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. Q s (tr @ [OutBlock ch (e s)]) \<and>
              (\<forall>d::real>0. Q s (tr @ [WaitBlk d (\<lambda>_. State s) ({ch}, {}), OutBlock ch (e s)])) \<and>
              Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({ch}, {})])}
       Cm (ch[!]e) {Q}"
  unfolding Valid_def
  by (auto elim: sendE)

theorem Valid_receive:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. (\<forall>v. Q (s(var := v)) (tr @ [InBlock ch v])) \<and>
              (\<forall>d::real>0. \<forall>v. Q (s(var := v))
                (tr @ [WaitBlk d (\<lambda>_. State s) ({}, {ch}), InBlock ch v])) \<and>
              Q s (tr @ [WaitBlk \<infinity> (\<lambda>_. State s) ({}, {ch})])}
       Cm (ch[?]var) {Q}"
  unfolding Valid_def
  by (auto elim: receiveE)

theorem Valid_seq:
  "\<Turnstile>\<^sub>H\<^sub>L {P} c1 {Q} \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {Q} c2 {R} \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P} c1; c2 {R}"
  unfolding Valid_def
  apply (auto elim!: seqE) by fastforce

theorem Valid_rep:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {P} c {P}"
  shows "\<Turnstile>\<^sub>H\<^sub>L {P} Rep c {P}"
proof -
  have "big_step p s1 tr2 s2 \<Longrightarrow> p = Rep c \<Longrightarrow> \<forall>tr1. P s1 tr1 \<longrightarrow> P s2 (tr1 @ tr2)" for p s1 s2 tr2
    apply (induct rule: big_step.induct, auto)
    by (metis Valid_def append.assoc assms)
  then show ?thesis
    using assms unfolding Valid_def by auto
qed

theorem Valid_ichoice:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {P1} c1 {Q}"
    and "\<Turnstile>\<^sub>H\<^sub>L {P2} c2 {Q}"
  shows "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s tr. P1 s tr \<and> P2 s tr} IChoice c1 c2 {Q}"
  using assms unfolding Valid_def by (auto elim: ichoiceE)

theorem Valid_ichoice_sp:
  assumes "\<Turnstile>\<^sub>H\<^sub>L {P} c1 {Q1}"
    and "\<Turnstile>\<^sub>H\<^sub>L {P} c2 {Q2}"
  shows "\<Turnstile>\<^sub>H\<^sub>L {P} IChoice c1 c2 {\<lambda>s tr. Q1 s tr \<or> Q2 s tr}"
  using assms unfolding Valid_def by (auto elim: ichoiceE)


subsection \<open>Assertions on traces\<close>
type_synonym tassn = "trace \<Rightarrow> bool"

definition entails_tassn :: "tassn \<Rightarrow> tassn \<Rightarrow> bool" (infixr "\<Longrightarrow>\<^sub>t" 25) where
  "(P \<Longrightarrow>\<^sub>t Q) \<longleftrightarrow> (\<forall>tr. P tr \<longrightarrow> Q tr)"

lemma entails_tassn_refl [simp]:
  "P \<Longrightarrow>\<^sub>t P"
  unfolding entails_tassn_def by auto

lemma entails_tassn_trans:
  "(P \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (Q \<Longrightarrow>\<^sub>t R) \<Longrightarrow> (P \<Longrightarrow>\<^sub>t R)"
  unfolding entails_tassn_def by auto

lemma entails_tassn_ex_pre:
  "(\<And>x. P x \<Longrightarrow>\<^sub>t Q) \<Longrightarrow> (\<lambda>tr. (\<exists>x. P x tr)) \<Longrightarrow>\<^sub>t Q"
  by (auto simp add: entails_tassn_def)

lemma entails_tassn_ex_post:
  "(\<exists>x. P \<Longrightarrow>\<^sub>t Q x) \<Longrightarrow> P \<Longrightarrow>\<^sub>t (\<lambda>tr. (\<exists>x. Q x tr))"
  by (auto simp add: entails_tassn_def)

definition emp_assn :: "tassn" ("emp\<^sub>t") where
  "emp\<^sub>t = (\<lambda>tr. tr = [])"

definition join_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@\<^sub>t" 65) where
  "P @\<^sub>t Q = (\<lambda>tr. \<exists>tr1 tr2. P tr1 \<and> Q tr2 \<and> tr = tr1 @ tr2)"

definition magic_wand_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "@-" 65) where
  "Q @- P = (\<lambda>tr. \<forall>tr1. Q tr1 \<longrightarrow> P (tr @ tr1))"

definition all_assn :: "('a \<Rightarrow> tassn) \<Rightarrow> tassn" (binder "\<forall>\<^sub>t" 10) where
  "(\<forall>\<^sub>tv. P v) = (\<lambda>tr. \<forall>v. P v tr)"

definition ex_assn :: "('a \<Rightarrow> tassn) \<Rightarrow> tassn" (binder "\<exists>\<^sub>t" 10) where
  "(\<exists>\<^sub>tv. P v) = (\<lambda>tr. \<exists>v. P v tr)"

definition conj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<and>\<^sub>t" 35) where
  "(P \<and>\<^sub>t Q) = (\<lambda>tr. P tr \<and> Q tr)"

definition disj_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<or>\<^sub>t" 25) where
  "(P \<or>\<^sub>t Q) = (\<lambda>tr. P tr \<or> Q tr)"

definition imp_assn :: "tassn \<Rightarrow> tassn \<Rightarrow> tassn" (infixr "\<longrightarrow>\<^sub>t" 25) where
  "(P \<longrightarrow>\<^sub>t Q) = (\<lambda>tr. P tr \<longrightarrow> Q tr)"

definition pure_assn :: "bool \<Rightarrow> tassn" ("\<up>") where
  "\<up>b = (\<lambda>_. b)"

inductive out_assn :: "gstate \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("Out\<^sub>t") where
  "Out\<^sub>t s ch v [OutBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> Out\<^sub>t s ch v [WaitBlk (ereal d) (\<lambda>_. s) ({ch}, {}), OutBlock ch v]"
| "Out\<^sub>t s ch v [WaitBlk \<infinity> (\<lambda>_. s) ({ch}, {})]"

inductive in_assn :: "gstate \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> tassn" ("In\<^sub>t") where
  "In\<^sub>t s ch v [InBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> In\<^sub>t s ch v [WaitBlk (ereal d) (\<lambda>_. s) ({}, {ch}), InBlock ch v]"
| "In\<^sub>t s ch v [WaitBlk \<infinity> (\<lambda>_. s) ({}, {ch})]"

inductive io_assn :: "cname \<Rightarrow> real \<Rightarrow> tassn" ("IO\<^sub>t") where
  "IO\<^sub>t ch v [IOBlock ch v]"

inductive wait_assn :: "real \<Rightarrow> (real \<Rightarrow> gstate) \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Wait\<^sub>t") where
  "d > 0 \<Longrightarrow> Wait\<^sub>t d p rdy [WaitBlk d (\<lambda>\<tau>. p \<tau>) rdy]"
| "d \<le> 0 \<Longrightarrow> Wait\<^sub>t d p rdy []"

lemma emp_unit_left [simp]:
  "(emp\<^sub>t @\<^sub>t P) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right [simp]:
  "(P @\<^sub>t emp\<^sub>t) = P"
  unfolding join_assn_def emp_assn_def by auto

lemma emp_unit_right':
  "P = (P @\<^sub>t emp\<^sub>t) "
  unfolding join_assn_def emp_assn_def by auto

lemma join_assoc:
  "(P @\<^sub>t Q) @\<^sub>t R = P @\<^sub>t (Q @\<^sub>t R)"
  unfolding join_assn_def by fastforce

lemma entails_mp_emp:
  "emp\<^sub>t \<Longrightarrow>\<^sub>t P @- P"
  unfolding entails_tassn_def emp_assn_def magic_wand_assn_def by auto

lemma entails_mp:
  "Q \<Longrightarrow>\<^sub>t P @- (Q @\<^sub>t P)"
  unfolding entails_tassn_def magic_wand_assn_def join_assn_def by auto

lemma magic_wand_mono:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> (R @- P) \<Longrightarrow>\<^sub>t (R @- Q)"
  unfolding entails_tassn_def magic_wand_assn_def by auto

definition false_assn :: "tassn" ("false\<^sub>A") where
  "false_assn tr = False"

lemma false_assn_entails [simp]:
  "false\<^sub>A \<Longrightarrow>\<^sub>t P"
  by (simp add: entails_tassn_def false_assn_def)

lemma pure_assn_entails [simp]:
  "(\<up>b \<and>\<^sub>t P \<Longrightarrow>\<^sub>t Q) = (b \<longrightarrow> P \<Longrightarrow>\<^sub>t Q)"
  unfolding entails_tassn_def conj_assn_def pure_assn_def by auto

lemma entails_tassn_cancel_left:
  "Q \<Longrightarrow>\<^sub>t R \<Longrightarrow> P @\<^sub>t Q \<Longrightarrow>\<^sub>t P @\<^sub>t R"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_cancel_left_emp:
  "Q \<Longrightarrow>\<^sub>t emp\<^sub>t  \<Longrightarrow> P @\<^sub>t Q \<Longrightarrow>\<^sub>t P "
  by (auto simp add: entails_tassn_def join_assn_def emp_assn_def)

lemma entails_tassn_cancel_right:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P @\<^sub>t R \<Longrightarrow>\<^sub>t Q @\<^sub>t R"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_cancel_both:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> R \<Longrightarrow>\<^sub>t S \<Longrightarrow> P @\<^sub>t R \<Longrightarrow>\<^sub>t Q @\<^sub>t S"
  by (auto simp add: entails_tassn_def join_assn_def)

lemma entails_tassn_conj:
  "P \<Longrightarrow>\<^sub>t Q \<Longrightarrow> P \<Longrightarrow>\<^sub>t R \<Longrightarrow> P \<Longrightarrow>\<^sub>t (Q \<and>\<^sub>t R)"
  by (auto simp add: entails_tassn_def conj_assn_def)

lemma entails_tassn_exI:
  "P \<Longrightarrow>\<^sub>t Q x \<Longrightarrow> P \<Longrightarrow>\<^sub>t (\<exists>\<^sub>t x. Q x)"
  unfolding ex_assn_def entails_tassn_def by auto

lemma conj_join_distrib [simp]:
  "(\<up>b \<and>\<^sub>t P) @\<^sub>t Q = (\<up>b \<and>\<^sub>t (P @\<^sub>t Q))"
  by (auto simp add: join_assn_def conj_assn_def pure_assn_def)

lemma conj_join_distrib2 [simp]:
  "(\<lambda>tr. b \<and> P tr) @\<^sub>t Q = (\<up>b \<and>\<^sub>t (P @\<^sub>t Q))"
  by (auto simp add: pure_assn_def conj_assn_def join_assn_def)

lemma wait_le_zero [simp]:
  "d \<le> 0 \<Longrightarrow> Wait\<^sub>t d p rdy = emp\<^sub>t"
  apply (rule ext) subgoal for tr
    apply auto
     apply (cases rule: wait_assn.cases)
    apply (auto simp add: emp_assn_def)
    by (auto intro: wait_assn.intros)
  done

inductive ode_inv_assn :: "(state \<Rightarrow> bool) \<Rightarrow> tassn" where
  "\<forall>t\<in>{0..d::real}. f (p t) \<Longrightarrow> ode_inv_assn f [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]"

inductive_cases ode_inv_assn_elim: "ode_inv_assn f tr"

lemma ode_inv_assn_implie: "ode_inv_assn c [WaitBlk (ereal d) (\<lambda>\<tau>. State (p \<tau>)) ({}, {})] \<Longrightarrow>
       \<forall>t\<in>{0..d}. c (p t)"
  apply (elim ode_inv_assn_elim)
  apply auto
  subgoal for d p' t
    apply (frule WaitBlk_cong)
    apply (frule WaitBlk_cong2)
    by auto
  done

text \<open>Simpler forms of weakest precondition\<close>

theorem Valid_send':
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s. Out\<^sub>t (State s) ch (e s) @- Q s}
       Cm (ch[!]e)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send)
  unfolding entails_def magic_wand_assn_def
  by (auto intro: out_assn.intros)

theorem Valid_receive':
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s. \<forall>\<^sub>tv. In\<^sub>t (State s) ch v @- Q (s(var := v))}
       Cm (ch[?]var)
      {Q}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def magic_wand_assn_def all_assn_def
  by (metis fun_upd_triv in_assn.intros)

text \<open>Strongest postcondition forms\<close>

theorem Valid_assign_sp:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P s t}
       Assign var e
      {\<lambda>s t. \<exists>x. s var = e (s(var := x)) \<and> P (s(var := x)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_assign)
  apply (auto simp add: entails_def)
  subgoal for s tr
    apply (rule exI[where x="s var"])
    by auto
  done

theorem Valid_havoc_sp:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P s t}
       Havoc var 
      {\<lambda>s t. \<exists>x. P (s(var := x)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_havoc)
  apply (auto simp add: entails_def)
  subgoal for s tr
    by (metis fun_upd_triv)
  done

theorem Valid_send_sp:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P s t}
       Cm (ch[!]e)
     {\<lambda>s t. (P s @\<^sub>t Out\<^sub>t (State s) ch (e s)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_receive_sp:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P s t}
       Cm (ch[?]var)
      {\<lambda>s t. \<exists>x v. (\<up>(s var = v) \<and>\<^sub>t (P(s(var := x)) @\<^sub>t In\<^sub>t (State (s(var := x))) ch v)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def
  apply (auto simp add: join_assn_def)
  subgoal for s tr v
    apply (rule exI[where x="s var"])
    apply (rule exI[where x=v])
    apply (auto simp add: conj_assn_def pure_assn_def)
    apply (rule exI[where x=tr]) by (auto intro: in_assn.intros)
  subgoal for s tr d v
    apply (rule exI[where x="s var"])
    apply (rule exI[where x=v])
    apply (auto simp add: conj_assn_def pure_assn_def)
    apply (rule exI[where x=tr])
    apply auto apply (rule in_assn.intros) by auto
  subgoal for s tr
    apply (rule exI[where x="s var"])
    apply (auto simp add: conj_assn_def pure_assn_def)
    apply (rule exI[where x=tr])
    apply auto by (rule in_assn.intros)
  done

theorem Valid_assume_sp:
   "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. P s t} Assume b {\<lambda>s t. b s \<and> P s t}"
  unfolding Valid_def
  by (metis AssumeE self_append_conv)

theorem Valid_if_split:
  assumes "b \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P1} c {Q1}"
    and "\<not>b \<Longrightarrow> \<Turnstile>\<^sub>H\<^sub>L {P2} c {Q2}"
  shows "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. if b then P1 s t else P2 s t}
             c
            {\<lambda>s t. if b then Q1 s t else Q2 s t}"
  using assms unfolding Valid_def
  by auto

theorem Valid_assign_sp_st:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> P s t}
        x ::= e
      {\<lambda>s t. s = st(x := e st) \<and> P st t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_assign)
  by (auto simp add: entails_def)

theorem Valid_havoc_sp_st:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> P s t}
        x ::= *
      {\<lambda>s t. \<exists>v. s = st(x := v) \<and> P st t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_havoc)
  by (auto simp add: entails_def)

theorem Valid_assign_sp_bst:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> b s \<and> P s t}
        x ::= *
      {\<lambda>s t. \<exists>v. s = st(x := v) \<and> b st \<and> P st t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_havoc)
  by (auto simp add: entails_def)

theorem Valid_send_sp_st:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> P s t}
       Cm (ch[!]e)
      {\<lambda>s t. s = st \<and> (P st @\<^sub>t Out\<^sub>t (State st) ch (e st)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_send_sp_bst:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> b s \<and> P s t}
       Cm (ch[!]e)
      {\<lambda>s t. s = st \<and> b s \<and> (P st @\<^sub>t Out\<^sub>t (State st) ch (e st)) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_send')
  by (auto simp add: entails_def magic_wand_assn_def join_assn_def)

theorem Valid_receive_sp_st:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> P s t}
        Cm (ch[?]var)
      {\<lambda>s t. \<exists>v. s = st(var := v) \<and> (P st @\<^sub>t In\<^sub>t (State st) ch v) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def
  apply (auto simp add: all_assn_def magic_wand_assn_def emp_assn_def join_assn_def)
  subgoal for tr v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    by (simp add: in_assn.intros)
  subgoal for tr d v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    using in_assn.intros(2) by auto
  subgoal for tr
    apply (rule exI[where x="st var"])
    apply auto apply (rule exI[where x=tr])
    by (metis in_assn.intros(3) infinity_ereal_def)
  done

theorem Valid_receive_sp_bst:
  "\<Turnstile>\<^sub>H\<^sub>L {\<lambda>s t. s = st \<and> b s \<and> P s t}
        Cm (ch[?]var)
      {\<lambda>s t. \<exists>v. s = st(var := v) \<and> b st \<and> (P st @\<^sub>t In\<^sub>t (State st) ch v) t}"
  apply (rule Valid_weaken_pre)
   prefer 2 apply (rule Valid_receive)
  unfolding entails_def
  apply (auto simp add: all_assn_def magic_wand_assn_def emp_assn_def join_assn_def)
  subgoal for tr v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    by (simp add: in_assn.intros)
  subgoal for tr d v
    apply (rule exI[where x=v])
    apply auto apply (rule exI[where x=tr])
    using in_assn.intros(2) by auto
  subgoal for tr
    apply (rule exI[where x="st var"])
    apply auto apply (rule exI[where x=tr])
    by (metis in_assn.intros(3) infinity_ereal_def)
  done


subsection \<open>Rules for internal and external choice\<close>

text \<open>Additional assertions\<close>

inductive inrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Inrdy\<^sub>t") where
  "Inrdy\<^sub>t s ch v rdy [InBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> Inrdy\<^sub>t s ch v rdy [WaitBlk d (\<lambda>_. State s) rdy, InBlock ch v]"

inductive outrdy_assn :: "state \<Rightarrow> cname \<Rightarrow> real \<Rightarrow> rdy_info \<Rightarrow> tassn" ("Outrdy\<^sub>t") where
  "Outrdy\<^sub>t s ch v rdy [OutBlock ch v]"
| "(d::real) > 0 \<Longrightarrow> Outrdy\<^sub>t s ch v rdy [WaitBlk d (\<lambda>_. State s) rdy, OutBlock ch v]"


end
