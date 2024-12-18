theory Logic
  imports Language
begin

subsection \<open>Hyper assertions\<close>

type_synonym 'a hyperassertion = "('a set \<Rightarrow> bool)"

definition entails where
  "entails A B \<longleftrightarrow> (\<forall>S. A S \<longrightarrow> B S)"

lemma entails_refl:
  "entails A A"
  by (simp add: entails_def)

lemma entailsI:
  assumes "\<And>S. A S \<Longrightarrow> B S"
  shows "entails A B"
  by (simp add: assms entails_def)

lemma entailsE:
  assumes "entails A B"
      and "A x"
    shows "B x"
  by (meson assms(1) assms(2) entails_def)

lemma bientails_equal:
  assumes "entails A B"
      and "entails B A"
    shows "A = B"
proof (rule ext)
  fix S show "A S = B S"
    by (meson assms(1) assms(2) entailsE)
qed

lemma entails_trans:
  assumes "entails A B"
      and "entails B C"
    shows "entails A C"
  by (metis assms(1) assms(2) entails_def)

definition setify_prop where
  "setify_prop b = {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. b \<sigma>\<^sub>p}"

lemma sem_assume_setify:
  "sem (Assume b) S = S \<inter> setify_prop b" (is "?A = ?B")
proof -
  have "\<And>\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?A \<longleftrightarrow> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?B"
  proof -
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p l
    have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?A \<longleftrightarrow> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> b \<sigma>\<^sub>p"
      by (simp add: assume_sem)
    then show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?A \<longleftrightarrow> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> ?B"
      by (simp add: setify_prop_def)
  qed
  then show ?thesis
    by auto
qed

definition over_approx :: "'a set \<Rightarrow> 'a hyperassertion" where
  "over_approx P S \<longleftrightarrow> S \<subseteq> P"

definition lower_closed :: "'a hyperassertion \<Rightarrow> bool" where
  "lower_closed P \<longleftrightarrow> (\<forall>S S'. P S \<and> S' \<subseteq> S \<longrightarrow> P S')"

lemma over_approx_lower_closed:
  "lower_closed (over_approx P)"
  by (metis (full_types) lower_closed_def order_trans over_approx_def)

definition under_approx :: "'a set \<Rightarrow> 'a hyperassertion" where
  "under_approx P S \<longleftrightarrow> P \<subseteq> S"

definition upper_closed :: "'a hyperassertion \<Rightarrow> bool" where
  "upper_closed P \<longleftrightarrow> (\<forall>S S'. P S \<and> S \<subseteq> S' \<longrightarrow> P S')"

lemma under_approx_upper_closed:
  "upper_closed (under_approx P)"
  by (metis (no_types, lifting) order.trans under_approx_def upper_closed_def)

definition closed_by_union :: "'a hyperassertion \<Rightarrow> bool" where
  "closed_by_union P \<longleftrightarrow> (\<forall>S S'. P S \<and> P S' \<longrightarrow> P (S \<union> S'))"

lemma closed_by_unionI:
  assumes "\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (a \<union> b)"
  shows "closed_by_union P"
  by (simp add: assms closed_by_union_def)

lemma closed_by_union_over:
  "closed_by_union (over_approx P)"
  by (simp add: closed_by_union_def over_approx_def)

lemma closed_by_union_under:
  "closed_by_union (under_approx P)"
  by (simp add: closed_by_union_def sup.coboundedI1 under_approx_def)

definition conj where
  "conj P Q S \<longleftrightarrow> P S \<and> Q S"

lemma entail_conj:
  assumes "entails A B"
  shows "entails A (conj A B)"
  by (metis (full_types) assms conj_def entails_def)

lemma entail_conj_weaken:
  "entails (conj A B) A"
  by (simp add: conj_def entails_def)

definition disj where
  "disj P Q S \<longleftrightarrow> P S \<or> Q S"

definition exists :: "('c \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "exists P S \<longleftrightarrow> (\<exists>x. P x S)"

definition forall :: "('c \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "forall P S \<longleftrightarrow> (\<forall>x. P x S)"

lemma over_inter:
  "entails (over_approx (P \<inter> Q)) (conj (over_approx P) (over_approx Q))"
  by (simp add: conj_def entails_def over_approx_def)

lemma over_union:
  "entails (disj (over_approx P) (over_approx Q)) (over_approx (P \<union> Q))"
  by (metis disj_def entailsI le_supI1 le_supI2 over_approx_def)

lemma under_union:
  "entails (under_approx (P \<union> Q)) (disj (under_approx P) (under_approx Q))"
  by (simp add: disj_def entails_def under_approx_def)

lemma under_inter:
  "entails (conj (under_approx P) (under_approx Q)) (under_approx (P \<inter> Q))"
  by (simp add: conj_def entails_def le_infI1 under_approx_def)

text \<open>Operator \<open>\<otimes>\<close>\<close>
definition join :: "'a hyperassertion \<Rightarrow> 'a hyperassertion \<Rightarrow> 'a hyperassertion" where
  "join A B S \<longleftrightarrow> (\<exists>SA SB. A SA \<and> B SB \<and> S = SA \<union> SB)"

definition general_join :: "('b \<Rightarrow> 'a hyperassertion) \<Rightarrow> 'a hyperassertion" where
  "general_join f S \<longleftrightarrow> (\<exists>F. S = (\<Union>x. F x) \<and> (\<forall>x. f x (F x)))"

lemma general_joinI:
  assumes "S = (\<Union>x. F x)"
      and "\<And>x. f x (F x)"
    shows "general_join f S"
  using assms(1) assms(2) general_join_def by blast

lemma join_closed_by_union:
  assumes "closed_by_union Q"
  shows "join Q Q = Q"
proof
  fix S
  show "join Q Q S \<longleftrightarrow> Q S"
    by (metis assms closed_by_union_def join_def sup_idem)
qed

lemma entails_join_entails:
  assumes "entails A1 B1"
      and "entails A2 B2"
    shows "entails (join A1 A2) (join B1 B2)"
proof (rule entailsI)
  fix S assume "join A1 A2 S"
  then obtain S1 S2 where "A1 S1" "A2 S2" "S = S1 \<union> S2"
    by (metis join_def)
  then show "join B1 B2 S"
    by (metis assms(1) assms(2) entailsE join_def)
qed

text \<open>Operator \<open>\<Otimes>\<close> (for \<open>x \<in> X\<close>)\<close>
definition natural_partition where
  "natural_partition I S \<longleftrightarrow> (\<exists>F. S = (\<Union>n. F n) \<and> (\<forall>n. I n (F n)))"

lemma natural_partitionI:
  assumes "S = (\<Union>n. F n)"
      and "\<And>n. I n (F n)"
    shows "natural_partition I S"
  using assms(1) assms(2) natural_partition_def by blast

lemma natural_partitionE:
  assumes "natural_partition I S"
  obtains F where "S = (\<Union>n. F n)" "\<And>n. I n (F n)"
  by (meson assms natural_partition_def)

subsection \<open>Rules of the Logic\<close>

subsection \<open>Soundness\<close>

text \<open>Hyper-Triples\<close>

type_synonym assn = "(state \<times> trace) set \<Rightarrow> bool"

definition hyper_hoare_triple ("\<Turnstile> {_} _ {_}" [51,0,0] 81) where
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (sem C S))"

lemma hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem C S)"
  shows "\<Turnstile> {P} C {Q}"
  by (simp add: assms hyper_hoare_triple_def)

lemma hyper_hoare_tripleE:
  assumes "\<Turnstile> {P} C {Q}"
      and "P S"
    shows "Q (sem C S)"
  using assms(1) assms(2) hyper_hoare_triple_def
  by metis

lemma consequence_rule:
  assumes "entails P P'"
      and "entails Q' Q"
      and "\<Turnstile> {P'} C {Q'}"
    shows "\<Turnstile> {P} C {Q}"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) entails_def hyper_hoare_triple_def)

lemma skip_rule:
  "\<Turnstile> {P} Skip {P}"
  by (simp add: hyper_hoare_triple_def sem_skip)

lemma assume_rule:
  "\<Turnstile> {(\<lambda>S. P (Set.filter (b \<circ> fst \<circ> snd) S)) } (Assume b) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P (Set.filter (b \<circ> fst \<circ> snd) S)"
  then show "P (sem (Assume b) S)"
    by (simp add: assume_sem)
qed

lemma seq_rule:
  assumes "\<Turnstile> {P} C1 {R}"
    and "\<Turnstile> {R} C2 {Q}"
    shows "\<Turnstile> {P} Seq C1 C2 {Q}"
  using assms(1) assms(2) hyper_hoare_triple_def sem_seq
  by metis

lemma if_rule:
  assumes "\<Turnstile> {P} C1 {Q1}"
      and "\<Turnstile> {P} C2 {Q2}"
    shows "\<Turnstile> {P} IChoice C1 C2 {join Q1 Q2}"
  by (metis (full_types) assms(1) assms(2) hyper_hoare_triple_def join_def sem_if)

lemma assign_rule:
  "\<Turnstile> {(\<lambda>S. P {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S }) } (Assign x e) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := e \<sigma>\<^sub>p), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S }"
  then show "P (sem (Assign x e) S)" using sem_assign
    by metis
qed


lemma havoc_rule:
  "\<Turnstile> {(\<lambda>S. P {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := v), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S})} (Havoc x) {P}"
proof (rule hyper_hoare_tripleI)
  fix S assume "P {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(x := v), l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}"
  then show "P (sem (Havoc x) S)" using sem_havoc by metis
qed

lemma send_rule:
  "\<Turnstile> {(\<lambda>S. P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {}), OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}))} (Cm (ch[!]e)) {P}"
proof (rule hyper_hoare_tripleI)
  fix S
  assume "P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {}), OutBlock ch (e \<sigma>\<^sub>p)]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d. (d::real) > 0 \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({ch}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S})"
  then show "P (sem (Cm (ch[!]e)) S)"
    using sem_send by metis
qed

lemma recv_rule:
  "\<Turnstile> {(\<lambda>S. P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch}), InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d v. (d::real) > 0 
  \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S}))} (Cm (ch[?]var)) {P}"
proof(rule hyper_hoare_tripleI)
  fix S
  assume "P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l v. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p(var := v), l @ [WaitBlk d (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch}), InBlock ch v]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l d v. (d::real) > 0 
  \<and> (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S} \<union>
  {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l @ [WaitBlk \<infinity> (\<lambda>_. State \<sigma>\<^sub>p) ({}, {ch})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S})"
  then show "P (sem (Cm (ch[?]var)) S)"
    using sem_recv by metis
qed

text \<open>Loops\<close>

lemma indexed_invariant_then_power:
  assumes "\<And>n. hyper_hoare_triple (I n) C (I (Suc n))"
      and "I 0 S"
  shows "I n (iterate_sem n C S)"
  using assms
proof (induct n arbitrary: S)
next
  case (Suc n)
  then have "I n (iterate_sem n C S)"
    by blast
  then have "I (Suc n) (sem C (iterate_sem n C S))"
    using Suc.prems(1) hyper_hoare_tripleE by blast
  then show ?case
    by (simp add: Suc.hyps Suc.prems(1))
qed (auto)

lemma indexed_invariant_then_power_bounded:
  assumes "\<And>m. m < n \<Longrightarrow> hyper_hoare_triple (I m) C (I (Suc m))"
      and "I 0 S"
  shows "I n (iterate_sem n C S)"
  using assms
proof (induct n arbitrary: S)
next
  case (Suc n)
  then have "I n (iterate_sem n C S)"
    using less_Suc_eq by presburger
  then have "I (Suc n) (sem C (iterate_sem n C S))"
    using Suc.prems(1) hyper_hoare_tripleE by blast
  then show ?case
    by (simp add: Suc.hyps Suc.prems(1))
qed (auto)

lemma while_rule:
  assumes "\<And>n. hyper_hoare_triple (I n) C (I (Suc n))"
  shows "hyper_hoare_triple (I 0) (Rep C) (natural_partition I)"
proof (rule hyper_hoare_tripleI)
  fix S assume asm0: "I 0 S"
  show "natural_partition I (sem (Rep C) S)"
  proof (rule natural_partitionI)
    show "sem (Rep C) S = \<Union> (range (\<lambda>n. iterate_sem n C S))"
      by (simp add: sem_while)
    fix n show "I n (iterate_sem n C S)"
      by (simp add: asm0 assms indexed_invariant_then_power)
  qed
qed

lemma rule_exists:
  assumes "\<And>x. \<Turnstile> {P x} C {Q x}"
  shows "\<Turnstile> {exists P} C {exists Q}"
  by (metis assms exists_def hyper_hoare_triple_def)

text \<open>continous\<close>

lemma rule_cont:
  "\<Turnstile> {(\<lambda>S. P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> b \<sigma>\<^sub>p} \<union> 
  {(\<sigma>\<^sub>l, p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l p d. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> d > 0 \<and> 
  ODEsol ode p d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and> p 0 = \<sigma>\<^sub>p}))} (Cont ode b) {P}"
proof(rule hyper_hoare_tripleI)
  fix S 
  assume "P ({(\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) |\<sigma>\<^sub>l \<sigma>\<^sub>p l. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> \<not> b \<sigma>\<^sub>p} \<union> 
  {(\<sigma>\<^sub>l, p d, l @ [WaitBlk d (\<lambda>\<tau>. State (p \<tau>)) ({}, {})]) |\<sigma>\<^sub>l \<sigma>\<^sub>p l p d. (\<sigma>\<^sub>l, \<sigma>\<^sub>p, l) \<in> S \<and> d > 0 \<and> 
  ODEsol ode p d \<and> (\<forall>t. t \<ge> 0 \<and> t < d \<longrightarrow> b (p t)) \<and> \<not>b (p d) \<and> p 0 = \<sigma>\<^sub>p})"
  then show "P (sem (Cont ode b) S)"
    using sem_ode by metis
qed


subsection \<open>Validity for parallel programs\<close>

subsection \<open>Basic elimination rules\<close>

named_theorems sync_elims

lemma combine_blocks_pairE [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. ch1 = ch2 \<Longrightarrow> v1 = v2 \<Longrightarrow> (ch_type1 = In \<and> ch_type2 = Out \<or> ch_type1 = Out \<and> ch_type2 = In) \<Longrightarrow>
   tr = IOBlock ch1 v1 # tr' \<Longrightarrow> combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<in> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE1' [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow> ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (CommBlock ch_type2 ch2 v2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_pairE2' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<in> comms \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   ch1 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk d2 p2 rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_unpairE3' [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   ch2 \<notin> comms \<Longrightarrow>
   (\<And>tr'. tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_waitE1 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   \<not>compat_rdy rdy1 rdy2 \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  then show ?case
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  then show ?case 
    by (metis WaitBlk_cong list.inject)
qed (auto)

lemma combine_blocks_waitE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d p1 rdy1 # tr1) (WaitBlk d p2 rdy2 # tr2) tr \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms' blks1 blks2 blks rdy1' rdy2' hist hist1 hist2 rdy t)
  have a: "d = t" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  have b: "WaitBlk d (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine) using combine_blocks_wait1(2,3) by auto 
  show ?case
    apply (rule combine_blocks_wait1)
    unfolding b using combine_blocks_wait1(4) unfolding a combine_blocks_wait1(7,8)
    by (auto simp add: combine_blocks_wait1(1,5))
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have a: "d = ereal t1" "d = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait2(7) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have a: "d = ereal t2" "d = t1"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  show ?case
    using a combine_blocks_wait3(7) by auto
qed (auto)

lemma combine_blocks_waitE3 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d1 \<Longrightarrow> d1 < d2 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms tr1 (WaitBlk (d2 - d1) (\<lambda>t. p2 (t + d1)) rdy2 # tr2) tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have a: "t = ereal d1" "t = d2"
    using combine_blocks_wait1(2,3) WaitBlk_cong by blast+
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms' blks1 t2 t1 hist2 rdy2' blks2 blks rdy1' hist hist1 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'" "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait2(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d2 p2 rdy2 = WaitBlk d2 hist2 rdy2"
    using combine_blocks_wait2(3) unfolding a[symmetric] by auto
  have a3: "WaitBlk d1 p2 rdy2 = WaitBlk d1 hist2 rdy2"
           "WaitBlk (d2 - d1) (\<lambda>\<tau>. p2 (\<tau> + d1)) rdy2 = WaitBlk (d2 - d1) (\<lambda>\<tau>. hist2 (\<tau> + d1)) rdy2"
    using WaitBlk_split[OF a2] combine_blocks_wait2 by auto
  have b: "WaitBlk d1 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk t1 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait2.hyps(2) a(1,4) a3 by auto
  show ?case
    apply (rule combine_blocks_wait2) unfolding a3 b
    using combine_blocks_wait2(4) unfolding combine_blocks_wait2(9,10)
    by (auto simp add: a combine_blocks_wait2(1,5))
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1 blks1 blks2 blks rdy2 hist hist2 rdy)
  have "ereal d1 = t1" "d2 = ereal t2"
    using combine_blocks_wait3(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait3(7,12) by auto
qed (auto)

lemma combine_blocks_waitE4 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow>
   0 < d2 \<Longrightarrow> d2 < d1 \<Longrightarrow>
   compat_rdy rdy1 rdy2 \<Longrightarrow>
   (\<And>tr'. tr = WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) # tr' \<Longrightarrow>
           combine_blocks comms (WaitBlk (d1 - d2) (\<lambda>t. p1 (t + d2)) rdy1 # tr1) tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
proof (induct rule: combine_blocks.cases)
  case (combine_blocks_wait1 comms blks1 blks2 blks rdy1 rdy2 hist hist1 hist2 rdy t)
  have "d1 = t" "ereal d2 = t"
    using combine_blocks_wait1(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait1(10) by auto
next
  case (combine_blocks_wait2 comms blks1 t2 t1 hist2 rdy2 blks2 blks rdy1 hist hist1 rdy)
  have "d1 = ereal t1" "ereal d2 = t2"
    using combine_blocks_wait2(2,3) by (auto simp add: WaitBlk_cong)
  then show ?case
    using combine_blocks_wait2(7,12) by auto
next
  case (combine_blocks_wait3 comms t1 t2 hist1 rdy1' blks1 blks2 blks rdy2' hist hist2 rdy)
  have a: "d1 = t1" "d2 = t2" "rdy1 = rdy1'" "rdy2 = rdy2'"
          "tr1 = blks1" "tr2 = blks2" 
    using combine_blocks_wait3(2,3) using WaitBlk_cong by blast+
  have a2: "WaitBlk d1 p1 rdy1 = WaitBlk d1 hist1 rdy1"
    using combine_blocks_wait3(2) unfolding a[symmetric] by auto
  have a3: "WaitBlk d2 p1 rdy1 = WaitBlk d2 hist1 rdy1"
           "WaitBlk (d1 - d2) (\<lambda>\<tau>. p1 (\<tau> + d2)) rdy1 = WaitBlk (d1 - d2) (\<lambda>\<tau>. hist1 (\<tau> + d2)) rdy1"
    using WaitBlk_split[OF a2] combine_blocks_wait3 by auto
  have b: "WaitBlk d2 (\<lambda>t. ParState (p1 t) (p2 t)) (merge_rdy rdy1 rdy2) =
           WaitBlk d2 (\<lambda>t. ParState (hist1 t) (hist2 t)) (merge_rdy rdy1' rdy2')"
    apply (rule WaitBlk_eq_combine)
    using combine_blocks_wait3 a(2,3) a3 by auto
  show ?case
    apply (rule combine_blocks_wait3) unfolding a3 b
    using combine_blocks_wait3(4) unfolding combine_blocks_wait3(9,10)
    by (auto simp add: a combine_blocks_wait3)
qed (auto)

lemma combine_blocks_emptyE1 [sync_elims]:
  "combine_blocks comms [] [] tr \<Longrightarrow> tr = []"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2 [sync_elims]:
  "combine_blocks comms (WaitBlk d1 p1 rdy1 # tr1) [] tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE2' [sync_elims]:
  "combine_blocks comms [] (WaitBlk d2 p2 rdy2 # tr2) tr \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3 [sync_elims]:
  "combine_blocks comms (CommBlock ch_type1 ch1 v1 # tr1) [] tr \<Longrightarrow>
   (\<And>tr'. ch1 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type1 ch1 v1 # tr' \<Longrightarrow>
           combine_blocks comms tr1 [] tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

lemma combine_blocks_emptyE3' [sync_elims]:
  "combine_blocks comms [] (CommBlock ch_type2 ch2 v2 # tr2) tr \<Longrightarrow>
   (\<And>tr'. ch2 \<notin> comms \<Longrightarrow> tr = CommBlock ch_type2 ch2 v2 # tr' \<Longrightarrow>
           combine_blocks comms [] tr2 tr' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: combine_blocks.cases, auto)

definition par_hyper_hoare_triple ("\<Turnstile>\<^sub>P {_} _ {_}" [51,0,0] 81) where
  "\<Turnstile>\<^sub>P {P} C {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (par_sem C S))"

definition emp_trace_assn :: "(state set \<Rightarrow> bool) \<Rightarrow> assn"
  where "emp_trace_assn P \<Sigma> \<longleftrightarrow> P {fst \<phi> |\<phi>. \<phi> \<in> \<Sigma>} \<and> (\<forall>\<phi>. \<phi> \<in> \<Sigma> \<longrightarrow> snd \<phi> = [])"

definition par_single_state_gassn :: "(state set \<Rightarrow> bool) \<Rightarrow> gstate set \<Rightarrow> bool"
  where "par_single_state_gassn P S \<longleftrightarrow> P {\<sigma>. State \<sigma> \<in> S}"

definition par_single_gassn :: "assn \<Rightarrow> (gstate \<times> trace) set \<Rightarrow> bool"
  where "par_single_gassn Q S = Q {(\<sigma>, l) | \<sigma> l. (State \<sigma>, l) \<in> S}"

definition par_state_gassn :: "(gstate set \<Rightarrow> bool) \<Rightarrow> (gstate set \<Rightarrow> bool) \<Rightarrow> gstate set \<Rightarrow> bool"
  where "par_state_gassn P1 P2 S \<longleftrightarrow> P1 {s1. \<exists>s2. (ParState s1 s2) \<in> S} \<and> P2 {s2. \<exists>s1. (ParState s1 s2) \<in> S}"

lemma par_hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (par_sem C S)"
  shows "\<Turnstile>\<^sub>P {P} C {Q}"
  by (simp add: assms par_hyper_hoare_triple_def)

lemma par_hyper_hoare_tripleE:
  assumes "\<Turnstile>\<^sub>P {P} C {Q}"
      and "P S"
    shows "Q (par_sem C S)"
  using assms(1) assms(2) par_hyper_hoare_triple_def
  by metis

lemma par_consequence_rule:
  assumes "entails P P'"
      and "entails Q' Q"
      and "\<Turnstile>\<^sub>P {P'} C {Q'}"
    shows "\<Turnstile>\<^sub>P {P} C {Q}"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) entails_def par_hyper_hoare_triple_def)

lemma rule_par_single:
  assumes "\<Turnstile> {emp_trace_assn P} C {Q}"
  shows "\<Turnstile>\<^sub>P {par_single_state_gassn P} (Single C) {par_single_gassn Q}"
proof(rule par_hyper_hoare_tripleI)
  fix S
  let ?\<Sigma> = "{(\<sigma>, []) |\<sigma>. State \<sigma> \<in> S}"
  assume "par_single_state_gassn P S"
  then have "P {\<sigma>. State \<sigma> \<in> S}"
    using par_single_state_gassn_def by auto
  then have "emp_trace_assn P ?\<Sigma>"
    using emp_trace_assn_def by auto
  then have "Q (sem C ?\<Sigma>)"
    using assms hyper_hoare_tripleE by blast
  then have "Q {(\<sigma>', l @ l') | \<sigma> \<sigma>' l l'. (\<sigma>, l) \<in> ?\<Sigma> \<and> big_step C \<sigma> l' \<sigma>'}"
    using sem_def by auto
  then have "Q {(\<sigma>', l) | \<sigma> \<sigma>' l. State \<sigma> \<in> S \<and> big_step C \<sigma> l \<sigma>'}"
    by auto
  then show "par_single_gassn Q (par_sem (Single C) S)"
    by (smt (verit, del_insts) Collect_cong Pair_inject gstate.inject(1) mem_Collect_eq 
        par_sem_single par_single_gassn_def)
qed

(*
lemma rule_par_Parallel:
  assumes "\<Turnstile>\<^sub>P {P1} C1 {Q1}"
      and "\<Turnstile>\<^sub>P {P2} C2 {Q2}"
    shows "True"
*)

end
