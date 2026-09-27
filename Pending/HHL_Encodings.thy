theory HHL_Encodings
  imports H3L_Core.ProgramHyperproperties
begin

theorem encoding_HL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))"
proof
  assume hl: "HL P C Q"
  show "hyper_hoare_triple (over_approx P) C (over_approx Q)"
  proof (rule hyper_hoare_tripleI)
    fix S assume "over_approx P S"
    then have sub: "S \<subseteq> P" by (simp add: over_approx_def)
    then have "sem C S \<subseteq> sem C P" by (rule sem_monotonic)
    also have "\<dots> \<subseteq> Q"
    proof
      fix \<phi> assume mem: "\<phi> \<in> sem C P"
      then obtain \<sigma>\<^sub>p tr0 l where src: "(fst \<phi>, \<sigma>\<^sub>p, tr0) \<in> P"
        "big_step C \<sigma>\<^sub>p l (fst (snd \<phi>))" "snd (snd \<phi>) = tr0 @ l"
        by (meson in_sem)
      then show "\<phi> \<in> Q" using hl src(1)
        by (cases "\<phi>"; cases "snd \<phi>") (auto simp: HL_def)
    qed
    finally have "sem C S \<subseteq> Q" .
    then show "over_approx Q (sem C S)" by (simp add: over_approx_def)
  qed
next
  assume ht: "hyper_hoare_triple (over_approx P) C (over_approx Q)"
  show "HL P C Q"
    unfolding HL_def
  proof (intro allI impI)
    fix \<sigma>\<^sub>l \<sigma>\<^sub>p \<sigma>\<^sub>p' tr0 l
    assume p: "(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0) \<in> P" and bs: "big_step C \<sigma>\<^sub>p l \<sigma>\<^sub>p'"
    from p have "over_approx P {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0)}" by (simp add: over_approx_def)
    then have "over_approx Q (sem C {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0)})"
      using ht hyper_hoare_tripleE by blast
    then have "sem C {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0)} \<subseteq> Q" by (simp add: over_approx_def)
    moreover have "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ l) \<in> sem C {(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0)}"
      using in_sem[of "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ l)" C "{(\<sigma>\<^sub>l, \<sigma>\<^sub>p, tr0)}"] bs p by blast
    ultimately show "(\<sigma>\<^sub>l, \<sigma>\<^sub>p', tr0 @ l) \<in> Q" by blast
  qed
qed

subsection \<open>Encoding Incorrectness Logic\<close>

definition IL where
  "IL P C Q \<longleftrightarrow> Q \<subseteq> sem C P"

subsection \<open>Encoding Incorrectness Logic\<close>

definition IL where
  "IL P C Q \<longleftrightarrow> Q \<subseteq> sem C P"

theorem encoding_IL:
  "IL P C Q \<longleftrightarrow> (\<Turnstile> {under_approx P} C {under_approx Q})"
proof
  assume ht: "\<Turnstile> {under_approx P} C {under_approx Q}"
  show "IL P C Q"
  proof -
    have "under_approx P P" by (simp add: under_approx_def)
    then have "under_approx Q (sem C P)"
      using ht hyper_hoare_tripleE by blast
    then show "IL P C Q" by (simp add: IL_def under_approx_def)
  qed
next
  assume il: "IL P C Q"
  show "\<Turnstile> {under_approx P} C {under_approx Q}"
  proof (rule hyper_hoare_tripleI)
    fix S assume sub: "under_approx P S"
    then have ps: "P \<subseteq> S" by (simp add: under_approx_def)
    have qs: "Q \<subseteq> sem C P" using il by (simp add: IL_def)
    have "sem C P \<subseteq> sem C S" using ps by (rule sem_monotonic)
    then have "Q \<subseteq> sem C S" using qs by blast
    then show "under_approx Q (sem C S)" by (simp add: under_approx_def)
  qed
qed

end
