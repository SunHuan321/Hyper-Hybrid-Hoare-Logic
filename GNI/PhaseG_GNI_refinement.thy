theory PhaseG_GNI_refinement
  imports PhaseG_GNI_hybrid
begin

section \<open>Reverse witness coverage for GNI refinement\<close>

definition gni_by ::
  "('a \<Rightarrow> 'h) \<Rightarrow> ('a \<Rightarrow> 'l) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "gni_by high low obs S \<longleftrightarrow>
    (\<forall>u\<in>S. \<forall>v\<in>S. low u = low v \<longrightarrow>
      (\<exists>w\<in>S. high w = high u \<and> low w = low v \<and> obs w = obs v))"

definition obs_match ::
  "('c \<Rightarrow> 'h) \<Rightarrow> ('c \<Rightarrow> 'l) \<Rightarrow> ('c \<Rightarrow> 'o) \<Rightarrow>
    ('a \<Rightarrow> 'h) \<Rightarrow> ('a \<Rightarrow> 'l) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow>
    'c \<Rightarrow> 'a \<Rightarrow> bool" where
  "obs_match hc lc oc ha la oa c a \<longleftrightarrow>
    hc c = ha a \<and> lc c = la a \<and> oc c = oa a"

theorem gni_by_reverse_witness_transfer:
  assumes abstract: "gni_by ha la oa A"
    and forward: "\<And>c. c \<in> C \<Longrightarrow>
      \<exists>a\<in>A. obs_match hc lc oc ha la oa c a"
    and reverse: "\<And>a. a \<in> A \<Longrightarrow>
      \<exists>c\<in>C. obs_match hc lc oc ha la oa c a"
  shows "gni_by hc lc oc C"
proof (unfold gni_by_def, rule ballI, rule ballI, rule impI)
  fix c1 c2
  assume c1: "c1 \<in> C" and c2: "c2 \<in> C" and low: "lc c1 = lc c2"
  from forward[OF c1] obtain a1 where a1: "a1 \<in> A"
    and r1: "obs_match hc lc oc ha la oa c1 a1" by blast
  from forward[OF c2] obtain a2 where a2: "a2 \<in> A"
    and r2: "obs_match hc lc oc ha la oa c2 a2" by blast
  have alow: "la a1 = la a2" using low r1 r2 unfolding obs_match_def by simp
  from abstract[unfolded gni_by_def, rule_format, OF a1 a2 alow]
  obtain a3 where a3: "a3 \<in> A" and ah: "ha a3 = ha a1"
    and al: "la a3 = la a2" and ao: "oa a3 = oa a2" by blast
  from reverse[OF a3] obtain c3 where c3: "c3 \<in> C"
    and r3: "obs_match hc lc oc ha la oa c3 a3" by blast
  have h: "hc c3 = hc c1" using r1 r3 ah unfolding obs_match_def by simp
  have l: "lc c3 = lc c2" using r2 r3 al unfolding obs_match_def by simp
  have o: "oc c3 = oc c2" using r2 r3 ao unfolding obs_match_def by simp
  show "\<exists>w\<in>C. hc w = hc c1 \<and> lc w = lc c2 \<and> oc w = oc c2"
    by (rule_tac x=c3 in bexI) (simp_all add: c3 h l o)
qed

lemma gni_obs_c_as_gni_by:
  "gni_obs_c hi lo l S =
    gni_by (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo)
      (low_obs_c l) S"
  by (simp add: gni_obs_c_def gni_by_def)

corollary gni_obs_c_reverse_witness_transfer:
  assumes abstract: "gni_obs_c hi lo l A"
    and forward: "\<And>c. c \<in> C \<Longrightarrow> \<exists>a\<in>A.
      lproj c hi = lproj a hi \<and> lproj c lo = lproj a lo
      \<and> low_obs_c l c = low_obs_c l a"
    and reverse: "\<And>a. a \<in> A \<Longrightarrow> \<exists>c\<in>C.
      lproj c hi = lproj a hi \<and> lproj c lo = lproj a lo
      \<and> low_obs_c l c = low_obs_c l a"
  shows "gni_obs_c hi lo l C"
proof -
  have g: "gni_by (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo)
    (low_obs_c l) A" using abstract by (simp add: gni_obs_c_as_gni_by)
  have f: "\<And>c. c \<in> C \<Longrightarrow> \<exists>a\<in>A.
    obs_match (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo) (low_obs_c l)
      (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo) (low_obs_c l) c a"
    using forward unfolding obs_match_def by blast
  have r: "\<And>a. a \<in> A \<Longrightarrow> \<exists>c\<in>C.
    obs_match (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo) (low_obs_c l)
      (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo) (low_obs_c l) c a"
    using reverse unfolding obs_match_def by blast
  have "gni_by (\<lambda>\<phi>. lproj \<phi> hi) (\<lambda>\<phi>. lproj \<phi> lo)
    (low_obs_c l) C"
    by (rule gni_by_reverse_witness_transfer[OF g f r])
  then show ?thesis by (simp add: gni_obs_c_as_gni_by)
qed

end
