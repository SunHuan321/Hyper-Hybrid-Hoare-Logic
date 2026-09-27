theory PhaseG_Havoc_Syntax
  imports PhaseG_Syntactic
begin

section \<open>Per-state syntactic weakest precondition for Havoc\<close>

text \<open>The fragment excludes raw state functions, pre-existing value binders,
filters, semantic escapes, and ATogether (the union-split postcondition of
IChoice; its havoc-wp needs a two-dimensional preimage construction, left
as documented residual). It permits arbitrarily nested state binders.
Each binder introduces its own real-valued choice binder; the index map
links a state slot to its own choice.\<close>

definition havoc_st :: "var \<Rightarrow> real \<Rightarrow> syn_state \<Rightarrow> syn_state" where
  "havoc_st x v \<phi> = (lproj \<phi>, (pproj \<phi>)(x := v), tproj \<phi>)"

lemma sem_havoc_st:
  "sem (Havoc x) S = {havoc_st x v \<phi> |\<phi> v. \<phi> \<in> S}"
  by (auto simp: sem_havoc havoc_st_def lproj_def pproj_def tproj_def
      split: prod.splits)

fun havoc_hexp_frag :: "hexp \<Rightarrow> bool" where
  "havoc_hexp_frag (EPVar st y) = True"
| "havoc_hexp_frag (ELVar st y) = True"
| "havoc_hexp_frag (EQVar i) = False"
| "havoc_hexp_frag (EConst v) = True"
| "havoc_hexp_frag (ETraceLen st) = True"
| "havoc_hexp_frag (EBinop a f b) = (havoc_hexp_frag a \<and> havoc_hexp_frag b)"
| "havoc_hexp_frag (EFun f a) = havoc_hexp_frag a"
| "havoc_hexp_frag (EPState st e) = False"

fun havoc_frag :: "hassertion \<Rightarrow> bool" where
  "havoc_frag (AConst b) = True"
| "havoc_frag (AComp a cmp b) = (havoc_hexp_frag a \<and> havoc_hexp_frag b)"
| "havoc_frag (ATrace st P) = True"
| "havoc_frag (ATraceRel st1 st2 R) = True"
| "havoc_frag (ASem P) = False"
| "havoc_frag (AForallState A) = havoc_frag A"
| "havoc_frag (AExistsState A) = havoc_frag A"
| "havoc_frag (AForall A) = False"
| "havoc_frag (AExists A) = False"
| "havoc_frag (AAnd A B) = (havoc_frag A \<and> havoc_frag B)"
| "havoc_frag (AOr A B) = (havoc_frag A \<and> havoc_frag B)"
| "havoc_frag (ANot A) = havoc_frag A"
| "havoc_frag (ATogether A1 A2) = False"
| "havoc_frag (AFilter b A) = False"

fun havoc_hexp :: "var \<Rightarrow> nat list \<Rightarrow> hexp \<Rightarrow> hexp" where
  "havoc_hexp x ix (EPVar st y) = (if y = x then EQVar (ix ! st) else EPVar st y)"
| "havoc_hexp x ix (EBinop a f b) =
    EBinop (havoc_hexp x ix a) f (havoc_hexp x ix b)"
| "havoc_hexp x ix (EFun f a) = EFun f (havoc_hexp x ix a)"
| "havoc_hexp x ix E = E"

fun havocS :: "var \<Rightarrow> nat list \<Rightarrow> hassertion \<Rightarrow> hassertion" where
  "havocS x ix (AConst b) = AConst b"
| "havocS x ix (AComp a cmp b) =
    AComp (havoc_hexp x ix a) cmp (havoc_hexp x ix b)"
| "havocS x ix (ATrace st P) = ATrace st P"
| "havocS x ix (ATraceRel st1 st2 R) = ATraceRel st1 st2 R"
| "havocS x ix (ANot A) = ANot (havocS x ix A)"
| "havocS x ix (ATogether A1 A2) = ATogether A1 A2"
| "havocS x ix (AForallState A) =
    AForallState (AForall (havocS x (0 # map Suc ix) A))"
| "havocS x ix (AExistsState A) =
    AExistsState (AExists (havocS x (0 # map Suc ix) A))"
| "havocS x ix (AAnd A B) = AAnd (havocS x ix A) (havocS x ix B)"
| "havocS x ix (AOr A B) = AOr (havocS x ix A) (havocS x ix B)"
| "havocS x ix A = A"

definition havoc_env ::
  "var \<Rightarrow> real list \<Rightarrow> nat list \<Rightarrow> syn_state list \<Rightarrow> syn_state list \<Rightarrow> bool" where
  "havoc_env x vals ix pre post \<longleftrightarrow>
    length pre = length post \<and> length ix = length pre \<and>
    (\<forall>i<length pre. ix ! i < length vals \<and>
       post ! i = havoc_st x (vals ! (ix ! i)) (pre ! i))"

lemma havoc_env_cons:
  assumes env: "havoc_env x vals ix pre post"
  shows "havoc_env x (v # vals) (0 # map Suc ix)
    (\<phi> # pre) (havoc_st x v \<phi> # post)"
  using env unfolding havoc_env_def
  by (auto simp: nth_Cons' nth_map)

lemma havoc_interp:
  assumes frag: "havoc_hexp_frag E" and wf: "wf_hexp (length pre) E"
    and env: "havoc_env x vals ix pre post"
  shows "interp_hexp vals pre (havoc_hexp x ix E) = interp_hexp [] post E"
  using frag wf
proof (induction E)
  case (EPVar st y)
  then show ?case using env unfolding havoc_env_def havoc_st_def
    by (auto simp: pproj_def nth_map split: prod.splits)
next
  case (ELVar st y)
  then show ?case using env unfolding havoc_env_def havoc_st_def
    by (auto simp: lproj_def split: prod.splits)
next
  case (ETraceLen st)
  then show ?case using env unfolding havoc_env_def havoc_st_def
    by (auto simp: tproj_def split: prod.splits)
qed auto

lemma tproj_havoc_st [simp]:
  "tproj (havoc_st x v \<phi>) = tproj \<phi>"
  by (simp add: havoc_st_def tproj_def)

lemma havoc_sat:
  assumes frag: "havoc_frag A" and wf: "wf_hassertion (length pre) A"
    and env: "havoc_env x vals ix pre post"
  shows "sat_hassertion vals pre (havocS x ix A) S =
    sat_hassertion [] post A (sem (Havoc x) S)"
  using frag wf env
proof (induction A arbitrary: vals ix pre post S)
  case (AComp a cmp b)
  then show ?case by (simp add: havoc_interp)
next
  case (ATrace st P)
  then show ?case unfolding havoc_env_def havoc_st_def
    by (auto simp: tproj_def split: prod.splits)
next
  case (AForallState A)
  have ih: "\<And>\<phi> v.
    sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S =
    sat_hassertion [] (havoc_st x v \<phi> # post) A (sem (Havoc x) S)"
  proof -
    fix \<phi> v
    have wf': "wf_hassertion (length (\<phi> # pre)) A"
      using AForallState.prems by simp
    have env': "havoc_env x (v # vals) (0 # map Suc ix)
      (\<phi> # pre) (havoc_st x v \<phi> # post)"
      by (rule havoc_env_cons[OF AForallState.prems(3)])
    show "sat_hassertion (v # vals) (\<phi> # pre)
        (havocS x (0 # map Suc ix) A) S =
      sat_hassertion [] (havoc_st x v \<phi> # post) A (sem (Havoc x) S)"
      by (rule AForallState.IH[OF _ wf' env'])
         (use AForallState.prems in simp)
  qed
  show ?case
  proof (simp only: havocS.simps sat_hassertion.simps, rule iffI)
    assume all: "\<forall>\<phi>\<in>S. \<forall>v. sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S"
    show "\<forall>\<psi>\<in>sem (Havoc x) S. sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)"
    proof (rule ballI)
      fix \<psi> assume "\<psi> \<in> sem (Havoc x) S"
      then obtain \<phi> v where m: "\<phi> \<in> S" and p: "\<psi> = havoc_st x v \<phi>"
        unfolding sem_havoc_st by blast
      from all m ih[of v \<phi>] show "sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)"
        by (simp add: p)
    qed
  next
    assume all: "\<forall>\<psi>\<in>sem (Havoc x) S.
      sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)"
    show "\<forall>\<phi>\<in>S. \<forall>v. sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S"
    proof (intro ballI allI)
      fix \<phi> v assume m: "\<phi> \<in> S"
      have "havoc_st x v \<phi> \<in> sem (Havoc x) S"
        using m unfolding sem_havoc_st by blast
      with all ih[of v \<phi>]
      show "sat_hassertion (v # vals) (\<phi> # pre)
        (havocS x (0 # map Suc ix) A) S" by blast
    qed
  qed
next
  case (AExistsState A)
  have ih: "\<And>\<phi> v.
    sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S =
    sat_hassertion [] (havoc_st x v \<phi> # post) A (sem (Havoc x) S)"
  proof -
    fix \<phi> v
    have wf': "wf_hassertion (length (\<phi> # pre)) A"
      using AExistsState.prems by simp
    have env': "havoc_env x (v # vals) (0 # map Suc ix)
      (\<phi> # pre) (havoc_st x v \<phi> # post)"
      by (rule havoc_env_cons[OF AExistsState.prems(3)])
    show "sat_hassertion (v # vals) (\<phi> # pre)
        (havocS x (0 # map Suc ix) A) S =
      sat_hassertion [] (havoc_st x v \<phi> # post) A (sem (Havoc x) S)"
      by (rule AExistsState.IH[OF _ wf' env'])
         (use AExistsState.prems in simp)
  qed
  show ?case
  proof (simp only: havocS.simps sat_hassertion.simps, rule iffI)
    assume ex: "\<exists>\<phi>\<in>S. \<exists>v. sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S"
    then obtain \<phi> v where m: "\<phi> \<in> S" and sat:
      "sat_hassertion (v # vals) (\<phi> # pre)
        (havocS x (0 # map Suc ix) A) S" by blast
    have mem: "havoc_st x v \<phi> \<in> sem (Havoc x) S"
      using m unfolding sem_havoc_st by blast
    have sat': "sat_hassertion [] (havoc_st x v \<phi> # post) A (sem (Havoc x) S)"
      using sat ih[of v \<phi>] by simp
    show "\<exists>\<psi>\<in>sem (Havoc x) S.
      sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)"
      by (rule bexI[OF _ mem]) (rule sat')
  next
    assume ex: "\<exists>\<psi>\<in>sem (Havoc x) S.
      sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)"
    then obtain \<psi> where mem: "\<psi> \<in> sem (Havoc x) S" and sat:
      "sat_hassertion [] (\<psi> # post) A (sem (Havoc x) S)" by blast
    from mem obtain \<phi> v where m: "\<phi> \<in> S" and p: "\<psi> = havoc_st x v \<phi>"
      unfolding sem_havoc_st by blast
    have sat': "sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S"
      using sat ih[of v \<phi>] by (simp add: p)
    show "\<exists>\<phi>\<in>S. \<exists>v. sat_hassertion (v # vals) (\<phi> # pre)
      (havocS x (0 # map Suc ix) A) S"
      by (rule bexI[OF _ m]) (rule exI[where x=v], rule sat')
  qed
qed (auto simp: havoc_env_def)

theorem denote_havocS:
  assumes frag: "havoc_frag A" and wf: "wf_hassertion 0 A"
  shows "denote (havocS x [] A) S = denote A (sem (Havoc x) S)"
proof -
  have eq: "sat_hassertion [] [] (havocS x [] A) S =
    sat_hassertion [] [] A (sem (Havoc x) S)"
    by (rule havoc_sat[OF frag]) (simp_all add: wf havoc_env_def)
  then show ?thesis by (simp add: denote_def)
qed

theorem havocS_rule:
  assumes frag: "havoc_frag A" and wf: "wf_hassertion 0 A"
  shows "\<Turnstile> {denote (havocS x [] A)} Havoc x {denote A}"
  using denote_havocS[OF frag wf] by (simp add: hyper_hoare_triple_def)

end
