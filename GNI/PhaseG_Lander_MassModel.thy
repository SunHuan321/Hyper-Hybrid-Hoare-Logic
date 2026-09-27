theory PhaseG_Lander_MassModel
  imports PhaseG_GNI_refinement H3L_Semantics.Lander
begin

section \<open>A candidate mass-sensitive lunar lander model\<close>

text \<open>The original Plant, Ctrl, and Abs in Lander use the normalized
variable W but do not use M or Fc.  These three variants retain the proved
model and its refinement theorem unchanged.  They expose the physical
relation W = Fc/M and make the admissible thrust bound explicit.  No
refinement or GNI theorem for these variants is asserted here.

Between control updates, this candidate holds Fc constant, uses
M' = -Fc/2500, and keeps the old W' = W^2/2500.  Under M > 0 and
Fc = M*W, these equations are compatible.  The private channel m2c
passes the current mass to the controller; the observer below hides its
value and event.  That channel and the constant-force assumption are
modeling choices that require validation against the intended plant.\<close>

definition lander_mass_field :: "var \<Rightarrow> state \<Rightarrow> real" where
  "lander_mass_field =
    ((\<lambda>_ _. 0)
      (V := (\<lambda>s. s Fc / s M - 3.732),
       M := (\<lambda>s. -(s Fc) / 2500),
       Fc := (\<lambda>_. 0),
       W := (\<lambda>s. (s W)\<^sup>2 / 2500)))"

definition lander_mass_clock_field :: "var \<Rightarrow> state \<Rightarrow> real" where
  "lander_mass_clock_field = lander_mass_field(T := (\<lambda>_. 1))"

definition lander_force_ok :: "real \<Rightarrow> state \<Rightarrow> bool" where
  "lander_force_ok Fmax s \<longleftrightarrow>
    0 < s M \<and> 0 \<le> s Fc \<and> s Fc \<le> Fmax"

definition Plant_M :: "real \<Rightarrow> proc" where
  "Plant_M Fmax =
    Interrupt (ODE lander_mass_field) (lander_force_ok Fmax)
      [(''p2c''[!](\<lambda>s. s V),
        Cm (''p2c''[!](\<lambda>s. s W));
        Cm (''m2c''[!](\<lambda>s. s M));
        Cm (''c2p''[?]W);
        Fc ::= (\<lambda>s. s M * s W);
        Assume (lander_force_ok Fmax))]"

definition Ctrl_M :: "real \<Rightarrow> proc" where
  "Ctrl_M Fmax =
    Wait (\<lambda>_. Period);
    Cm (''p2c''[?]V);
    Cm (''p2c''[?]W);
    Cm (''m2c''[?]M);
    Fc ::= (\<lambda>s. s M * W_upd (s V) (s W));
    Assume (lander_force_ok Fmax);
    Cm (''c2p''[!](\<lambda>s. s Fc / s M))"

definition Abs_M :: "real \<Rightarrow> proc" where
  "Abs_M Fmax =
    T ::= (\<lambda>_. 0);
    Cont (ODE lander_mass_clock_field)
      (\<lambda>s. s T < Period \<and> lander_force_ok Fmax s);
    W ::= (\<lambda>s. W_upd (s V) (s W));
    Fc ::= (\<lambda>s. s M * s W);
    Assume (lander_force_ok Fmax)"

definition Lander_M :: "real \<Rightarrow> pproc" where
  "Lander_M Fmax =
    Parallel (Single (Rep (Plant_M Fmax)))
      {''p2c'', ''m2c'', ''c2p''}
      (Single (Rep (Ctrl_M Fmax)))"

section \<open>Candidate trace-level GNI specification\<close>

text \<open>The high input is the initial plant mass, saved in a logical
label.  The two low input labels save initial V and W.  Public
communications retain direction, channel, and value.  A wait reveals
duration and the plant's V/W curve on [0,d]; the private mass channel is hidden.
This is a block-sensitive observer, so a future proof must address
unequal-duration splitting explicitly.\<close>

definition LOW_W :: char where "LOW_W = CHR ''q''"

fun lander_low_gstate :: "gstate \<Rightarrow> (real \<times> real) option" where
  "lander_low_gstate (State s) = Some (s V, s W)"
| "lander_low_gstate (ParState (State sp) _) = Some (sp V, sp W)"
| "lander_low_gstate (ParState (ParState _ _) _) = None"

datatype lander_obs_event =
    VisibleComm comm_type cname real
  | VisibleWait real "real \<Rightarrow> (real \<times> real) option"

fun lander_obs_block :: "trace_block \<Rightarrow> lander_obs_event option" where
  "lander_obs_block (CommBlock ct ch v) =
    (if ch = ''m2c'' then None else Some (VisibleComm ct ch v))"
| "lander_obs_block (WaitBlock d p rdy) =
    Some (VisibleWait d (restrict (lander_low_gstate \<circ> p) {0..d}))"

definition lander_obs_trace :: "trace \<Rightarrow> lander_obs_event list" where
  "lander_obs_trace tr =
    concat (map (\<lambda>b. case lander_obs_block b of
      None \<Rightarrow> [] | Some e \<Rightarrow> [e]) tr)"

fun lander_plant_logical ::
  "(char, real) exgstate \<Rightarrow> (char \<Rightarrow> real) option" where
  "lander_plant_logical (ExParState (ExState (lab, sp)) sc) = Some lab"
| "lander_plant_logical _ = None"

fun lander_final_low :: "(char, real) exgstate \<Rightarrow> (real \<times> real) option" where
  "lander_final_low (ExParState (ExState (lab, sp)) sc) = Some (sp V, sp W)"
| "lander_final_low _ = None"

definition lander_high_input ::
  "((char, real) exgstate \<times> trace) \<Rightarrow> real option" where
  "lander_high_input run = map_option (\<lambda>lab. lab HI)
    (lander_plant_logical (fst run))"

definition lander_low_input ::
  "((char, real) exgstate \<times> trace) \<Rightarrow> (real \<times> real) option" where
  "lander_low_input run = map_option (\<lambda>lab. (lab LO, lab LOW_W))
    (lander_plant_logical (fst run))"

definition lander_low_observation ::
  "((char, real) exgstate \<times> trace) \<Rightarrow>
    ((real \<times> real) option \<times> lander_obs_event list)" where
  "lander_low_observation run =
    (lander_final_low (fst run), lander_obs_trace (snd run))"

definition lander_mass_gni ::
  "((char, real) exgstate \<times> trace) set \<Rightarrow> bool" where
  "lander_mass_gni Runs \<longleftrightarrow>
    (\<forall>r\<in>Runs. lander_high_input r \<noteq> None \<and>
      lander_low_input r \<noteq> None \<and> lander_final_low (fst r) \<noteq> None) \<and>
    (\<forall>r1\<in>Runs. \<forall>r2\<in>Runs.
      lander_low_input r1 = lander_low_input r2 \<longrightarrow>
      (\<exists>r3\<in>Runs.
        lander_high_input r3 = lander_high_input r1 \<and>
        lander_low_input r3 = lander_low_input r2 \<and>
        lander_low_observation r3 = lander_low_observation r2))"

definition lander_mass_initial ::
  "real \<Rightarrow> (char, real) exgstate set \<Rightarrow> bool" where
  "lander_mass_initial Fmax S \<longleftrightarrow>
    0 < Fmax \<and> S \<noteq> {} \<and>
    (\<forall>x\<in>S. \<exists>lp lc sp sc.
      x = ExParState (ExState (lp, sp)) (ExState (lc, sc)) \<and>
      lp HI = sp M \<and> lp LO = sp V \<and> lp LOW_W = sp W \<and>
      sp Fc = sp M * sp W \<and> lander_force_ok Fmax sp \<and>
      0 < sc M)"

definition lander_mass_gni_spec ::
  "real \<Rightarrow> (char, real) exgstate set \<Rightarrow> bool" where
  "lander_mass_gni_spec Fmax S \<longleftrightarrow>
    lander_mass_initial Fmax S \<longrightarrow>
    par_sem (Lander_M Fmax) S \<noteq> {} \<and>
    lander_mass_gni (par_sem (Lander_M Fmax) S)"

end
