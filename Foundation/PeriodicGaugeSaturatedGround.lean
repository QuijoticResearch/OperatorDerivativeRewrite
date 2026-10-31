import Foundation.PeriodicGroundHaarScale
/-! Gauge-saturated positive-Haar trials for the actual periodic Wilson ground.
The free root and all63 relative temporal variables are retained. A measurable
positive support replaces projection infrastructure. The actual principal value
has matching beta^(-288) lower/upper powers, hence a uniform half-scale ratio.
Actual local plaquette variance has two-sided beta^(-2) bounds and its normalized
native vector has uniform one-step loss. Constants depend on this fixed cell;
no full even-sector spectral gap or physical mass gap is proved. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicGaugeSaturatedGround
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open FourCubePinnedCoercivity
attribute [local irreducible] boundaryHaar gaugeHaar kernel defect weight spatialAction temporalAction halfAction PeriodicSlabGauge.gaugeAction

def root : SpatialVertex := fun _ => 0
def depth (v : SpatialVertex) : ℕ := (v 0).val+(v 1).val+(v 2).val
def axis (v : SpatialVertex) : Fin 3 := if v 0≠0 then 0 else if v 1≠0 then 1 else 2
def parent (v : SpatialVertex) : SpatialVertex := Function.update v (axis v) (v (axis v)-1)

theorem depth_le (v : SpatialVertex) : depth v≤9 := by decide +revert

theorem depth_zero (v : SpatialVertex) : depth v=0 ↔ v=root := by decide +revert

theorem parent_shift (v : SpatialVertex) (hv : v≠root) : shift (parent v) (axis v)=v := by
  decide +revert

theorem parent_depth (v : SpatialVertex) (hv : v≠root) : depth (parent v)+1=depth v := by
  decide +revert


open PeriodicSlabGauge PeriodicPolynomialGround SU2HaarSmallCap

theorem rooted_defect_bound (a : Gauge) (A : ℝ) (hA : 0≤A)
    (he : ∀ e : SpatialEdge,defect (a e.1*(a (shift e.1 e.2))⁻¹)≤A) (v : SpatialVertex) :
    defect (a v*(a root)⁻¹)≤(4 : ℝ)^(depth v+1)*A := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      rw [mul_inv_cancel,defect_one]
      positivity
    · have hd := parent_depth v hv
      have hsmall : depth (parent v)<n := by omega
      have hprev := ih (depth (parent v)) hsmall (parent v) rfl
      have hedge := he (parent v,axis v)
      change defect (a (parent v)*(a (shift (parent v) (axis v)))⁻¹)≤A at hedge
      rw [parent_shift v hv] at hedge
      have hinv : (a (parent v)*(a v)⁻¹)⁻¹=a v*(a (parent v))⁻¹ := by group
      have hx : defect (a v*(a (parent v))⁻¹)≤A := by
        rw [← hinv,defect_inv]
        exact hedge
      have hprod : a v*(a root)⁻¹=(a v*(a (parent v))⁻¹)*(a (parent v)*(a root)⁻¹) := by group
      have h := FourCubeBoundaryCoercivity.defect_mul
        (a v*(a (parent v))⁻¹) (a (parent v)*(a root)⁻¹)
      rw [← hprod] at h
      have hp : (3 : ℝ)≤4^(depth (parent v)+1) := by
        have hh : (1 : ℝ)≤4^depth (parent v) := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        nlinarith
      have hpA := mul_nonneg (sub_nonneg.mpr hp) hA
      have hpow : (4 : ℝ)^(depth v+1)=4*4^(depth (parent v)+1) := by
        rw [← hd,pow_succ]
        ring
      rw [← hn,hpow]
      nlinarith

theorem rooted_uniform (a : Gauge) (A : ℝ) (hA : 0≤A)
    (he : ∀ e : SpatialEdge,defect (a e.1*(a (shift e.1 e.2))⁻¹)≤A) (v : SpatialVertex) :
    defect (a v*(a root)⁻¹)≤(4 : ℝ)^10*A := by
  have h := rooted_defect_bound a A hA he v
  have hp : (4 : ℝ)^(depth v+1)≤4^10 :=
    pow_le_pow_right₀ (by norm_num) (by have hh := depth_le v; omega)
  exact h.trans (mul_le_mul_of_nonneg_right hp hA)

theorem cap_overlap_edge (t : ℝ) (U : State) (a : Gauge)
    (hU : U∈boundaryBox t) (hV : gaugeAction a U∈boundaryBox t) (e : SpatialEdge) :
    defect (a e.1*(a (shift e.1 e.2))⁻¹)≤18*t^2 := by
  let R : SU2 := a (shift e.1 e.2)*U e*(a (shift e.1 e.2))⁻¹
  have hR : defect R=defect (U e) := by unfold R defect; rw [halfTrace_conjugate]
  have hQ : (a e.1*(a (shift e.1 e.2))⁻¹)*R=gaugeAction a U e := by
    unfold R gaugeAction
    group
  have h := FourCubeBoundaryCoercivity.defect_unmul (a e.1*(a (shift e.1 e.2))⁻¹) R
  rw [hQ,hR] at h
  have h1 := hU e (Set.mem_univ e)
  have h2 := hV e (Set.mem_univ e)
  change defect (U e)≤3*t^2 at h1
  change defect (gaugeAction a U e)≤3*t^2 at h2
  linarith

theorem cap_overlap_rooted (t : ℝ) (U : State) (a : Gauge)
    (hU : U∈boundaryBox t) (hV : gaugeAction a U∈boundaryBox t) (v : SpatialVertex) :
    a v*(a root)⁻¹∈cap (4096*t) := by
  have h := rooted_uniform a (18*t^2) (by positivity)
    (cap_overlap_edge t U a hU hV) v
  change defect (a v*(a root)⁻¹)≤3*(4096*t)^2
  nlinarith [sq_nonneg t]

private instance vertexDecidableEq : DecidableEq SpatialVertex :=
  fun v w => decidable_of_decidable_of_iff (p := ∀ i,v i=w i) funext_iff.symm

abbrev RootIndex := {v : SpatialVertex // v=root}
abbrev RelFieldIndex := {v : SpatialVertex // ¬v=root}
private instance rootIndexFintype : Fintype RootIndex := Subtype.fintype (fun v => v=root)

abbrev RootField := RootIndex → SU2
abbrev RelField := RelFieldIndex → SU2

def rootHaar : Measure RootField := Measure.pi (fun _ => law)
def relFieldHaar : Measure RelField := Measure.pi (fun _ => law)
instance root_probability : IsProbabilityMeasure rootHaar := by unfold rootHaar; infer_instance
instance relField_probability : IsProbabilityMeasure relFieldHaar := by unfold relFieldHaar; infer_instance

def split : Gauge ≃ᵐ (RootField × RelField) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialVertex => SU2) (fun v => v=root)

theorem split_preserving : MeasurePreserving split gaugeHaar (rootHaar.prod relFieldHaar) := by
  simpa only [split,gaugeHaar,rootHaar,relFieldHaar] using
    measurePreserving_piEquivPiSubtypeProd (fun _ : SpatialVertex => law) (fun v => v=root)

def relField (g : Gauge) (v : RelFieldIndex) : SU2 := g v.val*(g root)⁻¹

theorem relField_measurable : Measurable relField := by
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply v.val).mul (measurable_pi_apply root).inv

private theorem raw_preserving :
    MeasurePreserving (fun g : Gauge => (g root,fun v : RelFieldIndex => g v.val))
      gaugeHaar (law.prod relFieldHaar) := by
  have hr : MeasurePreserving (fun c : RootField => c ⟨root,rfl⟩) rootHaar law := by
    unfold rootHaar
    exact measurePreserving_eval (fun _ : RootIndex => law) ⟨root,rfl⟩
  have h := (hr.prod (MeasurePreserving.id relFieldHaar)).comp split_preserving
  convert h using 1
  funext g
  rfl

/-- The actual global root is independent Haar, and all 63 relField variables
remain independent Haar. No pointwise root fixing is performed. -/
theorem joint_preserving :
    MeasurePreserving (fun g : Gauge => (g root,relField g)) gaugeHaar (law.prod relFieldHaar) := by
  have hm : Measurable (fun p : SU2 × RelField => fun v : RelFieldIndex => p.2 v*p.1⁻¹) := by
    apply measurable_pi_iff.mpr
    intro v
    exact ((measurable_pi_apply v).comp measurable_snd).mul measurable_fst.inv
  have hc (c : SU2) :
      MeasurePreserving (fun h : RelField => fun v => h v*c⁻¹) relFieldHaar relFieldHaar := by
    unfold relFieldHaar
    exact measurePreserving_pi (fun _ : RelFieldIndex => law) (fun _ : RelFieldIndex => law)
      (fun _ => measurePreserving_mul_right law c⁻¹)
  have hs := (MeasurePreserving.id law).skew_product hm
    (ae_of_all law (fun c => (hc c).map_eq))
  exact hs.comp raw_preserving

theorem relField_preserving : MeasurePreserving relField gaugeHaar relFieldHaar :=
  (measurePreserving_snd (μ := law) (ν := relFieldHaar)).comp joint_preserving

def anchored (h : RelField) (v : SpatialVertex) : SU2 :=
  if hv : v=root then 1 else h ⟨v,hv⟩
def assemble (c : SU2) (h : RelField) (v : SpatialVertex) : SU2 := anchored h v*c

theorem anchored_root (h : RelField) : anchored h root=1 := by simp [anchored]
theorem assemble_root (c : SU2) (h : RelField) : assemble c h root=c := by
  simp [assemble,anchored_root]

theorem assemble_relField (g : Gauge) : assemble (g root) (relField g)=g := by
  funext v
  by_cases hv : v=root
  · subst v
    exact assemble_root _ _
  · simp [assemble,anchored,hv,relField,mul_assoc]

theorem assemble_measurable : Measurable (fun p : SU2 × RelField => assemble p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro v
  unfold assemble anchored
  split_ifs <;> fun_prop

/-- The reconstruction transports product Haar back to the actual temporal law. -/
theorem assemble_preserving :
    MeasurePreserving (fun p : SU2 × RelField => assemble p.1 p.2) (law.prod relFieldHaar) gaugeHaar := by
  refine ⟨assemble_measurable,?_⟩
  rw [← joint_preserving.map_eq,Measure.map_map assemble_measurable joint_preserving.measurable]
  have he : (fun g : Gauge => assemble (g root) (relField g))=id := funext assemble_relField
  change Measure.map (fun g : Gauge => assemble (g root) (relField g)) gaugeHaar = gaugeHaar
  rw [he,Measure.map_id]

/-- Exact product-Haar integral with the free root and every relField link retained. -/
theorem integral_split (f : Gauge → ℝ) (hf : Measurable f) :
    (∫ g,f g ∂gaugeHaar)=∫ p : SU2 × RelField,f (assemble p.1 p.2) ∂law.prod relFieldHaar := by
  have h := integral_map joint_preserving.measurable.aemeasurable
    (μ := gaugeHaar) (f := fun p : SU2 × RelField => f (assemble p.1 p.2))
  rw [joint_preserving.map_eq] at h
  have he := h ((hf.comp assemble_measurable).aestronglyMeasurable)
  simpa only [Function.comp_apply,assemble_relField] using he.symm


def relBox (t : ℝ) : Set RelField := Set.univ.pi (fun _ => cap t)

theorem rel_count : Fintype.card RelFieldIndex=63 := by decide

theorem relBox_measurable (t : ℝ) : MeasurableSet (relBox t) :=
  MeasurableSet.univ_pi (fun _ => cap_measurable t)

theorem relBox_mass (t : ℝ) : relFieldHaar.real (relBox t)=(law.real (cap t))^63 := by
  change (relFieldHaar (relBox t)).toReal=(law (cap t)).toReal^63
  simp [relFieldHaar,relBox,Measure.pi_pi,Finset.prod_const,
    Finset.card_univ,ENNReal.toReal_pow]

theorem relField_box_mass (t : ℝ) : gaugeHaar.real (relField ⁻¹' relBox t)=(law.real (cap t))^63 := by
  have h := relField_preserving.map_eq
  rw [← relBox_mass]
  change (gaugeHaar (relField ⁻¹' relBox t)).toReal=(relFieldHaar (relBox t)).toReal
  rw [← Measure.map_apply relField_measurable (relBox_measurable t),h]

theorem overlap_mass (t : ℝ) (U : State) (hU : U∈boundaryBox t) :
    gaugeHaar.real {a | gaugeAction a U∈boundaryBox t}≤(law.real (cap (4096*t)))^63 := by
  rw [← relField_box_mass]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro a ha v _
  exact cap_overlap_rooted t U a hU ha v.val



theorem conjugated_box (t : ℝ) (c : SU2) (V : State) (hV : V∈boundaryBox t) :
    gaugeAction (fun _ => c) V∈boundaryBox t := by
  intro e _
  change defect (gaugeAction (fun _ => c) V e)≤3*t^2
  unfold gaugeAction
  unfold defect
  rw [halfTrace_conjugate]
  have hh : defect (V e)≤3*t^2 := hV e (Set.mem_univ e)
  simpa only [defect] using hh

theorem assembled_weight (β : ℝ) (U V : State) (c : SU2) (h : RelField) :
    weight β U V (assemble c h)=weight β U (gaugeAction (fun _ => c) V) (anchored h) := by
  have he (e : SpatialEdge) : temporalWord U V (assemble c h) e=
      temporalWord U (gaugeAction (fun _ => c) V) (anchored h) e := by
    unfold temporalWord assemble gaugeAction
    group
  have ht : temporalAction U V (assemble c h)=
      temporalAction U (gaugeAction (fun _ => c) V) (anchored h) := by
    unfold temporalAction
    simp_rw [he]
  unfold weight halfAction
  rw [ht,spatial_action_invariant]

theorem kernel_root_block (β t : ℝ) (hb : 0≤β) (U V : State)
    (hU : U∈boundaryBox t) (hV : V∈boundaryBox t) :
    (law.real (cap t))^63*Real.exp (-41472*β*t^2)≤kernel β U V := by
  have hc : Measurable (fun a : Gauge => ((U,V),a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (weight β U V) := (weight_joint_measurable β).comp hc
  have hi := assemble_preserving.integrable_comp_of_integrable (weight_integrable β U V)
  have hp (p : SU2 × RelField) (hh : p∈Set.univ ×ˢ relBox t) :
      Real.exp (-41472*β*t^2)≤weight β U V (assemble p.1 p.2) := by
    rw [assembled_weight]
    have ha : anchored p.2∈temporalBox t := by
      intro v _
      unfold anchored
      split_ifs with hv
      · change defect (1 : SU2)≤3*t^2
        rw [defect_one]
        positivity
      · exact hh.2 ⟨v,hv⟩ (Set.mem_univ _)
    have h := action_cap_upper t U (gaugeAction (fun _ => p.1) V) (anchored p.2)
      hU (conjugated_box t p.1 V hV) ha
    unfold weight
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h hb]
  have hS : MeasurableSet (Set.univ ×ˢ relBox t : Set (SU2 × RelField)) :=
    MeasurableSet.univ.prod (relBox_measurable t)
  have hmass : (law.prod relFieldHaar).real (Set.univ ×ˢ relBox t)=(law.real (cap t))^63 := by
    change ((law.prod relFieldHaar) (Set.univ ×ˢ relBox t)).toReal=_
    rw [Measure.prod_prod]
    simp only [measure_univ,one_mul]
    exact relBox_mass t
  have hlow := setIntegral_mono_on (integrable_const (Real.exp (-41472*β*t^2))).integrableOn
    hi.integrableOn hS hp
  rw [setIntegral_const,smul_eq_mul,hmass] at hlow
  have hfull := setIntegral_le_integral (s := Set.univ ×ˢ relBox t) hi
    (ae_of_all _ (fun p => (Real.exp_pos _).le.trans (weight_bounds β U V (assemble p.1 p.2)).1))
  have he := integral_split (weight β U V) hm
  unfold kernel
  exact hlow.trans (hfull.trans_eq he.symm)

def gaugeEquiv (a : Gauge) : State ≃ᵐ State :=
  (MeasurableEquiv.mulLeft (fun e : SpatialEdge => a e.1)).trans
    (MeasurableEquiv.mulRight (fun e : SpatialEdge => (a (shift e.1 e.2))⁻¹))

theorem gaugeEquiv_embedding (a : Gauge) : MeasurableEmbedding (gaugeAction a) := by
  have he : (fun U : State => gaugeEquiv a U)=gaugeAction a := by
    funext U
    unfold gaugeEquiv gaugeAction
    rfl
  rw [← he]
  exact (gaugeEquiv a).measurableEmbedding

theorem action_boundary_preserving (a : Gauge) :
    MeasurePreserving (gaugeAction a) boundaryHaar boundaryHaar := by
  unfold boundaryHaar gaugeAction
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e : SpatialEdge => (measurePreserving_mul_right law (a (shift e.1 e.2))⁻¹).comp
      (measurePreserving_mul_left law (a e.1)))

theorem action_joint_measurable : Measurable (fun p : State × Gauge => gaugeAction p.2 p.1) := by
  apply measurable_pi_iff.mpr
  intro e
  unfold gaugeAction
  fun_prop

theorem action_comp (a b : Gauge) (U : State) : gaugeAction a (gaugeAction b U)=gaugeAction (a*b) U := by
  funext e
  unfold gaugeAction
  simp only [Pi.mul_apply]
  group

def indicator (t : ℝ) : State → ℝ := (boundaryBox t).indicator (fun _ => 1)
def average (t : ℝ) (U : State) : ℝ := ∫ a,indicator t (gaugeAction a U) ∂gaugeHaar

theorem indicator_measurable (t : ℝ) : Measurable (indicator t) :=
  measurable_const.indicator (boundaryBox_measurable t)

theorem indicator_bounds (t : ℝ) (U : State) : 0 ≤ indicator t U ∧ indicator t U≤1 := by
  by_cases hU : U∈boundaryBox t
  · simp [indicator,Set.indicator_of_mem hU]
  · simp [indicator,Set.indicator_of_notMem hU]

theorem average_measurable (t : ℝ) : Measurable (average t) := by
  have hm : StronglyMeasurable (Function.uncurry (fun U : State => fun a : Gauge => indicator t (gaugeAction a U))) :=
    ((indicator_measurable t).comp action_joint_measurable).stronglyMeasurable
  exact hm.integral_prod_right.measurable

theorem indicator_action_integrable (t : ℝ) (U : State) :
    Integrable (fun a => indicator t (gaugeAction a U)) gaugeHaar := by
  have hc : Measurable (fun a : Gauge => (U,a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun a : Gauge => indicator t (gaugeAction a U)) :=
    (indicator_measurable t).comp (action_joint_measurable.comp hc)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with a
  rw [Real.norm_eq_abs,abs_of_nonneg (indicator_bounds t _).1]
  exact (indicator_bounds t _).2

theorem average_bounds (t : ℝ) (U : State) : 0≤average t U ∧ average t U≤1 := by
  constructor
  · exact integral_nonneg (fun a => (indicator_bounds t _).1)
  · have h := integral_mono (indicator_action_integrable t U) (integrable_const (1 : ℝ))
      (fun a => (indicator_bounds t _).2)
    simpa only [average,integral_const,probReal_univ,one_smul] using h

theorem average_invariant (t : ℝ) (a : Gauge) (U : State) :
    average t (gaugeAction a U)=average t U := by
  unfold average
  simp_rw [action_comp]
  exact (gauge_right_preserving a).integral_comp (MeasurableEquiv.mulRight a).measurableEmbedding
    (fun g : Gauge => indicator t (gaugeAction g U))

theorem average_overlap_upper (t : ℝ) (U : State) (hU : U∈boundaryBox t) :
    average t U≤(law.real (cap (4096*t)))^63 := by
  have hc : Measurable (fun a : Gauge => (U,a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun a : Gauge => gaugeAction a U) := action_joint_measurable.comp hc
  have hset : MeasurableSet {a : Gauge | gaugeAction a U∈boundaryBox t} :=
    (boundaryBox_measurable t).preimage hm
  have he : (fun a => indicator t (gaugeAction a U))=
      ({a : Gauge | gaugeAction a U∈boundaryBox t}).indicator (fun _ => (1 : ℝ)) := rfl
  unfold average
  rw [he]
  have hi : (∫ a : Gauge,({a : Gauge | gaugeAction a U∈boundaryBox t}).indicator
      (fun _ => (1 : ℝ)) a ∂gaugeHaar)=gaugeHaar.real {a : Gauge | gaugeAction a U∈boundaryBox t} :=
    integral_indicator_one hset
  exact hi.trans_le (overlap_mass t U hU)


theorem average_mass (t : ℝ) : (∫ U,average t U ∂boundaryHaar)=(law.real (cap t))^192 := by
  have hm : Measurable (fun p : State × Gauge => indicator t (gaugeAction p.2 p.1)) :=
    (indicator_measurable t).comp action_joint_measurable
  have hi : Integrable (fun p : State × Gauge => indicator t (gaugeAction p.2 p.1))
      (boundaryHaar.prod gaugeHaar) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun p => by
          rw [Real.norm_eq_abs,abs_of_nonneg (indicator_bounds t _).1]
          exact (indicator_bounds t _).2))
  have hinner (a : Gauge) : (∫ U,indicator t (gaugeAction a U) ∂boundaryHaar)=boundaryHaar.real (boundaryBox t) := by
    have h := (action_boundary_preserving a).integral_comp (gaugeEquiv_embedding a) (indicator t)
    change (∫ U,indicator t (gaugeAction a U) ∂boundaryHaar)=∫ U,indicator t U ∂boundaryHaar at h
    have hj : (∫ U,indicator t U ∂boundaryHaar)=boundaryHaar.real (boundaryBox t) :=
      integral_indicator_one (boundaryBox_measurable t)
    exact h.trans hj
  unfold average
  rw [integral_integral_swap hi]
  simp_rw [hinner]
  simpa only [integral_const,probReal_univ,one_smul] using boundary_mass t

def saturation (t : ℝ) : Set State := {U | 0<average t U}

theorem saturation_measurable (t : ℝ) : MeasurableSet (saturation t) :=
  measurableSet_lt measurable_const (average_measurable t)

theorem saturation_witness (t : ℝ) (U : State) (hU : U∈saturation t) :
    ∃ a : Gauge,gaugeAction a U∈boundaryBox t := by
  by_contra hn
  push Not at hn
  have hz (a : Gauge) : indicator t (gaugeAction a U)=0 := by
    exact Set.indicator_of_notMem (hn a) _
  change 0<(∫ a,indicator t (gaugeAction a U) ∂gaugeHaar) at hU
  simp_rw [hz] at hU
  simpa using hU

theorem saturation_average_bound (t : ℝ) (U : State) :
    average t U≤(saturation t).indicator (fun _ => (law.real (cap (4096*t)))^63) U := by
  by_cases hU : U∈saturation t
  · rw [Set.indicator_of_mem hU]
    obtain ⟨a,ha⟩ := saturation_witness t U hU
    have h := average_overlap_upper t (gaugeAction a U) ha
    rw [average_invariant] at h
    exact h
  · rw [Set.indicator_of_notMem hU]
    exact le_of_not_gt hU

theorem saturation_mass_bound (t : ℝ) :
    (law.real (cap t))^192≤boundaryHaar.real (saturation t)*(law.real (cap (4096*t)))^63 := by
  have h := integral_mono_of_nonneg (ae_of_all _ (fun U => (average_bounds t U).1))
    ((integrable_const (μ := boundaryHaar) ((law.real (cap (4096*t)))^63)).indicator (saturation_measurable t))
    (ae_of_all _ (saturation_average_bound t))
  rw [average_mass,integral_indicator (saturation_measurable t),setIntegral_const,smul_eq_mul] at h
  exact h

theorem cap_positive (t : ℝ) (ht : 0<t) (h1 : t≤1) : 0<law.real (cap t) :=
  (mul_pos (by positivity : 0<(1/(4*Real.pi^2) : ℝ)) (pow_pos ht 3)).trans_le (mass_lower t ht.le h1)

theorem saturation_mass_pos (t : ℝ) (ht : 0<t) (h1 : t≤1) : 0<boundaryHaar.real (saturation t) := by
  have h := saturation_mass_bound t
  have hp := pow_pos (cap_positive t ht h1) 192
  by_contra hn
  have hz : boundaryHaar.real (saturation t)=0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
  rw [hz,zero_mul] at h
  linarith

theorem saturated_kernel_block (β t : ℝ) (hb : 0≤β) (U V : State)
    (hU : U∈saturation t) (hV : V∈saturation t) :
    (law.real (cap t))^63*Real.exp (-41472*β*t^2)≤kernel β U V := by
  obtain ⟨a,ha⟩ := saturation_witness t U hU
  obtain ⟨b,hb'⟩ := saturation_witness t V hV
  have h := kernel_root_block β t hb (gaugeAction a U) (gaugeAction b V) ha hb'
  rw [kernel_left_invariant,kernel_right_invariant] at h
  exact h

theorem eigenvalue_cap_comparison (β t : ℝ) (hb : 0≤β) (g : GroundData β) (ht : 0<t) (h1 : t≤1) :
    (law.real (cap t))^255*Real.exp (-41472*β*t^2)≤g.value*(law.real (cap (4096*t)))^63 := by
  have hM := saturation_mass_bound t
  have hLam := PeriodicGroundMass.eigenvalue_block_lower g (saturation t) (saturation_measurable t)
    (saturation_mass_pos t ht h1) ((law.real (cap t))^63*Real.exp (-41472*β*t^2))
    (fun U hU V hV => saturated_kernel_block β t hb U V hU hV)
  have hk : 0≤(law.real (cap t))^63*Real.exp (-41472*β*t^2) := by positivity
  have hh : 0≤(law.real (cap (4096*t)))^63 := pow_nonneg measureReal_nonneg _
  calc
    _ = ((law.real (cap t))^63*Real.exp (-41472*β*t^2))*(law.real (cap t))^192 := by ring
    _ ≤ ((law.real (cap t))^63*Real.exp (-41472*β*t^2))*(boundaryHaar.real (saturation t)*(law.real (cap (4096*t)))^63) :=
      mul_le_mul_of_nonneg_left hM hk
    _ = (((law.real (cap t))^63*Real.exp (-41472*β*t^2))*boundaryHaar.real (saturation t))*(law.real (cap (4096*t)))^63 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hLam hh


def orbitConstant : ℝ := (Real.exp 3*SU2HaarLaplaceUpper.upperConstant 1*4096^3)^63

theorem orbitConstant_pos : 0<orbitConstant := by
  unfold orbitConstant
  have hc := SU2HaarLaplaceUpper.upperConstant_pos 1 (by norm_num)
  positivity

def eigenLowerConstant : ℝ := (1/(4*Real.pi^2))^255*Real.exp (-41472)/orbitConstant

theorem eigenLowerConstant_pos : 0<eigenLowerConstant := by
  unfold eigenLowerConstant
  exact div_pos (mul_pos (pow_pos (by positivity) _) (Real.exp_pos _)) orbitConstant_pos

theorem scaled_overlap_upper (t : ℝ) (ht : 0<t) (h1 : 4096*t≤1) :
    (law.real (cap (4096*t)))^63≤orbitConstant*t^189 := by
  have h := pow_le_pow_left₀ measureReal_nonneg
    (PeriodicGroundHaarScale.cap_polynomial_upper (4096*t) (by positivity) h1) 63
  convert h using 1 <;> unfold orbitConstant <;> ring

theorem eigenvalue_scale_lower (β t : ℝ) (hb : 0≤β) (g : GroundData β)
    (ht : 0<t) (h1 : 4096*t≤1) (hscale : β*t^2≤1) :
    eigenLowerConstant*t^576≤g.value := by
  have ht1 : t≤1 := by linarith
  have hc : (0 : ℝ)<1/(4*Real.pi^2) := by positivity
  have hm := pow_le_pow_left₀ (mul_nonneg hc.le (pow_nonneg ht.le 3)) (mass_lower t ht.le ht1) 255
  have he : Real.exp (-41472 : ℝ)≤Real.exp (-41472*β*t^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hlow : ((1/(4*Real.pi^2))^255*Real.exp (-41472))*t^765≤
      (law.real (cap t))^255*Real.exp (-41472*β*t^2) := by
    have hh := mul_le_mul hm he (Real.exp_pos _).le (pow_nonneg measureReal_nonneg _)
    convert hh using 1 <;> ring
  have hcap := eigenvalue_cap_comparison β t hb g ht ht1
  have hupper := mul_le_mul_of_nonneg_left (scaled_overlap_upper t ht h1) g.value_pos.le
  have h := hlow.trans (hcap.trans hupper)
  have hh : (((1/(4*Real.pi^2))^255*Real.exp (-41472))*t^576)*t^189≤
      (g.value*orbitConstant)*t^189 := by
    convert h using 1 <;> ring
  have hcancel : ((1/(4*Real.pi^2))^255*Real.exp (-41472))*t^576≤g.value*orbitConstant :=
    (mul_le_mul_iff_left₀ (pow_pos ht 189)).mp hh
  unfold eigenLowerConstant
  calc
    _ = (((1/(4*Real.pi^2))^255*Real.exp (-41472))*t^576)/orbitConstant := by ring
    _ ≤ g.value := (div_le_iff₀ orbitConstant_pos).mpr hcancel

theorem eigenvalue_matching_lower (β : ℝ) (hb : 16777216≤β) (g : GroundData β) :
    eigenLowerConstant/β^288≤g.value := by
  have hp : 0<β := by linarith
  have hs : 0<Real.sqrt β := Real.sqrt_pos.mpr hp
  have hs4096 : 4096≤Real.sqrt β := by
    have hsq := Real.sq_sqrt hp.le
    nlinarith [Real.sqrt_nonneg β]
  let t : ℝ := 1/Real.sqrt β
  have ht : 0<t := div_pos zero_lt_one hs
  have ht2 : t^2=1/β := by dsimp [t]; rw [div_pow,one_pow,Real.sq_sqrt hp.le]
  have h1 : 4096*t≤1 := by
    dsimp [t]
    rw [mul_one_div]
    exact (div_le_one hs).mpr hs4096
  have hscale : β*t^2≤1 := by rw [ht2,mul_one_div_cancel hp.ne']
  have hpow : t^576=1/β^288 := by
    calc
      _ = (t^2)^288 := by ring
      _ = _ := by rw [ht2,div_pow,one_pow]
  have h := eigenvalue_scale_lower β t hp.le g ht h1 hscale
  rw [hpow] at h
  simpa only [mul_one_div] using h

def ratioConstant : ℝ := PeriodicGroundHaarScale.upperConstant*2^288/eigenLowerConstant

theorem ratioConstant_pos : 0<ratioConstant := by
  unfold ratioConstant
  exact div_pos (mul_pos PeriodicGroundHaarScale.upperConstant_pos (by positivity)) eigenLowerConstant_pos

theorem eigenvalue_half_ratio (β : ℝ) (hb : 16777216≤β) (g : GroundData β) (h : GroundData (β/2)) :
    h.value/g.value≤ratioConstant := by
  have hp : 0<β := by linarith
  have hl := eigenvalue_matching_lower β hb g
  have hu := PeriodicGroundHaarScale.eigenvalue_polynomial_upper (β/2) (by linarith) h
  have hn : 0≤PeriodicGroundHaarScale.upperConstant/(β/2)^288 := by
    exact (div_pos PeriodicGroundHaarScale.upperConstant_pos (pow_pos (by linarith) _)).le
  have hfirst := div_le_div_of_nonneg_right hu g.value_pos.le
  have hsecond := div_le_div_of_nonneg_left hn (div_pos eigenLowerConstant_pos (pow_pos hp _)) hl
  refine hfirst.trans (hsecond.trans_eq ?_)
  unfold ratioConstant
  rw [div_pow]
  field_simp


open PeriodicCurvatureVariance PeriodicCurvatureTransfer PeriodicSlabL2 PeriodicPlaquetteNoise
open PeriodicPlaquetteScaleObstruction PeriodicTemporalConcentration PeriodicSlabJoint

def uniformFloor : ℝ := 3/(76832*ratioConstant)

theorem uniformFloor_pos : 0<uniformFloor := by
  unfold uniformFloor
  exact div_pos (by norm_num) (mul_pos (by norm_num) ratioConstant_pos)

theorem energy_square_uniform (β : ℝ) (hb : 16777216≤β) (g : GroundData β) :
    (∫ q,energy q^2 ∂tripleLaw g)≤8*ratioConstant/β^2 := by
  have hp : 0<β := by linarith
  have h := (energy_square_scale_bound β hp g (ground (β/2))).trans
    (mul_le_mul_of_nonneg_left (eigenvalue_half_ratio β hb g (ground (β/2))) (show 0≤8/β^2 by positivity))
  convert h using 1 <;> ring

theorem plaquette_variance_uniform_upper (β : ℝ) (hb : 16777216≤β) (g : GroundData β) (p : SpatialFace) :
    variance (plaquette p) g.stationary≤32*ratioConstant/β^2 := by
  have h := (variance_bound_square β g p).trans
    (mul_le_mul_of_nonneg_left (energy_square_uniform β hb g) (by norm_num : (0 : ℝ)≤4))
  convert h using 1 <;> ring

theorem plaquette_uniform_native_loss (β : ℝ) (hb : 16777216≤β) (g : GroundData β) (p : SpatialFace) :
    uniformFloor≤‖operator g (normalized g p)-normalized g p‖ ∧
    uniformFloor≤SelfAdjointContractionIteration.dissipation (operator g) (normalized g p) ∧
    ‖operator g (normalized g p)‖^2+2*uniformFloor≤1 := by
  have hp : 0≤β := by linarith
  have hr := (div_le_iff₀ g.value_pos).mp (eigenvalue_half_ratio β hb g (ground (β/2)))
  have hq := variance_ratio_at_good_scale β (by linarith) g (ground (β/2)) p ratioConstant ratioConstant_pos hr
  refine ⟨hq.trans (normalized_residual_lower β hp g p),hq.trans (normalized_dirichlet_lower β hp g p),?_⟩
  have hn := normalized_norm_loss β hp g p
  have he : 2*((6/(49*(1+6*β)^2))/(2*variance (plaquette p) g.stationary))=
      (6/(49*(1+6*β)^2))/variance (plaquette p) g.stationary := by ring
  change 3/(76832*ratioConstant)≤_ at hq
  unfold uniformFloor
  rw [← he] at hn
  linarith


theorem plaquette_variance_two_sided (β : ℝ) (hb : 16777216≤β) (g : GroundData β) (p : SpatialFace) :
    6/(2401*β^2)≤variance (plaquette p) g.stationary ∧
    variance (plaquette p) g.stationary≤32*ratioConstant/β^2 := by
  have hp : 0<β := by linarith
  have hs : (1+6*β)^2≤49*β^2 := by
    have h := mul_nonneg (show 0≤β-1 by linarith) (show 0≤13*β+1 by linarith)
    nlinarith
  have hc : 6/(2401*β^2)≤6/(49*(1+6*β)^2) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2401*β^2)
      (by positivity : (0 : ℝ)<49*(1+6*β)^2)).mpr
    nlinarith
  exact ⟨hc.trans (PeriodicPlaquetteVarianceLower.stationary_variance_lower p β hp.le g),
    plaquette_variance_uniform_upper β hb g p⟩

end OperatorDerivativeRewrite.Foundation.PeriodicGaugeSaturatedGround
