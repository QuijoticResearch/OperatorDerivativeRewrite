import Foundation.FourCubeBoundaryCubic
import Foundation.SU2GaugeCovariantTransfer
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact finite-cell integration repair for the boundary cubic witness.
The interior integration is over ALL32 SU2 links with genuine product Haar law. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarParity
open QuaternionSU2Representation SU2JointPlaquetteCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex FourCubeChordIncidence
open FourCubeWilsonCubic FourCubeBoundaryCubic
attribute [local irreducible] upperFaces edges

/-- The quarter turn is a unit SU2 group element, not a formal reflection. -/
def turn (a : Fin 3) : SU2 := axis a (Real.pi/2)

theorem turn_axis (a b : Fin 3) (t : ℝ) :
    turn a*axis b t*(turn a)⁻¹=axis b (if a=b then t else -t) := by
  unfold turn axis
  rw [← hom.map_inv,← hom.map_mul,← hom.map_mul]
  congr 1
  apply Subtype.ext
  change axisRaw a (Real.pi/2)*axisRaw b t*star (axisRaw a (Real.pi/2))=
    axisRaw b (if a=b then t else -t)
  fin_cases a <;> fin_cases b <;> ext <;>
    simp [axisRaw,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

def conjugate (g : SU2) (U : FullEdge → SU2) : FullEdge → SU2 :=
  fun e => g*U e*g⁻¹

theorem retained_conjugate (g : SU2) (U : FullEdge → SU2) :
    retained (conjugate g U)=gaugeField (fun _ => g) (retained U) := by
  funext e
  by_cases he : e∈edges <;> simp [retained,conjugate,gaugeField,he]

theorem ribbon_conjugate (g : SU2) (U : FullEdge → SU2) (p : Upper) :
    ribbonWord (conjugate g U) p=g*ribbonWord U p*g⁻¹ := by
  unfold ribbonWord conjugate
  group

theorem fullAction_conjugate (g : SU2) (U : FullEdge → SU2) :
    fullAction (conjugate g U)=fullAction U := by
  unfold fullAction
  rw [retained_conjugate,innerAction_gauge]
  simp_rw [ribbon_conjugate,halfTrace_conjugate]

abbrev InteriorState := Interior → SU2

def interiorHaar : Measure InteriorState := Measure.pi (fun _ => law)
instance interiorHaar_probability : IsProbabilityMeasure interiorHaar := by
  unfold interiorHaar
  infer_instance

def interiorConjugate (g : SU2) (s : InteriorState) : InteriorState :=
  fun e => g*s e*g⁻¹

theorem interiorConjugate_preserving (g : SU2) :
    MeasurePreserving (interiorConjugate g) interiorHaar interiorHaar := by
  unfold interiorConjugate interiorHaar
  apply measurePreserving_pi (fun _ : Interior => law) (fun _ : Interior => law)
    (f := fun (_ : Interior) (C : SU2) => g*C*g⁻¹)
  intro e
  exact ⟨(measurable_mul_const g⁻¹).comp (measurable_const_mul g),
    SU2GaugeCovariantTransfer.haar_conjugation_map g⟩

def boundaryField (x y : ℝ) (s : InteriorState) : FullEdge → SU2
  | .inl e => s e
  | .inr (.inl c) => if c.val=chosenCap.val then axis 0 x else 1
  | .inr (.inr p) => if p.val=chosenRibbon.val then (axis 1 y)⁻¹ else 1

/-- The pointwise cubic witness embeds into the genuine all-interior family. -/
theorem witness_inclusion (x y z : ℝ) :
    boundaryField x y (fun e => if e.val=edgeA then axis 2 z else 1)=links x y z := by
  funext e
  cases e with
  | inl e => rfl
  | inr e => cases e <;> rfl

theorem boundaryField_conjugate (g : SU2) (x y x' y' : ℝ) (s : InteriorState)
    (hx : g*axis 0 x*g⁻¹=axis 0 x') (hy : g*axis 1 y*g⁻¹=axis 1 y') :
    conjugate g (boundaryField x y s)=boundaryField x' y' (interiorConjugate g s) := by
  funext e
  cases e with
  | inl e => rfl
  | inr e =>
    cases e with
    | inl c =>
      by_cases hc : c.val=chosenCap.val <;> simp [conjugate,boundaryField,hc,hx]
    | inr p =>
      have hi : g*(axis 1 y)⁻¹*g⁻¹=(g*axis 1 y*g⁻¹)⁻¹ := by group
      by_cases hp : p.val=chosenRibbon.val <;> simp [conjugate,boundaryField,hp,hi,hy]

theorem boundaryField_flip_y (x y : ℝ) (s : InteriorState) :
    conjugate (turn 0) (boundaryField x y s)=
      boundaryField x (-y) (interiorConjugate (turn 0) s) := by
  apply boundaryField_conjugate
  · simpa using turn_axis 0 0 x
  · simpa using turn_axis 0 1 y

theorem boundaryField_flip_x (x y : ℝ) (s : InteriorState) :
    conjugate (turn 1) (boundaryField x y s)=
      boundaryField (-x) y (interiorConjugate (turn 1) s) := by
  apply boundaryField_conjugate
  · simpa using turn_axis 1 0 x
  · simpa using turn_axis 1 1 y

theorem boundaryField_measurable (x y : ℝ) : Measurable (boundaryField x y) := by
  apply measurable_pi_iff.mpr
  intro e
  cases e with
  | inl e => exact measurable_pi_apply e
  | inr e =>
    cases e with
    | inl c => exact measurable_const
    | inr p => exact measurable_const

private theorem traceWord_measurable {ι : Type} (a b c d : ι) :
    Measurable (fun U : ι → SU2 => halfTrace (U a*U b*(U c)⁻¹*(U d)⁻¹)) :=
  halfTrace_measurable.comp ((((measurable_pi_apply a).mul (measurable_pi_apply b)).mul
    (measurable_pi_apply c).inv).mul (measurable_pi_apply d).inv)

private theorem retained_measurable : Measurable retained := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e∈edges
  · simpa only [retained,dif_pos he] using (measurable_pi_apply ((Sum.inl ⟨e,he⟩) : FullEdge))
  · simp only [retained,dif_neg he]
    exact measurable_const

private theorem face_measurable (p : FaceData) : Measurable (fun U : EdgeData → SU2 => faceAction U p) :=
  measurable_const.sub (traceWord_measurable (ι := EdgeData) (faceEdge p 0) (faceEdge p 1) (faceEdge p 2) (faceEdge p 3))

private theorem ribbon_measurable (p : Upper) :
    Measurable (fun U : FullEdge → SU2 => 1-halfTrace (ribbonWord U p)) :=
  measurable_const.sub (traceWord_measurable (ι := FullEdge) (.inl (ribbonInterior p))
    (.inr (.inl (capHigh p))) (.inr (.inr p)) (.inr (.inl (capLow p))))

theorem fullAction_measurable : Measurable fullAction :=
  (Finset.measurable_sum _ (fun p _ => (face_measurable p).comp retained_measurable)).add
    (Finset.measurable_sum _ (fun p _ => ribbon_measurable p))

def boltzmann (β x y : ℝ) (s : InteriorState) : ℝ :=
  Real.exp (-β*fullAction (boundaryField x y s))

def partition (β x y : ℝ) : ℝ := ∫ s, boltzmann β x y s ∂interiorHaar

theorem boltzmann_measurable (β x y : ℝ) : Measurable (boltzmann β x y) :=
  (measurable_const.mul (fullAction_measurable.comp (boundaryField_measurable x y))).exp

theorem fullAction_bounds (U : FullEdge → SU2) : 0 ≤ fullAction U ∧ fullAction U ≤ 144 := by
  have hb (A : SU2) : 0 ≤ 1-halfTrace A ∧ 1-halfTrace A ≤ 2 := by
    have h := abs_le.mp (halfTrace_bound A)
    constructor <;> linarith
  have hf (p : FaceData) : 0 ≤ faceAction (retained U) p ∧ faceAction (retained U) p ≤ 2 :=
    hb (retained U (faceEdge p 0)*retained U (faceEdge p 1)*
      (retained U (faceEdge p 2))⁻¹*(retained U (faceEdge p 3))⁻¹)
  unfold fullAction innerAction
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun p _ => (hf p).1))
      (Finset.sum_nonneg (fun p _ => (hb (ribbonWord U p)).1))
  · calc
      _ ≤ (∑ p∈innerFaces, (2:ℝ))+(∑ _p : Upper, (2:ℝ)) :=
        add_le_add (Finset.sum_le_sum (fun p _ => (hf p).2))
          (Finset.sum_le_sum (fun p _ => (hb (ribbonWord U p)).2))
      _ = 144 := by norm_num [innerFaces_card,upperFaces_card]

theorem boltzmann_bounds (β x y : ℝ) (s : InteriorState) :
    Real.exp (-(|β| *144)) ≤ boltzmann β x y s ∧
      boltzmann β x y s ≤ Real.exp (|β| *144) := by
  have hs := fullAction_bounds (boundaryField x y s)
  have ha : |-β*fullAction (boundaryField x y s)| ≤ |β| *144 := by
    rw [abs_mul,abs_neg,abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_left hs.2 (abs_nonneg β)
  exact ⟨Real.exp_le_exp.mpr (neg_le_of_abs_le ha),Real.exp_le_exp.mpr (le_of_abs_le ha)⟩

theorem boltzmann_integrable (β x y : ℝ) : Integrable (boltzmann β x y) interiorHaar :=
  Integrable.of_bound (boltzmann_measurable β x y).aestronglyMeasurable (Real.exp (|β| *144))
    (Filter.Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs,boltzmann,abs_of_pos (Real.exp_pos _)] using (boltzmann_bounds β x y s).2)

theorem partition_bounds (β x y : ℝ) : Real.exp (-(|β| *144)) ≤ partition β x y ∧
    partition β x y ≤ Real.exp (|β| *144) := by
  constructor
  · have h := integral_mono (integrable_const (Real.exp (-(|β| *144))))
      (boltzmann_integrable β x y) (fun s => (boltzmann_bounds β x y s).1)
    simpa only [partition,integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono (boltzmann_integrable β x y)
      (integrable_const (Real.exp (|β| *144))) (fun s => (boltzmann_bounds β x y s).2)
    simpa only [partition,integral_const,probReal_univ,one_smul] using h

theorem partition_pos (β x y : ℝ) : 0 < partition β x y :=
  lt_of_lt_of_le (Real.exp_pos _) (partition_bounds β x y).1

private theorem integral_conjugate (g : SU2) (f : InteriorState → ℝ) (hf : Measurable f) :
    (∫ s, f (interiorConjugate g s) ∂interiorHaar)=∫ s, f s ∂interiorHaar := by
  have h := integral_map (μ := interiorHaar) (interiorConjugate_preserving g).measurable.aemeasurable hf.aestronglyMeasurable
  rw [(interiorConjugate_preserving g).map_eq] at h
  exact h.symm

theorem boltzmann_flip_y (β x y : ℝ) (s : InteriorState) :
    boltzmann β x (-y) (interiorConjugate (turn 0) s)=boltzmann β x y s := by
  unfold boltzmann
  rw [← boundaryField_flip_y,fullAction_conjugate]

theorem boltzmann_flip_x (β x y : ℝ) (s : InteriorState) :
    boltzmann β (-x) y (interiorConjugate (turn 1) s)=boltzmann β x y s := by
  unfold boltzmann
  rw [← boundaryField_flip_x,fullAction_conjugate]

/-- Exact ALL-interior Haar identity, not a formal Gaussian parity argument. -/
theorem partition_even_y (β x y : ℝ) : partition β x (-y)=partition β x y := by
  unfold partition
  rw [← integral_conjugate (turn 0) _ (boltzmann_measurable β x (-y))]
  simp_rw [boltzmann_flip_y]

theorem partition_even_x (β x y : ℝ) : partition β (-x) y=partition β x y := by
  unfold partition
  rw [← integral_conjugate (turn 1) _ (boltzmann_measurable β (-x) y)]
  simp_rw [boltzmann_flip_x]

/-- Dimensionless effective action; positivity of the genuine partition
was proved above. No derivative/integral interchange is assumed. -/
def freeEnergy (β x y : ℝ) : ℝ := -Real.log (partition β x y)

theorem freeEnergy_even_y (β x y : ℝ) : freeEnergy β x (-y)=freeEnergy β x y := by
  rw [freeEnergy,freeEnergy,partition_even_y]

theorem freeEnergy_even_x (β x y : ℝ) : freeEnergy β (-x) y=freeEnergy β x y := by
  rw [freeEnergy,freeEnergy,partition_even_x]

theorem freeEnergy_centered_mixed_difference (β h k : ℝ) :
    freeEnergy β h k-freeEnergy β (-h) k-freeEnergy β h (-k)+freeEnergy β (-h) (-k)=0 := by
  rw [freeEnergy_even_x,freeEnergy_even_x,freeEnergy_even_y]
  ring

theorem partition_zero_coupling (x y : ℝ) : partition 0 x y=1 := by
  simp [partition,boltzmann]

/-- Normalization for literal reuse of the verified bounded-tilt calculus. -/
def normalizedAction (x y : ℝ) (s : InteriorState) : ℝ :=
  -fullAction (boundaryField x y s)/144

theorem normalizedAction_measurable (x y : ℝ) : Measurable (normalizedAction x y) :=
  (fullAction_measurable.comp (boundaryField_measurable x y)).neg.div_const 144

theorem normalizedAction_bound (x y : ℝ) (s : InteriorState) : |normalizedAction x y s| ≤ 1 := by
  have h := fullAction_bounds (boundaryField x y s)
  rw [normalizedAction,abs_div,abs_neg,abs_of_nonneg h.1]
  rw [abs_of_pos (by norm_num : (0:ℝ)<144)]
  exact (div_le_one (by norm_num : (0:ℝ)<144)).mpr h.2

theorem scaled_exponent (β x y : ℝ) (s : InteriorState) :
    (144*β)*normalizedAction x y s=-β*fullAction (boundaryField x y s) := by
  unfold normalizedAction
  ring

theorem partition_tilt (β x y : ℝ) :
    BoundedExponentialTiltResponse.partition interiorHaar (normalizedAction x y) (144*β)=partition β x y := by
  unfold BoundedExponentialTiltResponse.partition BoundedExponentialTiltResponse.weighted
  simp only [one_mul,scaled_exponent]
  rfl

def cellLaw (β x y : ℝ) : Measure InteriorState :=
  BoundedExponentialTiltResponse.tiltedMeasure interiorHaar (normalizedAction x y) (144*β)

instance cellLaw_probability (β x y : ℝ) : IsProbabilityMeasure (cellLaw β x y) :=
  BoundedExponentialTiltResponse.tiltedMeasure_probability interiorHaar (normalizedAction x y)
    (normalizedAction_measurable x y) (normalizedAction_bound x y) (144*β)

theorem cellLaw_density (β x y : ℝ) : cellLaw β x y=
    interiorHaar.withDensity (fun s => ENNReal.ofReal (boltzmann β x y s/partition β x y)) := by
  unfold cellLaw BoundedExponentialTiltResponse.tiltedMeasure BoundedExponentialTiltResponse.density
  simp only [scaled_exponent,partition_tilt]
  rfl

/-- Actual normalized Gibbs expectation, identified with the existing operator
response calculus rather than an abstract uninstantiated probability law. -/
theorem cellLaw_integral (β x y : ℝ) (f : InteriorState → ℝ) :
    (∫ s, f s ∂cellLaw β x y)=
      (∫ s, f s*boltzmann β x y s ∂interiorHaar)/partition β x y := by
  unfold cellLaw
  rw [BoundedExponentialTiltResponse.tilted_integral interiorHaar (normalizedAction x y) f
    (normalizedAction_measurable x y) (normalizedAction_bound x y) (144*β)]
  unfold BoundedExponentialTiltResponse.expectation BoundedExponentialTiltResponse.weighted
  simp only [scaled_exponent,partition_tilt]
  rfl

end OperatorDerivativeRewrite.Foundation.FourCubeHaarParity
