import Foundation.FourCubePhysicalEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Actual full-cell action and partition comparisons with an explicit boundary defect budget. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeBoundaryCoercivity
open QuaternionSU2Representation SU2JointPlaquetteCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeHaarParity (InteriorState)
open FourCubeHaarChannels FourCubeIntegratedCubic FourCubePinnedHaar
open FourCubePinnedCoercivity FourCubePinnedConcentration
open FourCubeHemisphereCoercivity FourCubeHaarQuadraticLimit

attribute [local irreducible] edges upperFaces

def boundaryCost (b : Boundary → SU2) : ℝ := ∑ p : Upper,defect (word b p)

def boundaryAction (b : Boundary → SU2) (s : InteriorState) : ℝ :=
  FourCubeBoundaryCubic.fullAction (fill b s)

def perturbedAction (b : Boundary → SU2) (U : PinnedState) : ℝ :=
  boundaryAction b (fillPole 1 U)

theorem boundaryCost_nonneg (b : Boundary → SU2) : 0 ≤ boundaryCost b :=
  Finset.sum_nonneg (fun _ _ => defect_nonneg _)

theorem boundaryAction_decomposition (b : Boundary → SU2) (s : InteriorState) :
    boundaryAction b s=internalAction s+
      ∑ p : Upper,defect (s (ribbonInterior p)*word b p) := by
  unfold boundaryAction FourCubeBoundaryCubic.fullAction
  rw [retained_fill]
  simp only [ribbon_fill]
  rfl

private theorem internal_nonneg (s : InteriorState) : 0 ≤ internalAction s := by
  unfold internalAction FourCubeWilsonCubic.innerAction
  apply Finset.sum_nonneg
  intro p _
  exact defect_nonneg (faceWord s p)

theorem defect_mul (U W : SU2) : defect (U*W) ≤ 3*(defect U+defect W) := by
  simpa only [mul_one,defect_one,add_zero] using defect_triple U W 1

theorem defect_unmul (U W : SU2) : defect U ≤ 3*(defect (U*W)+defect W) := by
  simpa only [mul_inv_cancel_right,defect_inv] using defect_mul (U*W) W⁻¹

theorem boundaryAction_upper (b : Boundary → SU2) (s : InteriorState) :
    boundaryAction b s ≤ 3*vacuumAction s+3*boundaryCost b := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun p _ => defect_mul (s (ribbonInterior p)) (word b p))
  rw [boundaryAction_decomposition,vacuum_decomposition]
  unfold ribbonEnergy boundaryCost
  simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum] at hh
  nlinarith [internal_nonneg s]

theorem boundaryAction_lower (b : Boundary → SU2) (s : InteriorState) :
    vacuumAction s/3-boundaryCost b ≤ boundaryAction b s := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun p _ => defect_unmul (s (ribbonInterior p)) (word b p))
  rw [boundaryAction_decomposition,vacuum_decomposition]
  unfold ribbonEnergy boundaryCost
  simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum] at hh
  nlinarith [internal_nonneg s]

theorem perturbedAction_upper (b : Boundary → SU2) (U : PinnedState) :
    perturbedAction b U ≤ 3*pinnedAction U+3*boundaryCost b :=
  boundaryAction_upper b (fillPole 1 U)

theorem perturbedAction_lower (b : Boundary → SU2) (U : PinnedState) :
    pinnedAction U/3-boundaryCost b ≤ perturbedAction b U :=
  boundaryAction_lower b (fillPole 1 U)

theorem boltzmann_upper (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) (U : PinnedState) :
    Real.exp (-β*perturbedAction b U) ≤
      Real.exp (β*boundaryCost b)*Real.exp (-(β/3)*pinnedAction U) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [perturbedAction_lower b U]

theorem boltzmann_lower (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) (U : PinnedState) :
    Real.exp (-3*β*boundaryCost b)*Real.exp (-(3*β)*pinnedAction U) ≤
      Real.exp (-β*perturbedAction b U) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [perturbedAction_upper b U]

theorem perturbedAction_measurable (b : Boundary → SU2) : Measurable (perturbedAction b) := by
  have hp : Measurable (fun U : PinnedState => ((1 : SU2),U)) :=
    measurable_const.prodMk measurable_id
  have hm := FourCubeHaarParity.fullAction_measurable.comp
    ((fill_measurable b).comp (fillPole_measurable.comp hp))
  unfold perturbedAction boundaryAction
  simpa only [Function.comp_def] using hm

theorem perturbed_boltzmann_integrable (β : ℝ) (b : Boundary → SU2) :
    Integrable (fun U => Real.exp (-β*perturbedAction b U)) pinnedHaar := by
  apply (integrable_const (Real.exp (144*|β|))).mono'
    ((measurable_const.mul (perturbedAction_measurable b)).exp.aestronglyMeasurable)
  filter_upwards with U
  change |Real.exp (-β*perturbedAction b U)| ≤ Real.exp (144*|β|)
  exact weight_bound β b (fillPole 1 U)

theorem pinnedPartition_upper (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) :
    pinnedPartition β b ≤ Real.exp (β*boundaryCost b)*normalizer (β/3) := by
  have hh := integral_mono (perturbed_boltzmann_integrable β b)
    ((boltzmann_integrable (β/3)).const_mul (Real.exp (β*boundaryCost b)))
    (boltzmann_upper β hβ b)
  simpa only [integral_const_mul,← normalizer_integral,pinnedPartition,weight,
    perturbedAction,boundaryAction] using hh

theorem pinnedPartition_lower (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) :
    Real.exp (-3*β*boundaryCost b)*normalizer (3*β) ≤ pinnedPartition β b := by
  have hh := integral_mono
    ((boltzmann_integrable (3*β)).const_mul (Real.exp (-3*β*boundaryCost b)))
    (perturbed_boltzmann_integrable β b) (boltzmann_lower β hβ b)
  simpa only [integral_const_mul,← normalizer_integral,pinnedPartition,weight,
    perturbedAction,boundaryAction] using hh

theorem axis_defect_upper (a : Fin 3) (t : ℝ) : defect (axis a t) ≤ t^2/2 := by
  rw [defect,FourCubeWilsonCubic.axis_trace]
  have hc := Real.cos_two_mul (t/2)
  have hs := Real.sin_sq_add_cos_sq (t/2)
  have hb := Real.sin_sq_le_sq (x := t/2)
  rw [show 2*(t/2)=t by ring] at hc
  nlinarith

theorem boundaryData_defect_upper (x y z : ℝ) (c : Boundary) :
    defect (boundaryData x y z c) ≤ (x^2+y^2+z^2)/2 := by
  cases c with
  | inl c =>
    simp only [boundaryData]
    split_ifs
    · nlinarith [axis_defect_upper 0 x,sq_nonneg y,sq_nonneg z]
    · rw [defect_inv]
      nlinarith [axis_defect_upper 2 z,sq_nonneg x,sq_nonneg y]
    · rw [defect_one]
      positivity
  | inr p =>
    simp only [boundaryData]
    split_ifs
    · rw [defect_inv]
      nlinarith [axis_defect_upper 1 y,sq_nonneg x,sq_nonneg z]
    · rw [defect_one]
      positivity

theorem boundaryCost_upper (x y z : ℝ) :
    boundaryCost (boundaryData x y z) ≤ 216*(x^2+y^2+z^2) := by
  have hp (p : Upper) : defect (word (boundaryData x y z) p) ≤
      (9/2 : ℝ)*(x^2+y^2+z^2) := by
    unfold word
    have hh := defect_triple (boundaryData x y z (.inl (capHigh p)))
      (boundaryData x y z (.inr p))⁻¹ (boundaryData x y z (.inl (capLow p)))⁻¹
    rw [defect_inv,defect_inv] at hh
    nlinarith [boundaryData_defect_upper x y z (.inl (capHigh p)),
      boundaryData_defect_upper x y z (.inr p),boundaryData_defect_upper x y z (.inl (capLow p))]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  simp only [Finset.sum_const,Finset.card_univ,upper_card,nsmul_eq_mul,Nat.cast_ofNat] at hh
  unfold boundaryCost
  nlinarith

def uniformChordBoundary (W : SU2) : Boundary → SU2
  | .inl _ => 1
  | .inr _ => W⁻¹

theorem uniformChord_word (W : SU2) (p : Upper) : word (uniformChordBoundary W) p=W := by
  simp [word,uniformChordBoundary]

theorem uniformChord_cost (W : SU2) : boundaryCost (uniformChordBoundary W)=48*defect W := by
  simp only [boundaryCost,uniformChord_word,Finset.sum_const,Finset.card_univ,upper_card,
    nsmul_eq_mul,Nat.cast_ofNat]

theorem uniformChord_action_at_one (W : SU2) :
    perturbedAction (uniformChordBoundary W) 1=48*defect W := by
  have hf : fillPole 1 (1 : PinnedState)=(fun _ => (1 : SU2)) := by
    funext e
    simp [fillPole]
  have hr : ribbonEnergy (fun _ => (1 : SU2))=0 := by simp [ribbonEnergy,defect_one]
  have hi := vacuum_decomposition (fun _ => (1 : SU2))
  rw [vacuum_one,hr,add_zero] at hi
  rw [perturbedAction,hf,boundaryAction_decomposition,← hi]
  simp only [zero_add,uniformChord_word,one_mul,Finset.sum_const,Finset.card_univ,
    upper_card,nsmul_eq_mul,Nat.cast_ofNat]

/-- An actual pinned72-face counterexample: a boundary budget cannot simply be omitted. -/
theorem no_boundary_free_upper (K : ℝ) :
    ¬ ∀ (b : Boundary → SU2) (U : PinnedState),perturbedAction b U ≤ K*pinnedAction U := by
  intro h
  have hh := h (uniformChordBoundary (axis 0 Real.pi)) 1
  rw [uniformChord_action_at_one,(pinnedAction_zero_iff 1).2 rfl,mul_zero] at hh
  norm_num [defect,FourCubeWilsonCubic.axis_trace,Real.cos_pi] at hh

end OperatorDerivativeRewrite.Foundation.FourCubeBoundaryCoercivity
