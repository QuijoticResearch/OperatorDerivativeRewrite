import Foundation.BrownianC2MartingaleRealization
import Foundation.BrownianOccupationIntegralTransport
import Foundation.BrownianTimeChangedMartingales
import Foundation.AmbientMartingaleModification

/-! A genuine boundary-test martingale for the constructed sticky candidate.
The boundary condition follows from actual one-sided derivatives. No transition
semigroup, uniqueness, strong Markov property or multiparticle flow is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.StickyC2MartingaleProblem
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
open BrownianMassClockStoppingTime BrownianTimeChangedMartingales
open ContinuousTimeChangeMartingale BrownianC2MartingaleRealization
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)

def coefficient (κ : ℝ≥0) : ℝ := (κ : ℝ)/2*deriv (deriv f) 0
def boundaryTest (κ : ℝ≥0) (x : ℝ) : ℝ := f x+coefficient f κ*|x|
def physicalDrift (κ : ℝ≥0) (ω : SampleSpace) (t : ℝ≥0) : ℝ :=
  (1/2 : ℝ)*∫ s in 0..(t : ℝ), deriv (deriv f) (changedPath κ ω s.toNNReal)
def boundaryProcess (κ : ℝ≥0) (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  boundaryTest f κ (changedPath κ ω t)-boundaryTest f κ 0-physicalDrift f κ ω t

include hf in
theorem boundaryTest_continuous (κ : ℝ≥0) : Continuous (boundaryTest f κ) :=
  hf.continuous.add (continuous_const.mul continuous_abs)

include hf in
theorem physicalDrift_measurable (κ t : ℝ≥0) : Measurable (fun ω => physicalDrift f κ ω t) := by
  have hq : Measurable (fun z : ℝ × SampleSpace => (z.1.toNNReal,z.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hm : Measurable (fun z : ℝ × SampleSpace =>
      deriv (deriv f) (changedPath κ z.2 z.1.toNNReal)) :=
    (GaussianC2Ito.second_continuous f hf).measurable.comp ((changedPath_joint κ).comp hq)
  have hm' : StronglyMeasurable (fun z : SampleSpace × ℝ =>
      deriv (deriv f) (changedPath κ z.1 z.2.toNNReal)) :=
    (hm.comp measurable_swap).stronglyMeasurable
  have hi := hm'.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (t : ℝ)))
  unfold physicalDrift
  simp only [intervalIntegral.integral_of_le t.coe_nonneg]
  exact hi.measurable.const_mul (1/2 : ℝ)

include hf in
theorem boundaryProcess_measurable (κ t : ℝ≥0) : Measurable (boundaryProcess f κ t) :=
  (((boundaryTest_continuous f hf κ).measurable.comp
    (changedPath_coordinate_measurable κ t)).sub_const (boundaryTest f κ 0)).sub
      (physicalDrift_measurable f hf κ t)

include hf K0 K1 h0 h1

theorem changed_compensated_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => compensatedPath f hf ω (inverse κ ω t))
      (physicalPast κ) gaussianProduct :=
  changed_martingale gaussianProduct augmentedPast (fun t ω => compensatedPath f hf ω t)
    (fun t ω => inverse κ ω t) (inverse_isStoppingTime κ) (fun ω => inverse_monotone κ ω)
    (compensated_martingale f hf K0 K1 h0 h1) (fun ω => (compensatedPath f hf ω).continuous)
    (fun t ω => inverse_le κ ω t)

theorem physicalDrift_transport : ∀ᵐ ω ∂gaussianProduct, ∀ κ t : ℝ≥0,
    physicalDrift f κ ω t = primitive f ω (inverse κ ω t)+
      coefficient f κ*compensator κ t ω := by
  have h := BrownianOccupationIntegralTransport.bounded_observation_transport
    (deriv (deriv f)) (GaussianC2Ito.second_continuous f hf) K1 (fun x => h1 x)
  filter_upwards [h] with ω hω κ t
  have ht := hω κ t
  unfold physicalDrift primitive rate coefficient compensator
  rw [ht]
  ring

theorem boundaryProcess_decomposition (κ : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0,
    boundaryProcess f κ t ω = compensatedPath f hf ω (inverse κ ω t)+
      coefficient f κ*changedSignPath κ ω t := by
  filter_upwards [physicalDrift_transport f hf K0 K1 h0 h1, tanaka_physical κ] with ω hd ht t
  have htan := ht t
  unfold boundaryProcess boundaryTest
  rw [hd κ t]
  change f (changedPath κ ω t)+coefficient f κ*|changedPath κ ω t|-
    (f 0+coefficient f κ*|0|)-
    (primitive f ω (inverse κ ω t)+coefficient f κ*compensator κ t ω) =
    (f (changedPath κ ω t)-f 0-primitive f ω (inverse κ ω t))+
      coefficient f κ*changedSignPath κ ω t
  rw [htan]
  norm_num
  ring

def augmentedPhysicalPast (κ : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  AmbientNullAugmentation.filtration gaussianProduct (physicalPast κ)

theorem boundaryProcess_martingale (κ : ℝ≥0) :
    Martingale (boundaryProcess f κ) (augmentedPhysicalPast κ) gaussianProduct := by
  have hM := (changed_compensated_martingale f hf K0 K1 h0 h1 κ).add
    (Martingale.smul (coefficient f κ) (changed_sign_martingale κ))
  apply AmbientMartingaleModification.martingale_modification gaussianProduct (physicalPast κ)
    _ (boundaryProcess f κ) hM (boundaryProcess_measurable f hf κ)
  intro t
  filter_upwards [boundaryProcess_decomposition f hf K0 K1 h0 h1 κ] with ω hω
  exact hω t

omit K0 K1 h0 h1 in
theorem right_derivative (κ : ℝ≥0) :
    HasDerivWithinAt (boundaryTest f κ) (deriv f 0+coefficient f κ) (Ici 0) 0 := by
  have h := ((hf.differentiable (by norm_num) 0).hasDerivAt.add
    ((hasDerivAt_id (0 : ℝ)).const_mul (coefficient f κ))).hasDerivWithinAt (s := Ici 0)
  simp only [mul_one] at h
  apply h.congr
  · intro x hx
    change 0 ≤ x at hx
    simp [boundaryTest, abs_of_nonneg hx]
  · simp [boundaryTest]

omit K0 K1 h0 h1 in
theorem left_derivative (κ : ℝ≥0) :
    HasDerivWithinAt (boundaryTest f κ) (deriv f 0-coefficient f κ) (Iic 0) 0 := by
  have h := ((hf.differentiable (by norm_num) 0).hasDerivAt.sub
    ((hasDerivAt_id (0 : ℝ)).const_mul (coefficient f κ))).hasDerivWithinAt (s := Iic 0)
  simp only [mul_one] at h
  apply h.congr
  · intro x hx
    change x ≤ 0 at hx
    simp only [boundaryTest, abs_of_nonpos hx, Pi.sub_apply, id_eq]
    ring
  · simp [boundaryTest]

omit hf K0 K1 h0 h1 in
theorem boundary_jump (κ : ℝ≥0) :
    (deriv f 0+coefficient f κ)-(deriv f 0-coefficient f κ) =
      2*(κ : ℝ)*((1/2 : ℝ)*deriv (deriv f) 0) := by
  unfold coefficient
  ring

end OperatorDerivativeRewrite.Foundation.StickyC2MartingaleProblem
