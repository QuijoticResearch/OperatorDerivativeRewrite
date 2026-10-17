import Foundation.StickyPairPaths
import Foundation.ContinuousBoundedSampling

/-! Verified occupation and bounded Fourier sampling for the constructed two-point paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairSampling
open InfiniteGaussian IBMConstructedSources StickyPairPaths BrownianMassRandomTimeChange
open BrownianMassClockStoppingTime BrownianFourierMartingales ContinuousBoundedSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem source_zero : ∀ᵐ w ∂gaussianProduct, clockPath w 0=0 :=
  clock_isBrownian.toIsPreBrownianReal.eval_zero_ae_eq_zero

theorem centered_law (t : ℝ≥0) :
    HasLaw (fun w => centeredPath w t) (gaussianReal 0 t) gaussianProduct := by
  apply (clock_isBrownian.toIsPreBrownianReal.hasLaw_eval t).congr
  filter_upwards [source_zero] with w hw
  simp [centeredPath,hw]

theorem coincidence_occupation : ∀ᵐ w ∂sourceMeasure, ∀ κ T : ℝ≥0,
    BrownianClockMeasureTransport.ordinaryTime
      ({t : ℝ≥0 | leftPath κ w t=rightPath κ w t} ∩ Iic T) =
      ENNReal.ofReal ((T:ℝ)-inverse κ w.1 T) := by
  have hp : MeasurePreserving (Prod.fst : Sample → SampleSpace)
      sourceMeasure gaussianProduct := measurePreserving_fst
  filter_upwards [hp.quasiMeasurePreserving.ae source_zero,
    hp.quasiMeasurePreserving.ae BrownianStickyOccupation.zero_occupation_gap] with w hw ho κ T
  have he : {t : ℝ≥0 | leftPath κ w t=rightPath κ w t} =
      {t : ℝ≥0 | changedPath κ w.1 t=0} := by
    ext t
    rw [mem_setOf_eq,coincidence]
    simp [separationPath,centeredPath,changedPath,hw]
  rw [he]
  exact ho κ T

theorem cosine_mean (u : ℝ) (t : ℝ≥0) :
    (∫ w, cosineProcess u t w ∂gaussianProduct)=1 := by
  calc
    _ = ∫ w, gaussianProduct[cosineProcess u t | augmentedPast 0] w ∂gaussianProduct :=
      (integral_condExp (augmentedPast.le 0)).symm
    _ = ∫ w, cosineProcess u 0 w ∂gaussianProduct :=
      integral_congr_ae ((cosine_martingale u).condExp_ae_eq (by positivity : (0:ℝ≥0) ≤ t))
    _ = ∫ _ : SampleSpace, (1:ℝ) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [source_zero] with w hw
      simp [cosineProcess,weight,cosine,hw]
    _ = 1 := by simp

theorem sine_mean (u : ℝ) (t : ℝ≥0) :
    (∫ w, sineProcess u t w ∂gaussianProduct)=0 := by
  calc
    _ = ∫ w, gaussianProduct[sineProcess u t | augmentedPast 0] w ∂gaussianProduct :=
      (integral_condExp (augmentedPast.le 0)).symm
    _ = ∫ w, sineProcess u 0 w ∂gaussianProduct :=
      integral_congr_ae ((sine_martingale u).condExp_ae_eq (by positivity : (0:ℝ≥0) ≤ t))
    _ = 0 := by
      convert integral_zero SampleSpace ℝ using 1
      apply integral_congr_ae
      filter_upwards [source_zero] with w hw
      simp [sineProcess,weight,sine,hw]

theorem stopped_cosine_mean (u : ℝ) (τ : SampleSpace → ℝ≥0)
    (hτ : IsStoppingTime augmentedPast (fun w => (τ w : WithTop ℝ≥0)))
    (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    (∫ w, cosineProcess u (τ w) w ∂gaussianProduct)=1 :=
  (stopped_expectation gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) τ hτ N hN).trans (cosine_mean u N)

theorem stopped_sine_mean (u : ℝ) (τ : SampleSpace → ℝ≥0)
    (hτ : IsStoppingTime augmentedPast (fun w => (τ w : WithTop ℝ≥0)))
    (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    (∫ w, sineProcess u (τ w) w ∂gaussianProduct)=0 :=
  (stopped_expectation gaussianProduct augmentedPast (sineProcess u)
    (sine_martingale u) (sine_continuous u) τ hτ N hN).trans (sine_mean u N)

theorem inverse_cosine_mean (κ t : ℝ≥0) (u : ℝ) :
    (∫ w, cosineProcess u (inverse κ w t) w ∂gaussianProduct)=1 := by
  apply stopped_cosine_mean u _ (inverse_isStoppingTime κ t) (Nat.ceil (t:ℝ))
  intro w
  apply (inverse_le κ w t).trans
  exact_mod_cast Nat.le_ceil (t:ℝ)

theorem inverse_sine_mean (κ t : ℝ≥0) (u : ℝ) :
    (∫ w, sineProcess u (inverse κ w t) w ∂gaussianProduct)=0 := by
  apply stopped_sine_mean u _ (inverse_isStoppingTime κ t) (Nat.ceil (t:ℝ))
  intro w
  apply (inverse_le κ w t).trans
  exact_mod_cast Nat.le_ceil (t:ℝ)

end OperatorDerivativeRewrite.Foundation.StickyPairSampling
