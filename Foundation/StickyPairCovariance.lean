import Foundation.StickyPairDiagonal

/-! Exact covariance of the constructed Gaussian-marginal pair equals expected sticky occupation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairCovariance
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairSampling StickyPairMarginals
open BrownianMassRandomTimeChange BrownianTimeChangedVariance
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem left_L2 (κ t : ℝ≥0) : MemLp (fun w => leftPath κ w t) 2 sourceMeasure :=
  (left_law κ t).memLp (memLp_id_gaussianReal 2)

theorem right_L2 (κ t : ℝ≥0) : MemLp (fun w => rightPath κ w t) 2 sourceMeasure :=
  (right_law κ t).memLp (memLp_id_gaussianReal 2)

theorem left_mean (κ t : ℝ≥0) : (∫ w, leftPath κ w t ∂sourceMeasure)=0 := by
  have h := (left_law κ t).integral_comp measurable_id.aestronglyMeasurable
  simpa only [Function.comp_def,id_eq,integral_id_gaussianReal] using h

theorem right_mean (κ t : ℝ≥0) : (∫ w, rightPath κ w t ∂sourceMeasure)=0 := by
  have h := (right_law κ t).integral_comp measurable_id.aestronglyMeasurable
  simpa only [Function.comp_def,id_eq,integral_id_gaussianReal] using h

theorem gaussian_square (t : ℝ≥0) : (∫ x : ℝ, x^2 ∂gaussianReal 0 t)=(t:ℝ) := by
  have h := variance_id_gaussianReal (μ := 0) (v := t)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa only [integral_id_gaussianReal,sub_zero,id_eq] using h

theorem left_square (κ t : ℝ≥0) : (∫ w, (leftPath κ w t)^2 ∂sourceMeasure)=(t:ℝ) := by
  have h := (left_law κ t).integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 t) from by fun_prop)
  change (∫ w, (leftPath κ w t)^2 ∂sourceMeasure)=∫ x : ℝ, x^2 ∂gaussianReal 0 t at h
  exact h.trans (gaussian_square t)

theorem right_square (κ t : ℝ≥0) : (∫ w, (rightPath κ w t)^2 ∂sourceMeasure)=(t:ℝ) := by
  have h := (right_law κ t).integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => x^2) (gaussianReal 0 t) from by fun_prop)
  change (∫ w, (rightPath κ w t)^2 ∂sourceMeasure)=∫ x : ℝ, x^2 ∂gaussianReal 0 t at h
  exact h.trans (gaussian_square t)

theorem difference_square (κ t : ℝ≥0) :
    (∫ w, (leftPath κ w t-rightPath κ w t)^2 ∂sourceMeasure)=
      2*∫ w, (inverse κ w t:ℝ) ∂gaussianProduct := by
  have hp : MeasurePreserving (Prod.fst : Sample → SampleSpace)
      sourceMeasure gaussianProduct := measurePreserving_fst
  have hf : HasLaw (Prod.fst : Sample → SampleSpace) gaussianProduct sourceMeasure :=
    ⟨measurable_fst.aemeasurable,hp.map_eq⟩
  calc
    _ = ∫ w : Sample, 2*(changedPath κ w.1 t)^2 ∂sourceMeasure := by
      apply integral_congr_ae
      filter_upwards [hp.quasiMeasurePreserving.ae source_zero] with w hw
      rw [difference,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      simp [separationPath,centeredPath,changedPath,hw]
    _ = 2*∫ w : Sample, (changedPath κ w.1 t)^2 ∂sourceMeasure := integral_const_mul _ _
    _ = 2*∫ w, (changedPath κ w t)^2 ∂gaussianProduct := by
      congr 1
      exact hf.integral_comp (changed_square_integrable κ t).aestronglyMeasurable
    _ = _ := by rw [changed_second_moment]

theorem product_integrable (κ t : ℝ≥0) :
    Integrable (fun w => leftPath κ w t*rightPath κ w t) sourceMeasure :=
  (left_L2 κ t).integrable_mul (right_L2 κ t)

theorem product_holding (κ t : ℝ≥0) :
    (∫ w, leftPath κ w t*rightPath κ w t ∂sourceMeasure)=
      ∫ w, BrownianStickyNontriviality.occupation κ w t ∂gaussianProduct := by
  have he : (fun w : Sample => (leftPath κ w t-rightPath κ w t)^2)=
      (fun w => (leftPath κ w t)^2+(rightPath κ w t)^2-
        2*(leftPath κ w t*rightPath κ w t)) := by
    funext w
    ring
  have hd := difference_square κ t
  have hi := integral_sub ((left_L2 κ t).integrable_sq.add (right_L2 κ t).integrable_sq)
    ((product_integrable κ t).const_mul 2)
  simp only [Pi.add_apply] at hi
  rw [he,hi,
    integral_add (left_L2 κ t).integrable_sq (right_L2 κ t).integrable_sq,
    integral_const_mul,left_square,right_square] at hd
  have hb := holding_variance_balance κ t
  rw [changed_second_moment] at hb
  linarith

theorem covariance_holding (κ t : ℝ≥0) :
    cov[(fun w => leftPath κ w t),(fun w => rightPath κ w t);sourceMeasure]=
      ∫ w, BrownianStickyNontriviality.occupation κ w t ∂gaussianProduct := by
  rw [covariance_eq_sub (left_L2 κ t) (right_L2 κ t),left_mean,right_mean]
  simp only [Pi.mul_apply,mul_zero,sub_zero]
  exact product_holding κ t

theorem covariance_positive (κ t : ℝ≥0) (hκ : 0 < κ) (ht : 0 < t) :
    0 < cov[(fun w => leftPath κ w t),(fun w => rightPath κ w t);sourceMeasure] := by
  rw [covariance_holding]
  exact BrownianStickyNontriviality.expected_occupation_pos κ t hκ ht

theorem not_independent (κ t : ℝ≥0) (hκ : 0 < κ) (ht : 0 < t) :
    ¬ IndepFun (fun w => leftPath κ w t) (fun w => rightPath κ w t) sourceMeasure := by
  intro hi
  have hz := hi.covariance_eq_zero (left_L2 κ t) (right_L2 κ t)
  have hp := covariance_positive κ t hκ ht
  rw [hz] at hp
  exact (lt_irrefl 0) hp

end OperatorDerivativeRewrite.Foundation.StickyPairCovariance
