import Foundation.StickyPairSampling
import Foundation.IBMOneTimeFourier

/-! Gaussian one-time marginals from independent compensation and stopped Fourier martingales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairMarginals
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairSampling
open BrownianMassRandomTimeChange BrownianMassClockStoppingTime BrownianFourierMartingales
open ContinuousBoundedSampling IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem observable_linear (u a b x y : ℝ) :
    observable u (a*x+b*y)=observable (u*a) x*observable (u*b) y := by
  unfold observable
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem centered_fourier (u : ℝ) (t : ℝ≥0) :
    (∫ w, observable u (centeredPath w t) ∂gaussianProduct)=
      (Real.exp (-(u^2*(t:ℝ)/2)) : ℂ) := by
  have hl := (centered_law t).integral_comp (observable_continuous u).aestronglyMeasurable
  change (∫ w, observable u (centeredPath w t) ∂gaussianProduct)=
    ∫ x, observable u x ∂gaussianReal 0 t at hl
  rw [hl,← charFun_eq_observable,charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem fiber_fourier (u a b x : ℝ) (r : ℝ≥0) :
    (∫ w, observable u (a*centeredPath w r+b*x) ∂gaussianProduct)=
      (Real.exp (-((u*a)^2*(r:ℝ)/2)) : ℂ)*observable (u*b) x := by
  simp_rw [observable_linear]
  rw [integral_mul_const,centered_fourier]

theorem weighted_phase_mean (κ t : ℝ≥0) (u : ℝ) :
    (∫ w, (weight u (inverse κ w t) : ℂ)*
      observable u (clockPath w (inverse κ w t)) ∂gaussianProduct)=1 := by
  let N : ℕ := Nat.ceil (t:ℝ)
  have hN (w : SampleSpace) : inverse κ w t ≤ N := by
    apply (inverse_le κ w t).trans
    exact_mod_cast Nat.le_ceil (t:ℝ)
  have hc := stopped_integrable gaussianProduct augmentedPast (cosineProcess u)
    (cosine_martingale u) (cosine_continuous u) (fun w => inverse κ w t)
    (inverse_isStoppingTime κ t) N hN
  have hs := stopped_integrable gaussianProduct augmentedPast (sineProcess u)
    (sine_martingale u) (sine_continuous u) (fun w => inverse κ w t)
    (inverse_isStoppingTime κ t) N hN
  have he (w : SampleSpace) :
      (weight u (inverse κ w t) : ℂ)*observable u (clockPath w (inverse κ w t)) =
      (cosineProcess u (inverse κ w t) w : ℂ)+
        (sineProcess u (inverse κ w t) w : ℂ)*Complex.I := by
    rw [observable,Complex.exp_ofReal_mul_I]
    simp only [cosineProcess,sineProcess,cosine,sine,Complex.ofReal_mul]
    ring
  simp_rw [he]
  have hi := integral_add hc.ofReal (hs.ofReal.mul_const Complex.I)
  change (∫ w, (cosineProcess u (inverse κ w t) w : ℂ)+
    (sineProcess u (inverse κ w t) w : ℂ)*Complex.I ∂gaussianProduct)=
    (∫ w, (cosineProcess u (inverse κ w t) w : ℂ) ∂gaussianProduct)+
    ∫ w, (sineProcess u (inverse κ w t) w : ℂ)*Complex.I ∂gaussianProduct at hi
  rw [hi,integral_mul_const,
    integral_complex_ofReal,integral_complex_ofReal,inverse_cosine_mean,inverse_sine_mean]
  simp

theorem compensation (κ t : ℝ≥0) (w : SampleSpace) (u a b : ℝ) (hab : a^2=b^2) :
    Real.exp (-((u*a)^2*(centerClock κ w t:ℝ)/2)) =
      Real.exp (-(u*a)^2*(t:ℝ))*weight (u*b) (inverse κ w t) := by
  rw [weight,← Real.exp_add,center_clock_real]
  congr 1
  simp only [mul_pow,hab]
  ring

def linearValue (κ t : ℝ≥0) (a b : ℝ) (w : Sample) : ℝ :=
  a*centerPath κ w t+b*separationPath κ w t

theorem linear_measurable (κ t : ℝ≥0) (a b : ℝ) : Measurable (linearValue κ t a b) :=
  (((ContinuousMap.measurable_eval t).comp (center_measurable κ)).const_mul a).add
    (((ContinuousMap.measurable_eval t).comp (separation_measurable κ)).const_mul b)

theorem balanced_fourier (κ t : ℝ≥0) (u a b : ℝ) (hab : a^2=b^2) :
    (∫ w, observable u (linearValue κ t a b w) ∂sourceMeasure)=
      (Real.exp (-(u*a)^2*(t:ℝ)) : ℂ) := by
  have hi : Integrable (fun w => observable u (linearValue κ t a b w)) sourceMeasure :=
    Integrable.of_bound ((observable_continuous u).measurable.comp
      (linear_measurable κ t a b)).aestronglyMeasurable 1
      (Eventually.of_forall fun w => (observable_norm u _).le)
  change Integrable _ (gaussianProduct.prod gaussianProduct) at hi
  calc
    _ = ∫ w, ∫ z, observable u
        (a*centeredPath z (centerClock κ w t)+b*centeredPath w (inverse κ w t))
        ∂gaussianProduct ∂gaussianProduct := integral_prod _ hi
    _ = ∫ w, (Real.exp (-((u*a)^2*(centerClock κ w t:ℝ)/2)) : ℂ)*
        observable (u*b) (centeredPath w (inverse κ w t)) ∂gaussianProduct := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => fiber_fourier u a b _ _
    _ = ∫ w, (Real.exp (-(u*a)^2*(t:ℝ)) : ℂ)*
        ((weight (u*b) (inverse κ w t) : ℂ)*
          observable (u*b) (clockPath w (inverse κ w t))) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [source_zero] with w hw
      rw [compensation κ t w u a b hab,Complex.ofReal_mul]
      simp only [centeredPath,ContinuousMap.coe_mk,hw,sub_zero]
      ring
    _ = _ := by rw [integral_const_mul,weighted_phase_mean]; ring

theorem half_law (κ t : ℝ≥0) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    HasLaw (linearValue κ t a b) (gaussianReal 0 t) sourceMeasure := by
  refine ⟨(linear_measurable κ t a b).aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_eq_observable,integral_map (linear_measurable κ t a b).aemeasurable
    (observable_continuous u).aestronglyMeasurable]
  rw [balanced_fourier κ t u a b (ha.trans hb.symm),charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  push_cast
  have ha' : (a:ℂ)^2=(1:ℂ)/2 := by
    rw [← Complex.ofReal_pow,ha]
    norm_num
  rw [mul_pow,ha']
  ring

theorem reciprocal_sqrt_square : (1/Real.sqrt (2:ℝ))^2=1/2 := by
  rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem left_law (κ t : ℝ≥0) :
    HasLaw (fun w => leftPath κ w t) (gaussianReal 0 t) sourceMeasure := by
  apply (half_law κ t (1/Real.sqrt 2) (1/Real.sqrt 2)
    reciprocal_sqrt_square reciprocal_sqrt_square).congr
  exact Eventually.of_forall fun w => by
    dsimp [linearValue,leftPath]
    ring

theorem right_law (κ t : ℝ≥0) :
    HasLaw (fun w => rightPath κ w t) (gaussianReal 0 t) sourceMeasure := by
  have hb : (-1/Real.sqrt (2:ℝ))^2=1/2 := by
    rw [neg_div,neg_sq]
    exact reciprocal_sqrt_square
  apply (half_law κ t (1/Real.sqrt 2) (-1/Real.sqrt 2) reciprocal_sqrt_square hb).congr
  exact Eventually.of_forall fun w => by
    dsimp [linearValue,rightPath]
    ring

end OperatorDerivativeRewrite.Foundation.StickyPairMarginals
