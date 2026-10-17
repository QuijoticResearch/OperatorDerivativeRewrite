import Foundation.BrownianTwoTimeFourier

/-! Actual two-time Fourier laws of the constructed sticky pair's balanced coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairTwoTimeFourier
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairSampling StickyPairMarginals
open BrownianMassRandomTimeChange BrownianComplexSampling BrownianCompensatedSampling
open BrownianTwoTimeFourier BrownianFourierMartingales IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem phase_exp (u : ℝ) (r : ℝ≥0) (w : SampleSpace) :
    phase u r w=Complex.exp (((u^2*(r:ℝ)/2:ℝ):ℂ)+((u*clockPath w r:ℝ):ℂ)*Complex.I) := by
  rw [phase_eq,weight,observable,Complex.ofReal_exp,← Complex.exp_add]

theorem compensation (κ s t : ℝ≥0) (w : SampleSpace) (p q a b : ℝ) (hab : a^2=b^2) :
    (Real.exp (-(((p*a+q*a)^2)*(centerClock κ w s:ℝ)+
      (q*a)^2*((centerClock κ w t:ℝ)-centerClock κ w s))/2) : ℂ)*
      observable (p*b) (clockPath w (inverse κ w s))*
      observable (q*b) (clockPath w (inverse κ w t)) =
    (Real.exp (-(a^2)*((p+q)^2*(s:ℝ)+q^2*((t:ℝ)-s))) : ℂ)*
      (phaseRatio ((p+q)*b) (q*b) (fun w => inverse κ w s) w*
        phase (q*b) (inverse κ w t) w) := by
  have habC : (a:ℂ)^2=(b:ℂ)^2 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow,hab]
  simp only [phaseRatio,phase_exp,observable,Complex.ofReal_exp]
  rw [← Complex.exp_sub]
  simp only [← Complex.exp_add]
  congr 1
  rw [center_clock_real,center_clock_real]
  push_cast
  simp only [add_mul,mul_pow,habC]
  ring_nf
  rw [habC]
  ring

theorem fiber (κ s t : ℝ≥0) (hst : s ≤ t) (w : SampleSpace) (p q a b : ℝ) :
    (∫ z, observable p (linearValue κ s a b (w,z))*
      observable q (linearValue κ t a b (w,z)) ∂gaussianProduct)=
    (Real.exp (-((p*a+q*a)^2*(centerClock κ w s:ℝ)+
      (q*a)^2*((centerClock κ w t:ℝ)-centerClock κ w s))/2) : ℂ)*
      observable (p*b) (centeredPath w (inverse κ w s))*
      observable (q*b) (centeredPath w (inverse κ w t)) := by
  change (∫ z, observable p (a*centeredPath z (centerClock κ w s)+
    b*centeredPath w (inverse κ w s))*observable q
    (a*centeredPath z (centerClock κ w t)+b*centeredPath w (inverse κ w t))
    ∂gaussianProduct)=_
  simp_rw [observable_linear]
  have he (z : SampleSpace) :
      (observable (p*a) (centeredPath z (centerClock κ w s))*
        observable (p*b) (centeredPath w (inverse κ w s)))*
      (observable (q*a) (centeredPath z (centerClock κ w t))*
        observable (q*b) (centeredPath w (inverse κ w t))) =
      (observable (p*a) (centeredPath z (centerClock κ w s))*
        observable (q*a) (centeredPath z (centerClock κ w t)))*
      (observable (p*b) (centeredPath w (inverse κ w s))*
        observable (q*b) (centeredPath w (inverse κ w t))) := by ring
  simp_rw [he]
  rw [integral_mul_const,centered_two_time_fourier (p*a) (q*a)
    (centerClock κ w s) (centerClock κ w t) (center_clock_monotone κ w hst)]
  ring

theorem balanced_two_time (κ s t : ℝ≥0) (hst : s ≤ t) (p q a b : ℝ) (hab : a^2=b^2) :
    (∫ w, observable p (linearValue κ s a b w)*observable q (linearValue κ t a b w)
      ∂sourceMeasure)=
    (Real.exp (-(a^2)*((p+q)^2*(s:ℝ)+q^2*((t:ℝ)-s))) : ℂ) := by
  have hi : Integrable (fun w => observable p (linearValue κ s a b w)*
      observable q (linearValue κ t a b w)) sourceMeasure := by
    apply Integrable.of_bound
      (((observable_continuous p).measurable.comp (linear_measurable κ s a b)).mul
        ((observable_continuous q).measurable.comp (linear_measurable κ t a b))).aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by
      change ‖observable p (linearValue κ s a b w)*
        observable q (linearValue κ t a b w)‖ ≤ 1
      simp only [norm_mul,observable_norm,mul_one,le_refl]
  change Integrable _ (gaussianProduct.prod gaussianProduct) at hi
  calc
    _ = ∫ w, ∫ z, observable p (linearValue κ s a b (w,z))*
        observable q (linearValue κ t a b (w,z)) ∂gaussianProduct ∂gaussianProduct :=
      integral_prod _ hi
    _ = ∫ w, (Real.exp (-((p*a+q*a)^2*(centerClock κ w s:ℝ)+
        (q*a)^2*((centerClock κ w t:ℝ)-centerClock κ w s))/2) : ℂ)*
        observable (p*b) (centeredPath w (inverse κ w s))*
        observable (q*b) (centeredPath w (inverse κ w t)) ∂gaussianProduct := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => fiber κ s t hst w p q a b
    _ = ∫ w, (Real.exp (-(a^2)*((p+q)^2*(s:ℝ)+q^2*((t:ℝ)-s))) : ℂ)*
        (phaseRatio ((p+q)*b) (q*b) (fun w => inverse κ w s) w*
          phase (q*b) (inverse κ w t) w) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [source_zero] with w hw
      simp only [centeredPath,ContinuousMap.coe_mk,hw,sub_zero]
      exact compensation κ s t w p q a b hab
    _ = _ := by
      rw [integral_const_mul,inverse_two_phase_mean κ s t hst]
      ring

theorem map_pair_eq_of_fourier {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X Y : Ω → ℝ) (X' Y' : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hX' : Measurable X') (hY' : Measurable Y')
    (h : ∀ p q : ℝ, (∫ w, observable p (X w)*observable q (Y w) ∂μ)=
      ∫ w, observable p (X' w)*observable q (Y' w) ∂ν) :
    μ.map (fun w => (X w,Y w))=ν.map (fun w => (X' w,Y' w)) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,
    integral_map (hX.prodMk hY).aemeasurable (by fun_prop),
    integral_map (hX'.prodMk hY').aemeasurable (by fun_prop)]
  have hL (x y : ℝ) : L (x,y)=L (1,0)*x+L (0,1)*y := by
    have he : (x,y)=x • (1,0)+y • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul,map_smul]
    simp only [smul_eq_mul]
    ring
  have he (x y : ℝ) : Complex.exp ((L (x,y):ℂ)*Complex.I)=
      observable (L (1,0)) x*observable (L (0,1)) y := by
    rw [hL]
    unfold observable
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact h (L (1,0)) (L (0,1))

theorem half_two_time_law (κ s t : ℝ≥0) (hst : s ≤ t) (a b : ℝ)
    (ha : a^2=1/2) (hb : b^2=1/2) :
    HasLaw (fun w => (linearValue κ s a b w,linearValue κ t a b w))
      (gaussianProduct.map (fun w => (clockPath w s,clockPath w t))) sourceMeasure := by
  refine ⟨((linear_measurable κ s a b).prodMk (linear_measurable κ t a b)).aemeasurable,?_⟩
  apply map_pair_eq_of_fourier sourceMeasure gaussianProduct
    (linearValue κ s a b) (linearValue κ t a b) (fun w => clockPath w s) (fun w => clockPath w t)
    (linear_measurable κ s a b) (linear_measurable κ t a b)
    ((ContinuousMap.measurable_eval s).comp clockPath_measurable)
    ((ContinuousMap.measurable_eval t).comp clockPath_measurable)
  intro p q
  rw [balanced_two_time κ s t hst p q a b (ha.trans hb.symm),ha,two_time_fourier p q s t hst]
  congr 1
  ring

theorem left_two_time_law (κ s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun w => (leftPath κ w s,leftPath κ w t))
      (gaussianProduct.map (fun w => (clockPath w s,clockPath w t))) sourceMeasure := by
  apply (half_two_time_law κ s t hst (1/Real.sqrt 2) (1/Real.sqrt 2)
    reciprocal_sqrt_square reciprocal_sqrt_square).congr
  exact Eventually.of_forall fun w => by
    dsimp [linearValue,leftPath]
    congr 1 <;> ring

theorem right_two_time_law (κ s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun w => (rightPath κ w s,rightPath κ w t))
      (gaussianProduct.map (fun w => (clockPath w s,clockPath w t))) sourceMeasure := by
  have hb : (-1/Real.sqrt (2:ℝ))^2=1/2 := by
    rw [neg_div,neg_sq]
    exact reciprocal_sqrt_square
  apply (half_two_time_law κ s t hst (1/Real.sqrt 2) (-1/Real.sqrt 2)
    reciprocal_sqrt_square hb).congr
  exact Eventually.of_forall fun w => by
    dsimp [linearValue,rightPath]
    congr 1 <;> ring

end OperatorDerivativeRewrite.Foundation.StickyPairTwoTimeFourier
