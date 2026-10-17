import Foundation.BrownianFiniteIncrementFourier
import Foundation.StickyPairTwoTimeFourier

/-! Actual finite increment Fourier laws of the sticky pair's balanced coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairFiniteIncrementFourier
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairMarginals
open BrownianMassRandomTimeChange BrownianComplexSampling BrownianFiniteCompensator
open BrownianFiniteIncrementFourier StickyPairTwoTimeFourier IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem interval_compensation (κ s t : ℝ≥0) (w : SampleSpace) (v a b : ℝ) (hab : a^2=b^2) :
    (Real.exp (-(v*a)^2*((centerClock κ w t:ℝ)-centerClock κ w s)/2) : ℂ)*
      observable (v*b) (clockPath w (inverse κ w t)-clockPath w (inverse κ w s)) =
    (Real.exp (-(v*a)^2*((t:ℝ)-s)) : ℂ)*
      (phase (v*b) (inverse κ w t) w/phase (v*b) (inverse κ w s) w) := by
  have habC : (a:ℂ)^2=(b:ℂ)^2 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow,hab]
  simp only [phase_exp,observable,Complex.ofReal_exp]
  rw [← Complex.exp_sub]
  simp only [← Complex.exp_add]
  congr 1
  rw [center_clock_real,center_clock_real]
  push_cast
  simp only [mul_pow,habC]
  ring

theorem observable_increment (κ s t : ℝ≥0) (w z : SampleSpace) (v a b : ℝ) :
    observable v (linearValue κ t a b (w,z)-linearValue κ s a b (w,z)) =
      observable (v*a) (centeredPath z (centerClock κ w t)-centeredPath z (centerClock κ w s))*
      observable (v*b) (centeredPath w (inverse κ w t)-centeredPath w (inverse κ w s)) := by
  rw [← observable_linear]
  congr 1
  dsimp [linearValue,centerPath,separationPath,inversePath]
  ring

theorem fiber (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (u : ℕ → ℝ) (n : ℕ) (w : SampleSpace) (a b : ℝ) :
    (∫ z, incrementProduct (fun r w => linearValue κ r a b w) times u n (w,z) ∂gaussianProduct)=
      (∏ k ∈ Finset.range n, (Real.exp (-(u k*a)^2*
        ((centerClock κ w (times (k+1)):ℝ)-centerClock κ w (times k))/2) : ℂ))*
      (∏ k ∈ Finset.range n, observable (u k*b)
        (centeredPath w (inverse κ w (times (k+1)))-centeredPath w (inverse κ w (times k)))) := by
  have hc := centered_formula (fun k => centerClock κ w (times k))
    ((center_clock_monotone κ w).comp ht) (fun k => u k*a) n
  change (∫ z, ∏ k ∈ Finset.range n, observable (u k*a)
    (centeredPath z (centerClock κ w (times (k+1)))-centeredPath z (centerClock κ w (times k)))
    ∂gaussianProduct)=_ at hc
  simp_rw [incrementProduct,observable_increment]
  calc
    _ = ∫ z, (∏ k ∈ Finset.range n, observable (u k*a)
        (centeredPath z (centerClock κ w (times (k+1)))-centeredPath z (centerClock κ w (times k))))*
        (∏ k ∈ Finset.range n, observable (u k*b)
          (centeredPath w (inverse κ w (times (k+1)))-centeredPath w (inverse κ w (times k))))
        ∂gaussianProduct := integral_congr_ae (Eventually.of_forall fun z => Finset.prod_mul_distrib)
    _ = _ := by rw [integral_mul_const,hc]

theorem increment_measurable (κ : ℝ≥0) (times : ℕ → ℝ≥0)
    (u : ℕ → ℝ) (n : ℕ) (a b : ℝ) :
    Measurable (incrementProduct (fun r w => linearValue κ r a b w) times u n) := by
  apply Finset.measurable_fun_prod
  intro k hk
  exact (observable_continuous (u k)).measurable.comp
    ((linear_measurable κ (times (k+1)) a b).sub (linear_measurable κ (times k) a b))

theorem balanced_formula (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (u : ℕ → ℝ) (n : ℕ) (a b : ℝ) (hab : a^2=b^2) :
    (∫ w, incrementProduct (fun r w => linearValue κ r a b w) times u n w ∂sourceMeasure)=
      ∏ k ∈ Finset.range n, (Real.exp (-(u k*a)^2*((times (k+1):ℝ)-times k)) : ℂ) := by
  have hi : Integrable (incrementProduct (fun r w => linearValue κ r a b w) times u n)
      sourceMeasure := by
    apply Integrable.of_bound (increment_measurable κ times u n a b).aestronglyMeasurable 1
    exact Eventually.of_forall fun w => by
      simp only [incrementProduct,norm_prod,observable_norm,Finset.prod_const_one,le_refl]
  change Integrable _ (gaussianProduct.prod gaussianProduct) at hi
  let C : ℂ := ∏ k ∈ Finset.range n,
    (Real.exp (-(u k*a)^2*((times (k+1):ℝ)-times k)) : ℂ)
  have he (w : SampleSpace) :
      (∏ k ∈ Finset.range n, (Real.exp (-(u k*a)^2*
        ((centerClock κ w (times (k+1)):ℝ)-centerClock κ w (times k))/2) : ℂ))*
      (∏ k ∈ Finset.range n, observable (u k*b)
        (centeredPath w (inverse κ w (times (k+1)))-centeredPath w (inverse κ w (times k)))) =
      C*density (fun k w => inverse κ w (times k)) (fun k => u k*b) n w := by
    calc
      _ = ∏ k ∈ Finset.range n, (Real.exp (-(u k*a)^2*
          ((centerClock κ w (times (k+1)):ℝ)-centerClock κ w (times k))/2) : ℂ)*
          observable (u k*b) (centeredPath w (inverse κ w (times (k+1)))-
            centeredPath w (inverse κ w (times k))) := Finset.prod_mul_distrib.symm
      _ = ∏ k ∈ Finset.range n, (Real.exp (-(u k*a)^2*((times (k+1):ℝ)-times k)) : ℂ)*
          (phase (u k*b) (inverse κ w (times (k+1))) w/
            phase (u k*b) (inverse κ w (times k)) w) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [centered_increment]
        exact interval_compensation κ (times k) (times (k+1)) w (u k) a b hab
      _ = _ := Finset.prod_mul_distrib
  calc
    _ = ∫ w, ∫ z, incrementProduct (fun r w => linearValue κ r a b w) times u n (w,z)
        ∂gaussianProduct ∂gaussianProduct := integral_prod _ hi
    _ = ∫ w, C*density (fun k w => inverse κ w (times k)) (fun k => u k*b) n w
        ∂gaussianProduct := by
      apply integral_congr_ae
      exact Eventually.of_forall fun w => (fiber κ times ht u n w a b).trans (he w)
    _ = _ := by
      rw [integral_const_mul,inverse_density_mean κ times ht]
      simp only [mul_one]
      rfl

theorem half_matches_source (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (u : ℕ → ℝ) (n : ℕ) (a b : ℝ) (ha : a^2=1/2) (hb : b^2=1/2) :
    (∫ w, incrementProduct (fun r w => linearValue κ r a b w) times u n w ∂sourceMeasure)=
      ∫ w, incrementProduct (fun r w => clockPath w r) times u n w ∂gaussianProduct := by
  rw [balanced_formula κ times ht u n a b (ha.trans hb.symm),source_formula times ht u n]
  apply Finset.prod_congr rfl
  intro k hk
  congr 1
  rw [mul_pow,ha]
  ring

end OperatorDerivativeRewrite.Foundation.StickyPairFiniteIncrementFourier
