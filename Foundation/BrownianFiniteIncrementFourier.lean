import Foundation.BrownianFiniteCompensator
import Foundation.BrownianTwoTimeFourier

/-! Actual finite increment Fourier laws of the independent Brownian center source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianFiniteIncrementFourier
open InfiniteGaussian IBMConstructedSources StickyPairPaths BrownianTwoTimeFourier IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def incrementProduct {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (times : ℕ → ℝ≥0)
    (u : ℕ → ℝ) (n : ℕ) (w : Ω) : ℂ :=
  ∏ k ∈ Finset.range n, observable (u k) (X (times (k+1)) w-X (times k) w)

theorem source_fin_formula (times : ℕ → ℝ≥0) (ht : Monotone times) (u : ℕ → ℝ) (n : ℕ) :
    (∫ w, ∏ i : Fin n, observable (u i)
      (clockPath w (times (i+1))-clockPath w (times i)) ∂gaussianProduct)=
    ∏ i : Fin n, (Real.exp (-(u i)^2*((times (i+1):ℝ)-times i)/2) : ℂ) := by
  have hi : iIndepFun (fun i : Fin n => fun w =>
      clockPath w (times (i+1))-clockPath w (times i)) gaussianProduct :=
    (clock_isBrownian.toIsPreBrownianReal.hasIndepIncrements.nat ht).precomp Fin.val_injective
  have hm (i : Fin n) : Measurable (fun w =>
      clockPath w (times (i+1))-clockPath w (times i)) :=
    ((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
      ((ContinuousMap.measurable_eval _).comp clockPath_measurable)
  have hf := hi.integral_fun_prod_comp (fun i => (hm i).aemeasurable)
    (fun i => (observable_continuous (u i)).aestronglyMeasurable)
  change (∫ w, ∏ i : Fin n, observable (u i)
    (clockPath w (times (i+1))-clockPath w (times i)) ∂gaussianProduct)=
    ∏ i : Fin n, ∫ w, observable (u i)
      (clockPath w (times (i+1))-clockPath w (times i)) ∂gaussianProduct at hf
  rw [hf]
  apply Finset.prod_congr rfl
  intro i hi
  rw [increment_fourier]
  have hh : (times i:ℝ) ≤ times (i+1) := by exact_mod_cast ht (Nat.le_succ (i:ℕ))
  simp only [coe_nndist,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hh)]
  congr 1
  ring

theorem source_formula (times : ℕ → ℝ≥0) (ht : Monotone times) (u : ℕ → ℝ) (n : ℕ) :
    (∫ w, incrementProduct (fun r w => clockPath w r) times u n w ∂gaussianProduct)=
    ∏ k ∈ Finset.range n, (Real.exp (-(u k)^2*((times (k+1):ℝ)-times k)/2) : ℂ) := by
  simpa only [← Fin.prod_univ_eq_prod_range,incrementProduct] using source_fin_formula times ht u n

theorem centered_increment (w : SampleSpace) (s t : ℝ≥0) :
    centeredPath w t-centeredPath w s=clockPath w t-clockPath w s := by
  dsimp [centeredPath]
  ring

theorem centered_formula (times : ℕ → ℝ≥0) (ht : Monotone times) (u : ℕ → ℝ) (n : ℕ) :
    (∫ w, incrementProduct (fun r w => centeredPath w r) times u n w ∂gaussianProduct)=
    ∏ k ∈ Finset.range n, (Real.exp (-(u k)^2*((times (k+1):ℝ)-times k)/2) : ℂ) := by
  simp_rw [incrementProduct,centered_increment]
  exact source_formula times ht u n

end OperatorDerivativeRewrite.Foundation.BrownianFiniteIncrementFourier
