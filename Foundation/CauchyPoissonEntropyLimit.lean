import Foundation.CauchyPoissonRegularization
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter InformationTheory
open scoped Topology ENNReal
/-! Entropy convergence for every initial probability law and uniqueness of
the probability fixed point of every positive-time actual transition. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonEntropyLimit
open CauchyPoissonRegularization CauchyPoissonEntropy CauchyPoissonMixtureEntropy CauchyPoissonMarkovKernel

theorem burnin_geometric_bound (q s t c : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hc : ∀ (μ : Measure Circle) [IsProbabilityMeasure μ],
      klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤ ENNReal.ofReal c*klDiv μ (invariantLaw q))
    (μ : Measure Circle) [IsProbabilityMeasure μ] (n : ℕ) :
    klDiv ((kernel q (s+n*t)) ∘ₘ μ) (invariantLaw q) ≤
      (ENNReal.ofReal c)^n*klDiv ((kernel q s) ∘ₘ μ) (invariantLaw q) := by
  let := kernel_markov q s hq hs
  have hh := entropy_geometric q t c hq ht hc ((kernel q s) ∘ₘ μ) n
  rw [Measure.comp_assoc,kernel_composition q s ((n:ℝ)*t) hq hs (mul_nonneg (Nat.cast_nonneg n) ht)] at hh
  exact hh

theorem finite_geometric_tendsto (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (D : ℝ≥0∞) (hD : D ≠ ⊤) :
    Tendsto (fun n : ℕ => (ENNReal.ofReal c)^n*D) atTop (𝓝 0) := by
  have hr := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const D.toReal
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have heq : (ENNReal.ofReal ∘ fun n : ℕ => c^n*D.toReal) = (fun n : ℕ => (ENNReal.ofReal c)^n*D) := by
    funext n
    dsimp only [Function.comp_apply]
    rw [ENNReal.ofReal_mul (pow_nonneg hc0 n),ENNReal.ofReal_pow hc0,ENNReal.ofReal_toReal hD]
  rw [heq] at he
  simpa only [zero_mul,ENNReal.ofReal_zero] using he

theorem entropy_tendsto_zero (q : ℝ) (hq : |q| < 1) (μ : Measure Circle) [IsProbabilityMeasure μ] :
    Tendsto (fun t : ℝ => klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)) atTop (𝓝 0) := by
  obtain ⟨c,hc0,hc1,hc⟩ := exists_entropy_contraction q 1 hq (by norm_num)
  have hD := positive_time_entropy_finite q 1 hq (by norm_num) μ
  have hb := finite_geometric_tendsto c hc0.le hc1 _ hD
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hb).2 ε hε).exists
  refine ⟨1+(n:ℝ),fun t ht => ?_⟩
  have hg := burnin_geometric_bound q 1 1 c hq (by norm_num) (by norm_num) hc μ n
  simp only [mul_one] at hg
  exact ((entropy_time_monotone q (1+(n:ℝ)) t hq (by positivity) ht μ).trans hg).trans hn.le


theorem positive_time_fixed_law_unique (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (hfix : (kernel q t) ∘ₘ μ = μ) :
    μ = invariantLaw q := by
  let := invariantLaw_probability q hq
  have hD := positive_time_entropy_finite q t hq ht μ
  rw [hfix] at hD
  obtain ⟨c,hc0,hc1,hc⟩ := exists_entropy_contraction q t hq ht
  have hh := hc μ
  rw [hfix] at hh
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc0.le] at hr
  have hz : (klDiv μ (invariantLaw q)).toReal = 0 := by nlinarith [ENNReal.toReal_nonneg (a := klDiv μ (invariantLaw q))]
  have he : klDiv μ (invariantLaw q) = 0 := by simpa only [ENNReal.toReal_eq_zero_iff,hD,or_false] using hz
  exact klDiv_eq_zero_iff.mp he

end OperatorDerivativeRewrite.Foundation.CauchyPoissonEntropyLimit
