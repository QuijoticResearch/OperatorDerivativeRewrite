import Foundation.HigherHeatFourierPathC0
import Foundation.HigherHeatGenerator

/-! Actual path-space heat difference quotients on a weighted l1 domain. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathDerivative
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierPathSemigroup HigherHeatFourierPathC0

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def rate (m : ℕ) (i : ℕ) : ℝ :=
  (∑ j : Fin (gridSize (spectrumLevels levels i)),
    HigherHeatGenerator.weight m
      (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)) /
        (gridSize (spectrumLevels levels i) : ℝ)

theorem rate_nonneg (m : ℕ) (i : ℕ) : 0 ≤ rate levels ξ m i := by
  exact div_nonneg (Finset.sum_nonneg (fun j _ => HigherHeatGenerator.weight_nonneg m _))
    (Nat.cast_nonneg _)

theorem multiplier_exp (m : ℕ) (T : ℝ≥0) (i : ℕ) :
    multiplier levels ξ m T i=(Real.exp (-(T:ℝ)*rate levels ξ m i) : ℝ) := by
  simp only [multiplier, HigherHeatL2.symbol, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  unfold duration rate HigherHeatGenerator.weight
  simp only [NNReal.coe_div, NNReal.coe_natCast, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coefficient_quotient_bound (m : ℕ) (a b : Coeff)
    (hab : ∀ i, b i=a i*((-rate levels ξ m i : ℝ) : ℂ)) (t : ℝ) (i : ℕ) :
    ‖(t⁻¹ • (coefficientEvolution levels ξ m t.toNNReal a-a) : Coeff) i‖ ≤ ‖b i‖ := by
  change ‖(t⁻¹:ℝ) • (a i*multiplier levels ξ m t.toNNReal i-a i)‖ ≤ ‖b i‖
  rw [multiplier_exp, hab i]
  have he : (t⁻¹:ℝ) • (a i*(Real.exp (-(t.toNNReal:ℝ)*rate levels ξ m i):ℝ)-a i)=
      a i*(HigherHeatGenerator.coefficient (rate levels ξ m i) t : ℂ) := by
    simp only [HigherHeatGenerator.coefficient, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
    ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (rate_nonneg levels ξ m i)]
  exact mul_le_mul_of_nonneg_left
    (HigherHeatGenerator.coefficient_bound _ (rate_nonneg levels ξ m i) t) (norm_nonneg _)

theorem coefficient_quotient_tendsto (m : ℕ) (a b : Coeff)
    (hab : ∀ i, b i=a i*((-rate levels ξ m i : ℝ) : ℂ)) :
    Tendsto (fun t : ℝ => t⁻¹ • (coefficientEvolution levels ξ m t.toNNReal a-a))
      (𝓝[Set.Ioi 0] 0) (𝓝 b) := by
  let q (t : ℝ) : Coeff := t⁻¹ • (coefficientEvolution levels ξ m t.toNNReal a-a)
  have hi (i : ℕ) : Tendsto (fun t => q t i) (𝓝[Set.Ioi 0] 0) (𝓝 (b i)) := by
    have ht := (tendsto_const_nhds (x := a i)).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (HigherHeatGenerator.coefficient_tendsto (rate levels ξ m i)))
    have he (t : ℝ) : q t i=a i*(HigherHeatGenerator.coefficient (rate levels ξ m i) t : ℂ) := by
      change (t⁻¹:ℝ) • (a i*multiplier levels ξ m t.toNNReal i-a i)=_
      rw [multiplier_exp]
      simp only [HigherHeatGenerator.coefficient, Complex.real_smul, Complex.ofReal_div,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv]
      ring
    simpa only [he, Function.comp_def, ← hab i] using ht
  have hn (i : ℕ) : Tendsto (fun t => ‖q t i-b i‖) (𝓝[Set.Ioi 0] 0) (𝓝 (0:ℝ)) := by
    simpa only [sub_self, norm_zero] using (hi i).sub_const (b i) |>.norm
  have hb (t : ℝ) (i : ℕ) : ‖‖q t i-b i‖‖ ≤ 2*‖b i‖ := by
    rw [Real.norm_eq_abs, abs_norm]
    have hq := coefficient_quotient_bound levels ξ m a b hab t i
    calc
      _ ≤ ‖q t i‖+‖b i‖ := norm_sub_le _ _
      _ ≤ ‖b i‖+‖b i‖ := add_le_add hq le_rfl
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence ((coeff_summable b).mul_left (2:ℝ)) hn
    (Eventually.of_forall hb)
  have hs : Tendsto (fun t => ∑' i, ‖q t i-b i‖) (𝓝[Set.Ioi 0] 0) (𝓝 (0:ℝ)) := by
    simpa using ht
  have he (t : ℝ) : ‖q t-b‖=∑' i, ‖q t i-b i‖ := by rw [← coeff_norm]; rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact hs.congr' (Eventually.of_forall fun t => (he t).symm)

theorem evolution_quotient_tendsto (m : ℕ) (hm : 0 < m) (a b : Coeff)
    (hab : ∀ i, b i=a i*((-rate levels ξ m i : ℝ) : ℂ)) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution levels ξ m hm t.toNNReal
      ((kernel levels ξ).mkQ a)-(kernel levels ξ).mkQ a))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((kernel levels ξ).mkQ b)) := by
  have ht := (kernel levels ξ).mkQL.continuous.tendsto b |>.comp
    (coefficient_quotient_tendsto levels ξ m a b hab)
  simp only [evolution_mk]
  simpa only [Function.comp_def, ContinuousLinearMap.map_smul_of_tower, map_sub,
    Submodule.mkQL_apply] using ht

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathDerivative
