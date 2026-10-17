import Foundation.HigherHeatFourierPathSemigroup

/-! Strong continuity and normalization of the genuine Fourier path heat semigroup. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathC0
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations HigherHeatFourierPathSemigroup

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem multiplier_continuous (m : ℕ) (i : ℕ) :
    Continuous (fun T => multiplier levels ξ m T i) := by
  unfold multiplier HigherHeatL2.symbol duration
  fun_prop

theorem coefficient_continuous (m : ℕ) (a : Coeff) :
    Continuous (fun T => coefficientEvolution levels ξ m T a) := by
  apply continuous_iff_continuousAt.mpr
  intro T₀
  have hi (i : ℕ) : Tendsto (fun T => ‖a i*multiplier levels ξ m T i-
      a i*multiplier levels ξ m T₀ i‖) (𝓝 T₀) (𝓝 (0:ℝ)) := by
    have hc : Continuous (fun T => a i*multiplier levels ξ m T i-
        a i*multiplier levels ξ m T₀ i) :=
      (continuous_const.mul (multiplier_continuous levels ξ m i)).sub continuous_const
    simpa only [sub_self, norm_zero] using hc.norm.tendsto T₀
  have hb (T : ℝ≥0) (i : ℕ) : ‖‖a i*multiplier levels ξ m T i-
      a i*multiplier levels ξ m T₀ i‖‖ ≤ 2*‖a i‖ := by
    rw [Real.norm_eq_abs, abs_norm]
    calc
      _ ≤ ‖a i*multiplier levels ξ m T i‖+‖a i*multiplier levels ξ m T₀ i‖ := norm_sub_le _ _
      _ ≤ ‖a i‖+‖a i‖ := by
        apply add_le_add
        all_goals
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (multiplier_bound levels ξ m _ i)
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence ((coeff_summable a).mul_left (2:ℝ)) hi
    (Eventually.of_forall hb)
  have hs : Tendsto (fun T => ∑' i, ‖a i*multiplier levels ξ m T i-
      a i*multiplier levels ξ m T₀ i‖) (𝓝 T₀) (𝓝 (0:ℝ)) := by simpa using ht
  have hn (T : ℝ≥0) : ‖coefficientEvolution levels ξ m T a-
      coefficientEvolution levels ξ m T₀ a‖=
      ∑' i, ‖a i*multiplier levels ξ m T i-a i*multiplier levels ξ m T₀ i‖ := by
    rw [← coeff_norm]
    apply tsum_congr
    intro i
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact hs.congr' (Eventually.of_forall fun T => (hn T).symm)

theorem evolution_strong_continuous (m : ℕ) (hm : 0 < m) (q : TestSpace levels ξ) :
    Continuous (fun T => evolution levels ξ m hm T q) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  change Continuous (fun T => (kernel levels ξ).mkQL (coefficientEvolution levels ξ m T a))
  exact (kernel levels ξ).mkQL.continuous.comp (coefficient_continuous levels ξ m a)

theorem evolution_tendsto_zero (m : ℕ) (hm : 0 < m) (q : TestSpace levels ξ) :
    Tendsto (fun T => evolution levels ξ m hm T q) (𝓝 0) (𝓝 q) := by
  have ht := (evolution_strong_continuous levels ξ m hm q).tendsto 0
  rwa [evolution_zero] at ht

theorem evolution_generator (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (i : ℕ) :
    evolution levels ξ m hm T (generator levels ξ i)=
      multiplier levels ξ m T i • generator levels ξ i := by
  rw [generator, evolution_mk, ← map_smul]
  congr 1
  apply Subtype.ext
  funext j
  change (lp.single 1 i (1:ℂ) : Coeff) j*multiplier levels ξ m T j=
    multiplier levels ξ m T i*(lp.single 1 i (1:ℂ) : Coeff) j
  classical
  by_cases hj : j=i
  · subst j
    rw [lp.coeFn_single, Pi.single_eq_same, one_mul, mul_one]
  · rw [lp.coeFn_single, Pi.single_eq_of_ne hj, zero_mul, mul_zero]

theorem multiplier_unit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) : multiplier levels ξ m T 0=1 := by
  unfold multiplier
  change (∏ j : Fin (gridSize 0), HigherHeatL2.symbol m (duration T 0)
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), (0 : Grid 0) k))=1
  have hp : 2*m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by norm_num) hm)
  simp [HigherHeatL2.symbol, hp]

theorem evolution_unit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    evolution levels ξ m hm T (unit levels ξ)=unit levels ξ := by
  change evolution levels ξ m hm T (generator levels ξ 0)=generator levels ξ 0
  rw [evolution_generator, multiplier_unit levels ξ m hm T, one_smul]

theorem evolution_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    ‖evolution levels ξ m hm T‖=1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa only [one_mul] using evolution_bound levels ξ m hm T q
  · have hh := (evolution levels ξ m hm T).le_opNorm (unit levels ξ)
    simpa only [evolution_unit, unit_norm, mul_one] using hh

theorem expectation_dirac_limit (m : ℕ) (hm : 0 < m) (q : TestSpace levels ξ) :
    Tendsto (fun T => realize levels ξ (evolution levels ξ m hm T q) zeroPath)
      (𝓝 0) (𝓝 (realize levels ξ q zeroPath)) :=
  ((BoundedContinuousFunction.evalCLM ℂ zeroPath).comp (realize levels ξ)).continuous.tendsto q
    |>.comp (evolution_tendsto_zero levels ξ m hm q)

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathC0
