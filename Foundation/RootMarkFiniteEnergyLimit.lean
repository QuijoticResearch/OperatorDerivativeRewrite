import Foundation.RootMarkL2Limit
import Foundation.RootMarkL2Integral

/-! Finite-energy construction of actual infinite stochastic integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkFiniteEnergyLimit
open RootMarkStochasticIntegral RootMarkL2Integral RootMarkGKWConditioning RootMarkL2Limit
open RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)

theorem integral_conditioning (a : ℝ) (H : Fin 3 → Coefficients) (m n : ℕ) (h : m ≤ n) :
    conditionalValue m (integralL2 a H n) = integralL2 a H m := by
  apply Lp.ext
  exact (prefix_projection_condExp_ae m (integralL2 a H n)).trans
    ((condExp_congr_ae (integralL2_ae a H n)).trans
      (((RootMarkItoIsometry.totalIntegral_martingale a H).2 m n h).trans
        (integralL2_ae a H m).symm))

theorem squared_distance (a : ℝ) (H : Fin 3 → Coefficients) (m n : ℕ) (h : m ≤ n) :
    ‖integralL2 a H n-integralL2 a H m‖^2 =
      ‖integralL2 a H n‖^2-‖integralL2 a H m‖^2 := by
  have he : (prefixSpace m).starProjection (integralL2 a H n) = integralL2 a H m :=
    integral_conditioning a H m n h
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection (integralL2 a H n) (prefixSpace m)
  rw [Submodule.starProjection_orthogonal_val,he] at hp
  linarith

theorem finite_energy_cauchy (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    CauchySeq (fun n : ℕ => integralL2 a H n) := by
  have ht := hH.hasSum.tendsto_sum_nat
  have hc := ht.cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.dist_eq] at hb
  have he := squared_distance a H N n hn
  rw [integralL2_norm_square,integralL2_norm_square] at he
  have hsq : ‖integralL2 a H n-integralL2 a H N‖^2 < ε^2 :=
    he ▸ lt_of_le_of_lt (le_abs_self _) hb
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (integralL2 a H n-integralL2 a H N)]

theorem finite_energy_integral (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    ∃ Y : Lp ℂ 2 marks, Tendsto (fun n : ℕ => integralL2 a H n) atTop (𝓝 Y) :=
  cauchySeq_tendsto_of_complete (finite_energy_cauchy a H hH)

def stochasticLimit (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) : Lp ℂ 2 marks :=
  (finite_energy_integral a H hH).choose

theorem stochasticLimit_tendsto (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    Tendsto (fun n : ℕ => integralL2 a H n) atTop (𝓝 (stochasticLimit a H hH)) :=
  (finite_energy_integral a H hH).choose_spec

theorem stochasticLimit_isometry (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    ‖stochasticLimit a H hH‖^2 = ∑' j : ℕ, ∫ η, energy a H j η ∂marks := by
  have ht := (stochasticLimit_tendsto a H hH).norm.pow 2
  simp only [integralL2_norm_square] at ht
  exact tendsto_nhds_unique ht hH.hasSum.tendsto_sum_nat

theorem conditionalValue_continuous (m : ℕ) :
    Continuous (fun Y : Lp ℂ 2 marks => conditionalValue m Y) :=
  (lpMeas ℂ ℂ (history m) 2 marks).subtypeL.continuous.comp
    (condExpL2 ℂ ℂ (history.le m)).continuous

theorem stochasticLimit_conditioning (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) (m : ℕ) :
    conditionalValue m (stochasticLimit a H hH) = integralL2 a H m := by
  have ht := ((conditionalValue_continuous m).tendsto (stochasticLimit a H hH)).comp
    (stochasticLimit_tendsto a H hH)
  exact tendsto_nhds_unique ht (tendsto_atTop_of_eventually_const
    (fun n hn => integral_conditioning a H m n hn))

theorem stochasticLimit_mean_zero (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    (∫ η, stochasticLimit a H hH η ∂marks) = 0 := by
  calc
    _ = ∫ η, conditionalValue 0 (stochasticLimit a H hH) η ∂marks :=
      (conditionalValue_mean 0 (stochasticLimit a H hH)).symm
    _ = ∫ η, integralL2 a H 0 η ∂marks := by rw [stochasticLimit_conditioning]
    _ = ∫ η, RootMarkItoIsometry.totalIntegral a H 0 η ∂marks :=
      integral_congr_ae (integralL2_ae a H 0)
    _ = 0 := by rw [RootMarkItoIsometry.totalIntegral_zero]; simp

theorem stochasticLimit_ae_tendsto (a : ℝ) (H : Fin 3 → Coefficients)
    (hH : Summable (fun j : ℕ => ∫ η, energy a H j η ∂marks)) :
    ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => RootMarkItoIsometry.totalIntegral a H n η)
      atTop (𝓝 (stochasticLimit a H hH η)) := by
  have hi : Integrable (stochasticLimit a H hH : MarkSample → ℂ) marks :=
    memLp_one_iff_integrable.mp ((Lp.memLp _).mono_exponent one_le_two)
  have ht := RootMarkComplexClarkLimit.integrable_condExp_ae_limit _ hi
  have hn (n : ℕ) :
      marks[(stochasticLimit a H hH : MarkSample → ℂ) | history n] =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n := by
    have he := (prefix_projection_condExp_ae n (stochasticLimit a H hH)).symm
    change _ =ᵐ[marks] (conditionalValue n (stochasticLimit a H hH) : MarkSample → ℂ) at he
    rw [stochasticLimit_conditioning] at he
    exact he.trans (integralL2_ae a H n)
  filter_upwards [ht,ae_all_iff.mpr hn] with η hη hnη
  exact hη.congr (fun n => hnη n)

end OperatorDerivativeRewrite.Foundation.RootMarkFiniteEnergyLimit
