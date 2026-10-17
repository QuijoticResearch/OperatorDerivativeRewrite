import Foundation.RootMarkItoIsometry

/-! Native L2 realization of the actually constructed predictable stochastic integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkL2Integral
open RootMarkStochasticIntegral RootMarkItoIsometry RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment)

theorem adapted_memLp (M : ℕ → MarkSample → ℂ) (hM : StronglyAdapted history M)
    (n : ℕ) (p : ℝ≥0∞) : MemLp (M n) p marks := by
  obtain ⟨F,hF⟩ := RootMarkMartingaleRepresentation.adapted_factors M hM
  apply MemLp.of_bound ((hM n).mono (history.le n)).aestronglyMeasurable
    (∑ ξ : ComplexFourthRootWalk.Sample n, ‖F n ξ‖)
  exact Eventually.of_forall fun η => by
    have he := congrFun (congrFun hF n) η
    change M n η = F n (initialSegment n η) at he
    rw [he]
    exact Finset.single_le_sum (fun ξ _ => norm_nonneg (F n ξ)) (Finset.mem_univ _)

theorem integral_memLp (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ) (p : ℝ≥0∞) :
    MemLp (totalIntegral a H N) p marks :=
  adapted_memLp _ (totalIntegral_martingale a H).stronglyAdapted N p

def integralL2 (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ) : Lp ℂ 2 marks :=
  (integral_memLp a H N 2).toLp (totalIntegral a H N)

theorem integralL2_ae (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ) :
    integralL2 a H N =ᵐ[marks] totalIntegral a H N :=
  (integral_memLp a H N 2).coeFn_toLp

theorem integralL2_norm_square (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ) :
    ‖integralL2 a H N‖^2 = ∑ j ∈ Finset.range N, ∫ η, energy a H j η ∂marks := by
  apply Complex.ofReal_injective
  calc
    ((‖integralL2 a H N‖^2 : ℝ) : ℂ) = ⟪integralL2 a H N, integralL2 a H N⟫_ℂ :=
      by simpa only [← RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_pow] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (integralL2 a H N)).symm
    _ = ∫ η, ⟪integralL2 a H N η, integralL2 a H N η⟫_ℂ ∂marks := L2.inner_def _ _
    _ = ∫ η, ((‖totalIntegral a H N η‖^2 : ℝ) : ℂ) ∂marks := by
      apply integral_congr_ae
      filter_upwards [integralL2_ae a H N] with η hη
      simp only [hη, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_pow]
    _ = ((∫ η, ‖totalIntegral a H N η‖^2 ∂marks : ℝ) : ℂ) := integral_complex_ofReal
    _ = _ := congrArg Complex.ofReal (ito_isometry a H N)

theorem totalIntegral_add (a : ℝ) (H K : Fin 3 → Coefficients) (N : ℕ) :
    totalIntegral a (H+K) N = totalIntegral a H N+totalIntegral a K N := by
  funext η
  simp only [totalIntegral, stochasticIntegral, increment, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

theorem totalIntegral_smul (a : ℝ) (c : ℂ) (H : Fin 3 → Coefficients) (N : ℕ) :
    totalIntegral a (c • H) N = c • totalIntegral a H N := by
  funext η
  simp only [totalIntegral, stochasticIntegral, increment, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

def integralOperator (a : ℝ) (N : ℕ) : (Fin 3 → Coefficients) →ₗ[ℂ] Lp ℂ 2 marks where
  toFun H := integralL2 a H N
  map_add' H K := by
    apply Lp.ext
    filter_upwards [integralL2_ae a (H+K) N, integralL2_ae a H N, integralL2_ae a K N,
      Lp.coeFn_add (integralL2 a H N) (integralL2 a K N)] with η hHK hH hK hadd
    rw [hHK, hadd]
    simp only [Pi.add_apply, hH, hK]
    simpa only [Pi.add_apply] using congrFun (totalIntegral_add a H K N) η
  map_smul' c H := by
    change integralL2 a (c • H) N = c • integralL2 a H N
    apply Lp.ext
    filter_upwards [integralL2_ae a (c • H) N, integralL2_ae a H N,
      Lp.coeFn_smul c (integralL2 a H N)] with η hcH hH hsmul
    rw [hcH, hsmul]
    simp only [Pi.smul_apply, hH]
    simpa only [Pi.smul_apply] using congrFun (totalIntegral_smul a c H N) η

end OperatorDerivativeRewrite.Foundation.RootMarkL2Integral
