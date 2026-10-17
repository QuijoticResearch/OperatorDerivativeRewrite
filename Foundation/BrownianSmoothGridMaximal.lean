import Foundation.BrownianSmoothMassRealization
import Foundation.ConditionalEnvelopeMaximal

/-! A genuine finite-grid maximal probability bound for differences of the
constructed continuous compensated paths. Adapted envelopes are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothGridMaximal
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull GaussianConditionalIto
open BrownianTanakaApproximation BrownianSmoothMassRealization ConditionalEnvelopeMaximal

def gridFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    Filtration ℕ (inferInstance : MeasurableSpace SampleSpace) :=
  ⟨fun i => naturalFiltration (τ i), fun _ _ h => naturalFiltration.mono (hτ h),
    fun i => naturalFiltration.le (τ i)⟩

def terminalDifference (n m : ℕ) (T : ℝ≥0) : GaussianL2 :=
  itoIntegral (approximateField n T) - itoIntegral (approximateField m T)

theorem difference_conditional (n m : ℕ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[terminalDifference n m T | naturalFiltration S] =ᵐ[gaussianProduct]
      fun ω => compensatedPath n ω S - compensatedPath m ω S := by
  have h := pastProjection_ae S (terminalDifference n m T)
  have hp : pastProjection S (terminalDifference n m T) =
      itoIntegral (approximateField n S) - itoIntegral (approximateField m S) := by
    unfold terminalDifference
    rw [map_sub, pastProjection_integral, pastProjection_integral,
      show GaussianPredictableCutoff.predictableCut S (approximateField n T) =
        approximateField n (min S T) from GaussianSmoothConditional.cut_integrand _ S T,
      show GaussianPredictableCutoff.predictableCut S (approximateField m T) =
        approximateField m (min S T) from GaussianSmoothConditional.cut_integrand _ S T,
      min_eq_left hST]
  rw [hp] at h
  filter_upwards [h.symm, Lp.coeFn_sub (itoIntegral (approximateField n S))
    (itoIntegral (approximateField m S)), compensatedPath_coeFn n S,
      compensatedPath_coeFn m S] with ω hh hs hn hm
  rw [hh, hs, Pi.sub_apply, hn, hm]

theorem integral_norm_le (F : GaussianL2) : ∫ ω, ‖F ω‖ ∂gaussianProduct ≤ ‖F‖ := by
  let G : GaussianL2 := (Lp.memLp F).norm.toLp (fun ω => ‖F ω‖)
  have hG : G =ᵐ[gaussianProduct] fun ω => ‖F ω‖ := MemLp.coeFn_toLp _
  have hn : ‖G‖ = ‖F‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable F)]
    rfl
  have ho : ‖gaussianOne‖ = 1 := by
    have h := GaussianDeterministicGraphCore.gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg gaussianOne]
  have hi : (∫ ω, ‖F ω‖ ∂gaussianProduct) = inner ℝ gaussianOne G := by
    rw [gaussianOne_inner_eq_integral]
    exact (integral_congr_ae hG).symm
  rw [hi]
  simpa only [ho, hn, one_mul] using real_inner_le_norm gaussianOne G

theorem difference_norm (n m : ℕ) (T : ℝ≥0) :
    ‖terminalDifference n m T‖ = ‖approximateField n T - approximateField m T‖ := by
  rw [terminalDifference, ← map_sub, itoIntegral.norm_map]

theorem finite_grid_maximal (n m : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hT : ∀ i, τ i ≤ T) (ε : ℝ≥0) (N : ℕ) :
    (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ i ≤ N,
      (ε : ℝ) ≤ ‖compensatedPath n ω (τ i) - compensatedPath m ω (τ i)‖} ≤
      ENNReal.ofReal ‖approximateField n T - approximateField m T‖ := by
  have hF : Integrable (terminalDifference n m T) gaussianProduct :=
    (Lp.memLp _).integrable (by norm_num)
  have h := maximal_of_ae_dominated gaussianProduct (gridFiltration τ hτ)
    (terminalDifference n m T) hF
    (fun i ω => ‖compensatedPath n ω (τ i) - compensatedPath m ω (τ i)‖) (by
      intro i
      filter_upwards [conditional_dominated gaussianProduct (gridFiltration τ hτ)
        (terminalDifference n m T) i, difference_conditional n m (τ i) T (hT i)]
        with ω hd he
      change ‖gaussianProduct[terminalDifference n m T | naturalFiltration (τ i)] ω‖ ≤ _ at hd
      rwa [he] at hd) ε N
  exact h.trans (ENNReal.ofReal_le_ofReal (by
    rw [← difference_norm]
    exact integral_norm_le _))

end OperatorDerivativeRewrite.Foundation.BrownianSmoothGridMaximal
