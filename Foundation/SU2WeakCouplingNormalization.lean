import Foundation.SU2CoupledLoopResponse
/-! Vanishing two-loop coupling with persistent local variance and divergent normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
namespace OperatorDerivativeRewrite.Foundation.SU2WeakCouplingNormalization

def localVar (r : ℝ) : ℝ := variance μ X F r

theorem localVar_eq_actual (r : ℝ) :
    localVar r = (∫ p, (F p)^2 ∂coupledLaw r) -
      (∫ p, F p ∂coupledLaw r)^2 := by
  have hF : Measurable F := halfTrace_measurable.comp measurable_fst
  have hX : Measurable X := hF.mul (halfTrace_measurable.comp measurable_snd)
  have bX (p) : |X p| ≤ 1 := by
    calc
      |X p| = |F p| * |G p| := by simp [X]
      _ ≤ 1 * 1 := mul_le_mul (halfTrace_bound p.1) (halfTrace_bound p.2)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  change expectation μ X (fun p => F p ^ 2) r - (expectation μ X F r)^2 = _
  rw [← tilted_integral μ X (fun p => F p ^ 2) hX bX r,
      ← tilted_integral μ X F hX bX r]
  rfl
theorem localVar_zero : localVar 0 = 1/4 := by
  have hF : (∫ p, F p ∂μ) = 0 := by
    have h := integral_prod_mul (μ := law) (ν := law) halfTrace (fun _ : SU2 => (1 : ℝ))
    change (∫ p, halfTrace p.1 ∂law.prod law) = 0
    simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h
  have hF2 : (∫ p, (F p)^2 ∂μ) = 1/4 := by
    have h := integral_prod_mul (μ := law) (ν := law)
      (fun A : SU2 => halfTrace A^2) (fun _ : SU2 => (1 : ℝ))
    change (∫ p, halfTrace p.1^2 ∂law.prod law) = 1/4
    simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).2.1] using h
  change expectation μ X (fun p => F p ^ 2) 0 - (expectation μ X F 0)^2 = 1/4
  rw [expectation_zero, expectation_zero, hF2, hF]
  norm_num

theorem localVar_continuousAt_zero : ContinuousAt localVar 0 := by
  have hF : Measurable F := halfTrace_measurable.comp measurable_fst
  have hX : Measurable X := hF.mul (halfTrace_measurable.comp measurable_snd)
  have bF (p) : |F p| ≤ 1 := halfTrace_bound p.1
  have bX (p) : |X p| ≤ 1 := by
    calc
      |X p| = |F p| * |G p| := by simp [X]
      _ ≤ 1 * 1 := mul_le_mul (bF p) (halfTrace_bound p.2) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact (variance_hasDerivAt_zero μ X F hX hF bX 1 (by norm_num) bF).continuousAt

private theorem exists_weak (n : ℕ) :
    ∃ r, 0 < r ∧ r < 1 / ((n:ℝ)+1) ∧ 0 < corr r :=
  positive_corr_near_zero (1 / ((n:ℝ)+1)) (by positivity)

def weakCoupling (n : ℕ) : ℝ := Classical.choose (exists_weak n)

theorem weakCoupling_pos (n : ℕ) : 0 < weakCoupling n :=
  (Classical.choose_spec (exists_weak n)).1

theorem weakCoupling_small (n : ℕ) : weakCoupling n < 1 / ((n:ℝ)+1) :=
  (Classical.choose_spec (exists_weak n)).2.1

theorem weakCoupling_corr_pos (n : ℕ) : 0 < corr (weakCoupling n) :=
  (Classical.choose_spec (exists_weak n)).2.2

theorem weakCoupling_tendsto_zero :
    Filter.Tendsto weakCoupling Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0:ℝ)))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Filter.Eventually.of_forall (fun n => (weakCoupling_pos n).le)
  · exact Filter.Eventually.of_forall (fun n => (weakCoupling_small n).le)

theorem corr_tendsto_zero :
    Filter.Tendsto (fun n => corr (weakCoupling n)) Filter.atTop (nhds 0) := by
  have h0 : corr 0 = 0 := by
    have hF : (∫ p, F p ∂μ) = 0 := by
      have h := integral_prod_mul (μ := law) (ν := law) halfTrace (fun _ : SU2 => (1 : ℝ))
      change (∫ p, halfTrace p.1 ∂law.prod law) = 0
      simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h
    have hG : (∫ p, G p ∂μ) = 0 := by
      have h := integral_prod_mul (μ := law) (ν := law) (fun _ : SU2 => (1 : ℝ)) halfTrace
      change (∫ p, halfTrace p.2 ∂law.prod law) = 0
      simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h
    have hX : (∫ p, X p ∂μ) = 0 := by
      have h := integral_prod_mul (μ := law) (ν := law) halfTrace halfTrace
      change (∫ p, halfTrace p.1 * halfTrace p.2 ∂law.prod law) = 0
      simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h
    simp [corr, expectation_zero, hF, hG, hX]
  change Filter.Tendsto (corr ∘ weakCoupling) Filter.atTop (nhds 0)
  simpa [h0] using corr_hasDerivAt_zero.continuousAt.tendsto.comp weakCoupling_tendsto_zero

theorem localVar_tendsto_quarter :
    Filter.Tendsto (fun n => localVar (weakCoupling n)) Filter.atTop (nhds (1/4:ℝ)) := by
  change Filter.Tendsto (localVar ∘ weakCoupling) Filter.atTop (nhds (1/4:ℝ))
  simpa [localVar_zero] using localVar_continuousAt_zero.tendsto.comp weakCoupling_tendsto_zero

theorem no_uniform_normalized_local_variance :
    ¬ ∃ M : ℝ, ∀ n : ℕ, localVar (weakCoupling n) / corr (weakCoupling n) ≤ M := by
  rintro ⟨M, hM⟩
  have hvarEv : ∀ᶠ n : ℕ in Filter.atTop, 1/8 ≤ localVar (weakCoupling n) :=
    localVar_tendsto_quarter.eventually (eventually_ge_nhds (by norm_num : (1/8:ℝ) < 1/4))
  have hMul : Filter.Tendsto (fun n : ℕ => M * corr (weakCoupling n))
      Filter.atTop (nhds 0) := by
    simpa using corr_tendsto_zero.const_mul M
  have hLower : ∀ᶠ n : ℕ in Filter.atTop, 1/8 ≤ M * corr (weakCoupling n) := by
    filter_upwards [hvarEv] with n hv
    exact hv.trans ((div_le_iff₀ (weakCoupling_corr_pos n)).mp (hM n))
  have hbad : (1/8:ℝ) ≤ 0 := ge_of_tendsto hMul hLower
  norm_num at hbad
end OperatorDerivativeRewrite.Foundation.SU2WeakCouplingNormalization
