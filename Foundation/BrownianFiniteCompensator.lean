import Foundation.BrownianCompensatedSampling

/-! Actual finite products of normalized Fourier phases along ordered Brownian stopping clocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianFiniteCompensator
open InfiniteGaussian BrownianComplexSampling BrownianCompensatedSampling
open BrownianFourierMartingales BrownianStoppedTrigConditional BrownianMassClockStoppingTime
open BrownianMassRandomTimeChange
set_option backward.isDefEq.respectTransparency false

variable (τ : ℕ → SampleSpace → ℝ≥0)
  (hτ : ∀ k, IsStoppingTime augmentedPast (fun w => (τ k w : WithTop ℝ≥0)))
  (hmono : ∀ w, Monotone (fun k => τ k w)) (u : ℕ → ℝ)

def density (n : ℕ) (w : SampleSpace) : ℂ :=
  ∏ k ∈ Finset.range n, phase (u k) (τ (k+1) w) w/phase (u k) (τ k w) w

theorem density_succ (n : ℕ) (w : SampleSpace) :
    density τ u (n+1) w=density τ u n w*
      (phase (u n) (τ (n+1) w) w/phase (u n) (τ n w) w) := by
  exact Finset.prod_range_succ _ n

include hτ hmono in
theorem density_measurable (n : ℕ) : Measurable[(hτ n).measurableSpace] (density τ u n) := by
  apply Finset.measurable_fun_prod
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hm (j : ℕ) (hj : j ≤ n) :
      Measurable[(hτ n).measurableSpace] (fun w => phase (u k) (τ j w) w) :=
    (phase_at_stop_measurable (τ j) (hτ j) (u k)).mono
      ((hτ j).measurableSpace_mono (hτ n) (fun w => WithTop.coe_le_coe.mpr (hmono w hj))) le_rfl
  exact (hm (k+1) hk').div (hm k hk'.le)

theorem density_bound (n N : ℕ) (hN : ∀ k, k ≤ n → ∀ w, τ k w ≤ N) (w : SampleSpace) :
    ‖density τ u n w‖ ≤ ∏ k ∈ Finset.range n, weight (u k) N := by
  rw [density,norm_prod]
  apply Finset.prod_le_prod₀
  · intro k hk
    exact norm_nonneg _
  · intro k hk
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) (phase_norm_one_le (u k) (τ k w) w)).trans
    rw [phase_norm]
    exact weight_monotone (u k) (by exact_mod_cast hN (k+1) (Finset.mem_range.mp hk) w)

include hτ hmono in
theorem density_integrable (n N : ℕ) (hN : ∀ k, k ≤ n → ∀ w, τ k w ≤ N) :
    Integrable (density τ u n) gaussianProduct :=
  Integrable.of_bound ((density_measurable τ hτ hmono u n).mono
    (hτ n).measurableSpace_le le_rfl).aestronglyMeasurable
    (∏ k ∈ Finset.range n, weight (u k) N)
    (Eventually.of_forall (density_bound τ u n N hN))

include hτ hmono in
theorem density_mean (n N : ℕ) (hN : ∀ k, k ≤ n → ∀ w, τ k w ≤ N) :
    (∫ w, density τ u n w ∂gaussianProduct)=1 := by
  induction n generalizing N with
  | zero => simp [density]
  | succ n ih =>
    have hNn (k : ℕ) (hk : k ≤ n) (w : SampleSpace) : τ k w ≤ N :=
      hN k (hk.trans (Nat.le_succ n)) w
    let F : SampleSpace → ℂ := fun w => density τ u n w/phase (u n) (τ n w) w
    have hF : StronglyMeasurable[(hτ n).measurableSpace] F :=
      ((density_measurable τ hτ hmono u n).div
        (phase_at_stop_measurable (τ n) (hτ n) (u n))).stronglyMeasurable
    have hb (w : SampleSpace) : ‖F w‖ ≤ ∏ k ∈ Finset.range n, weight (u k) N := by
      change ‖density τ u n w/phase (u n) (τ n w) w‖ ≤ _
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) (phase_norm_one_le (u n) (τ n w) w)).trans
        (density_bound τ u n N hNn w)
    have he (w : SampleSpace) : density τ u (n+1) w=F w*phase (u n) (τ (n+1) w) w := by
      rw [density_succ]
      dsimp [F]
      ring
    have hc (w : SampleSpace) : F w*phase (u n) (τ n w) w=density τ u n w :=
      div_mul_cancel₀ _ (phase_nonzero (u n) (τ n w) w)
    calc
      _ = ∫ w, F w*phase (u n) (τ (n+1) w) w ∂gaussianProduct :=
        integral_congr_ae (Eventually.of_forall he)
      _ = ∫ w, F w*phase (u n) (τ n w) w ∂gaussianProduct :=
        bounded_weighted_sampling (τ (n+1)) (hτ (n+1)) (τ n) (hτ n) (u n)
          (fun w => hmono w (Nat.le_succ n)) N (hN (n+1) le_rfl) F hF
          (∏ k ∈ Finset.range n, weight (u k) N) hb
      _ = ∫ w, density τ u n w ∂gaussianProduct := integral_congr_ae (Eventually.of_forall hc)
      _ = 1 := ih N hNn

theorem inverse_density_mean (κ : ℝ≥0) (times : ℕ → ℝ≥0) (ht : Monotone times)
    (u : ℕ → ℝ) (n : ℕ) :
    (∫ w, density (fun k w => inverse κ w (times k)) u n w ∂gaussianProduct)=1 := by
  apply density_mean (fun k w => inverse κ w (times k))
    (fun k => inverse_isStoppingTime κ (times k))
    (fun w _ _ hk => inverse_monotone κ w (ht hk)) u n (Nat.ceil (times n))
  intro k hk w
  exact (inverse_le κ w (times k)).trans ((ht hk).trans (Nat.le_ceil (times n)))

end OperatorDerivativeRewrite.Foundation.BrownianFiniteCompensator
