import Foundation.SU2ResidualEntropy
import Foundation.CauchyPoissonRegularization

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2ResidualEntropy

namespace OperatorDerivativeRewrite.Foundation.SU2PointEntropy

private theorem X_measurable : Measurable X :=
  (halfTrace_measurable.comp measurable_fst).mul
    (halfTrace_measurable.comp measurable_snd)

private theorem X_bound (p : SU2 × SU2) : |X p| ≤ 1 := by
  rw [X, abs_mul]
  calc
    |F p| * |G p| ≤ 1 * 1 :=
      mul_le_mul (halfTrace_bound _) (halfTrace_bound _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem globalPartition_upper (r : ℝ) :
    globalPartition r ≤ Real.exp (|r|) := by
  have hi : Integrable (fun p => Real.exp (r * X p)) μ :=
    BoundedExponentialTiltResponse.exponential_integrable μ X X_measurable X_bound r
  have h := integral_mono hi (integrable_const (Real.exp (|r|))) (fun p =>
    Real.exp_le_exp.mpr (by
      have hb := interaction_bound r p.1 p.2
      have he : interaction r p.1 p.2 = r * X p := by
        simp only [interaction, X, F, G]
        ring
      rw [he] at hb
      exact (le_abs_self _).trans hb))
  simpa [globalPartition, BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted] using h

theorem localPartition_lower (r : ℝ) (C : SU2) :
    Real.exp (-|r|) ≤ MeasurableExponentialKernel.partition law (interaction r) C := by
  have hi := interaction_exp_integrable r C
  have h := integral_mono (integrable_const (Real.exp (-|r|))) hi (fun D =>
    Real.exp_le_exp.mpr (by
      have hb := interaction_bound r C D
      exact (neg_le_neg hb).trans (neg_abs_le _)))
  simpa [MeasurableExponentialKernel.partition] using h

theorem equilibriumDensity_lower (r : ℝ) (D : SU2) :
    Real.exp (-(2 * |r|)) ≤ equilibriumDensity r D := by
  have hg := globalPartition_upper r
  have hp := globalPartition_pos r
  apply (le_div_iff₀ hp).2
  calc
    Real.exp (-(2 * |r|)) * globalPartition r ≤
      Real.exp (-(2 * |r|)) * Real.exp (|r|) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ = Real.exp (-|r|) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := localPartition_lower r D

theorem transitionDensity_upper (r : ℝ) (C D : SU2) :
    MeasurableExponentialKernel.density law (interaction r) C D ≤
      Real.exp (2 * |r|) := by
  have hp := MeasurableExponentialKernel.partition_positive law (interaction r) C
    (interaction_exp_integrable r C)
  apply (div_le_iff₀ hp).2
  calc
    Real.exp (interaction r C D) ≤ Real.exp (|r|) :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans (interaction_bound r C D))
    _ = Real.exp (2 * |r|) * Real.exp (-|r|) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * |r|) *
        MeasurableExponentialKernel.partition law (interaction r) C :=
      mul_le_mul_of_nonneg_left (localPartition_lower r C) (Real.exp_pos _).le

theorem reverse_density_bound (r : ℝ) (C D : SU2) :
    MeasurableExponentialKernel.density law (interaction r) C D ≤
      Real.exp (4 * |r|) * equilibriumDensity r D := by
  calc
    _ ≤ Real.exp (2 * |r|) := transitionDensity_upper r C D
    _ = Real.exp (4 * |r|) * Real.exp (-(2 * |r|)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (equilibriumDensity_lower r D)
      (Real.exp_pos _).le

theorem loopKernel_dominated_by_equilibrium (r : ℝ) (C : SU2) :
    loopKernel r C ≤ ENNReal.ofReal (Real.exp (4 * |r|)) • equilibriumLaw r := by
  rw [loopKernel, MeasurableExponentialKernel.kernel_apply law _ (interaction_measurable r),
    equilibriumLaw]
  rw [← withDensity_smul' (ENNReal.ofReal (Real.exp (4 * |r|)))
    (fun D : SU2 => ENNReal.ofReal (equilibriumDensity r D)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards with D
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (reverse_density_bound r C D)

theorem forward_dominated_by_equilibrium (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] :
    loopKernel r ∘ₘ ρ ≤
      ENNReal.ofReal (Real.exp (4 * |r|)) • equilibriumLaw r := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB (loopKernel r).aemeasurable]
  have hb : ∀ C : SU2,
      loopKernel r C B ≤
        (ENNReal.ofReal (Real.exp (4 * |r|)) • equilibriumLaw r) B :=
    fun C => Measure.le_iff.mp (loopKernel_dominated_by_equilibrium r C) B hB
  simpa using lintegral_mono (μ := ρ) hb

theorem point_entropy_finite (r : ℝ) (C : SU2) :
    klDiv (loopKernel r C) (equilibriumLaw r) ≠ ⊤ := by
  letI : IsProbabilityMeasure (loopKernel r C) :=
    (loopKernel_markov r).isProbabilityMeasure C
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  exact OperatorDerivativeRewrite.Foundation.CauchyPoissonRegularization.entropy_finite_of_domination
    _ _ (Real.exp (4 * |r|)) (Real.exp_pos _).le
    (loopKernel_dominated_by_equilibrium r C)

theorem forward_entropy_finite (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] :
    klDiv (loopKernel r ∘ₘ ρ) (equilibriumLaw r) ≠ ⊤ := by
  letI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
  letI : IsProbabilityMeasure (equilibriumLaw r) := equilibriumLaw_probability r
  exact OperatorDerivativeRewrite.Foundation.CauchyPoissonRegularization.entropy_finite_of_domination
    _ _ (Real.exp (4 * |r|)) (Real.exp_pos _).le
    (forward_dominated_by_equilibrium r ρ)

theorem iterateLaw_shift (r : ℝ) (ρ : Measure SU2) (n : ℕ) :
    iterateLaw r ρ (n + 1) = iterateLaw r (loopKernel r ∘ₘ ρ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change loopKernel r ∘ₘ iterateLaw r ρ (n + 1) =
        loopKernel r ∘ₘ iterateLaw r (loopKernel r ∘ₘ ρ) n
      rw [ih]

theorem entropy_geometric_after_first (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) :
    klDiv (iterateLaw r ρ (n + 1)) (equilibriumLaw r) ≤
      (ENNReal.ofReal (1 - reset r)) ^ n *
        klDiv (loopKernel r ∘ₘ ρ) (equilibriumLaw r) := by
  rw [iterateLaw_shift]
  letI : IsMarkovKernel (loopKernel r) := loopKernel_markov r
  exact entropy_geometric r (loopKernel r ∘ₘ ρ) n

theorem entropy_after_first_finite (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] (n : ℕ) :
    klDiv (iterateLaw r ρ (n + 1)) (equilibriumLaw r) ≠ ⊤ := by
  have h := entropy_geometric_after_first r ρ n
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by simp) (forward_entropy_finite r ρ)) h

theorem point_start_one_step (r : ℝ) (C : SU2) :
    iterateLaw r (Measure.dirac C) 1 = loopKernel r C := by
  change loopKernel r ∘ₘ Measure.dirac C = loopKernel r C
  exact Measure.dirac_bind (Kernel.measurable (loopKernel r)) C

theorem point_start_entropy_finite (r : ℝ) (C : SU2) (n : ℕ) :
    klDiv (iterateLaw r (Measure.dirac C) (n + 1)) (equilibriumLaw r) ≠ ⊤ := by
  exact entropy_after_first_finite r (Measure.dirac C) n

theorem entropy_tendsto_zero_after_first (r : ℝ) (ρ : Measure SU2)
    [IsProbabilityMeasure ρ] :
    Tendsto (fun n : ℕ => klDiv (iterateLaw r ρ (n + 1)) (equilibriumLaw r))
      atTop (𝓝 0) := by
  have hc : ENNReal.ofReal (1 - reset r) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr
      ⟨by linarith [reset_pos r], by norm_num⟩
  have hA := forward_entropy_finite r ρ
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc
  have hbound : Tendsto (fun n : ℕ =>
      (ENNReal.ofReal (1 - reset r)) ^ n *
        klDiv (loopKernel r ∘ₘ ρ) (equilibriumLaw r)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hpow (Or.inr hA)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun n => bot_le) (fun n => entropy_geometric_after_first r ρ n)

theorem point_start_entropy_tendsto_zero (r : ℝ) (C : SU2) :
    Tendsto (fun n : ℕ =>
      klDiv (iterateLaw r (Measure.dirac C) (n + 1)) (equilibriumLaw r))
      atTop (𝓝 0) :=
  entropy_tendsto_zero_after_first r (Measure.dirac C)

end OperatorDerivativeRewrite.Foundation.SU2PointEntropy
