import Foundation.IBMUniformQuarticFamily

/-! Actual IBM uniform quartic fluctuations vanish in the original joint
scenery-clock probability space. Their conditional mean has not yet been
identified with a deterministic physical-time limit. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformQuarticProbability
open InfiniteGaussian IBMSourceLaws IBMUniformQuarticFamily IBMUniformClockGridEnergy
open IBMUniformClockMaximum IBMClockTraversalEnvelope
attribute [local irreducible] IBMUniformQuarticFamily.residual IBMUniformQuarticFamily.quartic
  IBMUniformQuarticFamily.clockMean IBMConstructedSources.clockPath

def tailEvent (T : ℝ≥0) (n : ℕ) (ε : ℝ) : Set JointSample :=
  {ω | ε ≤ |residual T n ω|}

theorem tailEvent_measurable (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    MeasurableSet (tailEvent T n ε) :=
  measurableSet_le measurable_const (continuous_abs.measurable.comp (residual_measurable T n))

def conditionalTail (T : ℝ≥0) (n : ℕ) (ε : ℝ) (y : SampleSpace) : ℝ :=
  ∫ x, (tailEvent T n ε).indicator (fun _ => (1 : ℝ)) (x,y) ∂gaussianProduct

theorem conditionalTail_eq_measure (T : ℝ≥0) (n : ℕ) (ε : ℝ) (y : SampleSpace) :
    conditionalTail T n ε y = gaussianProduct.real {x | ε ≤ |residual T n (x,y)|} := by
  change (∫ x, ({x | ε ≤ |residual T n (x,y)|}).indicator
    (fun _ => (1 : ℝ)) x ∂gaussianProduct) = _
  rw [integral_indicator_const]
  · simp
  · exact (tailEvent_measurable T n ε).preimage (measurable_id.prodMk measurable_const)

theorem conditionalTail_le_one (T : ℝ≥0) (n : ℕ) (ε : ℝ) (y : SampleSpace) :
    conditionalTail T n ε y ≤ 1 := by
  rw [conditionalTail_eq_measure]
  exact measureReal_le_one

theorem joint_indicator_integrable (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Integrable ((tailEvent T n ε).indicator (fun _ => (1 : ℝ))) jointMeasure :=
  (integrable_const 1).indicator (tailEvent_measurable T n ε)

theorem conditionalTail_integrable (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Integrable (conditionalTail T n ε) gaussianProduct :=
  (joint_indicator_integrable T n ε).integral_prod_right

/-- Fubini identifies the integral of genuine conditional tail probabilities
with the tail probability under the original joint scenery-clock measure. -/
theorem joint_tail_eq_integral (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    jointMeasure.real (tailEvent T n ε) =
      ∫ y, conditionalTail T n ε y ∂gaussianProduct := by
  calc
    _ = ∫ ω, (tailEvent T n ε).indicator (fun _ => (1 : ℝ)) ω ∂jointMeasure := by
      rw [integral_indicator_const 1 (tailEvent_measurable T n ε)]
      simp
    _ = _ := integral_prod_symm _ (joint_indicator_integrable T n ε)

theorem conditionalTail_chebyshev {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) (y : SampleSpace) :
    conditionalTail T n ε y ≤
      (∫ x, residual T n (x,y) ^ 2 ∂gaussianProduct) / ε ^ 2 := by
  rw [conditionalTail_eq_measure]
  calc
    _ ≤ gaussianProduct.real {x | ε ^ 2 ≤ residual T n (x,y) ^ 2} := by
      apply measureReal_mono (h₂ := by finiteness)
      intro x hx
      change ε ≤ |residual T n (x,y)| at hx
      change ε ^ 2 ≤ residual T n (x,y) ^ 2
      rw [← sq_abs (residual T n (x,y))]
      gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
      rw [mul_comm]
      exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
        (conditional_residual_square_integrable hT n hn y) (ε ^ 2)

theorem conditionalTail_good_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) {y : SampleSpace}
    (hy : y ∉ bad T n δ) :
    conditionalTail T n ε y ≤
      (96 / ε ^ 2) * (δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y) := by
  exact (conditionalTail_chebyshev hT n hn hε y).trans
    ((div_le_div_of_nonneg_right (conditional_residual_square_le hT n hn hδ hy)
      (sq_nonneg ε)).trans_eq (by ring))

/-- No global scenery-clock L2 error bound is assumed: a bounded indicator
and an integrable good-clock envelope suffice for the joint probability. -/
theorem joint_tail_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    jointMeasure.real (tailEvent T n ε) ≤ gaussianProduct.real (bad T n δ) +
      (96 / ε ^ 2) * (∫ y, δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y
        ∂gaussianProduct) := by
  let B := (bad T n δ).indicator (fun _ => (1 : ℝ))
  let E := fun y => δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ y
  let c := 96 / ε ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he (y : SampleSpace) : 0 ≤ E y := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => tent_nonneg _ _
  have hiB : Integrable B gaussianProduct :=
    (integrable_const 1).indicator (bad_measurable T n δ)
  have hiE : Integrable E gaussianProduct :=
    (energy_integrable (Finset.range n) (grid (T / n)) hδ.le).const_mul _
  rw [joint_tail_eq_integral]
  calc
    _ ≤ ∫ y, B y + c * E y ∂gaussianProduct := by
      apply integral_mono (conditionalTail_integrable T n ε) (hiB.add (hiE.const_mul c))
      intro y
      change conditionalTail T n ε y ≤ B y + c * E y
      by_cases hy : y ∈ bad T n δ
      · have hBy : B y = 1 := indicator_of_mem hy _
        rw [hBy]
        exact (conditionalTail_le_one T n ε y).trans (le_add_of_nonneg_right (mul_nonneg hc (he y)))
      · have hBy : B y = 0 := indicator_of_notMem hy _
        rw [hBy, zero_add]
        exact conditionalTail_good_le hT n hn hδ.le hε hy
    _ = _ := by
      rw [integral_add hiB (hiE.const_mul c), integral_const_mul]
      have hBmass : (∫ y, B y ∂gaussianProduct) = gaussianProduct.real (bad T n δ) := by
        dsimp only [B]
        rw [integral_indicator_const (1 : ℝ) (bad_measurable T n δ)]
        simp
      rw [hBmass]

attribute [local irreducible] IBMClockTraversalEnvelope.energy IBMUniformClockMaximum.bad

/-- Actual uniform-grid IBM quartic fluctuations about their EXACT clock-
conditional means vanish in probability, under the original joint law. -/
theorem residual_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (fun n : ℕ => residual T (n + 1))
      Filter.atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs]
  change Filter.Tendsto (fun n : ℕ => jointMeasure.real (tailEvent T (n + 1) ε))
    Filter.atTop (nhds 0)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n =>
    joint_tail_le hT (n + 1) (by omega)
      (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ)))
      (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) (-(4/9 : ℝ))) hε)
  simpa only [Nat.cast_add, Nat.cast_one, mul_zero, add_zero] using
    (bad_probability_tendsto T).add
      ((actual_weighted_energy_tendsto hT).const_mul (96 / ε ^ 2))

end OperatorDerivativeRewrite.Foundation.IBMUniformQuarticProbability
