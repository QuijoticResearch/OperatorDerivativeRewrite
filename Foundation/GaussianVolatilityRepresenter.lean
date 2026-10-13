import Foundation.GaussianPositiveVolatility
import Foundation.WeightedL2Transport

/-! A concrete weighted random representer, obtained from the already proved
closed Brownian derivative. This does not define an intrinsic closed derivative
on the volatility observable or identify a predictable adjoint with the full derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianVolatilityRepresenter
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeProductL2
open GaussianPredictableFull GaussianContinuousRigidity GaussianTimeSensitivity
open GaussianTimePolynomialPairing GaussianTimeDivergence GaussianPositiveVolatility
attribute [local instance] timeHilbert_secondCountable

/-- The positive coefficient on the finite horizon, extended positively outside it. -/
def coefficient (a : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  if z.1 ≤ (a : ℝ) then 1 else 1 + process a z.2 ^ 2

theorem coefficient_measurable (a : ℝ≥0) : Measurable (coefficient a) := by
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    measurable_const (measurable_const.add
      (((process_stronglyMeasurable a).measurable.comp measurable_snd).pow_const 2))

theorem coefficient_lower (a : ℝ≥0) (z : ℝ × SampleSpace) : 1 ≤ coefficient a z := by
  unfold coefficient
  split_ifs
  · rfl
  · linarith [sq_nonneg (process a z.2)]

theorem coefficient_ne_zero (a : ℝ≥0) (z : ℝ × SampleSpace) : coefficient a z ≠ 0 := by
  have := coefficient_lower a z
  linarith

abbrev horizonMeasure (b : ℝ≥0) := PredictableRealL2.horizonMeasure b gaussianProduct

def correctionField (a b : ℝ≥0) : TimeProbabilityL2 :=
  productTensor (timeVector a)
    ((2 : ℝ) • incrementProductL2 (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b)

def gradientField (a b : ℝ≥0) : TimeProbabilityL2 :=
  (volatilityField a b : TimeProbabilityL2) + correctionField a b

theorem gradientField_graph (a b : ℝ≥0) (hab : a ≤ b) :
    (itoIntegral (volatilityField a b), fieldEmbedding (gradientField a b)) ∈
      closedCylindricalDerivative.graph := by
  simpa only [gradientField, map_add, correctionField, fieldEmbedding_tensor,
    ← sensitivity_eq a b hab] using volatility_derivative_graph a b hab

theorem coefficient_eq_field (a b : ℝ≥0) :
    coefficient a =ᵐ[horizonMeasure b] (volatilityField a b : TimeProbabilityL2) := by
  apply (ae_restrict_iff' (PredictableRealL2.horizon_measurable b)).2
  filter_upwards [volatilityField_coeFn a b] with z hz hzb
  rw [hz]
  have hx : 0 < z.1 ∧ z.1 ≤ (b : ℝ) := hzb.1
  by_cases ha : z.1 ≤ (a : ℝ)
  · have hi : z.1 ∈ Ioc 0 (a : ℝ) := ⟨hx.1, ha⟩
    have hj : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := fun h => (not_lt_of_ge ha) h.1
    simp [coefficient, ha, hi, hj]
  · have hi : z.1 ∉ Ioc 0 (a : ℝ) := fun h => ha h.2
    have hj : z.1 ∈ Ioc (a : ℝ) (b : ℝ) := ⟨lt_of_not_ge ha, hx.2⟩
    simp [coefficient, ha, hi, hj]

theorem correctionField_coeFn (a b : ℝ≥0) :
    correctionField a b =ᵐ[timeProbability] fun z =>
      (Ioc 0 (a : ℝ)).indicator (fun _ => (1 : ℝ)) z.1 *
        (2 * process a z.2 * (process b z.2 - process a z.2)) := by
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (timeVector_coeFn a)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp
      (incrementProductL2_coeFn (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b)
  have hm := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp
      (Lp.coeFn_smul (2 : ℝ) (incrementProductL2 (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b))
  filter_upwards [productTensor_coeFn (timeVector a)
    ((2 : ℝ) • incrementProductL2 (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b), ht, hp, hm]
    with z hc ht hp hm
  change correctionField a b z = _ at hc
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, MvPolynomial.eval_X] at ht hp hm
  rw [hc, ht, hm, hp]
  ring

theorem quotient_memLp (a b : ℝ≥0) :
    MemLp (fun z => gradientField a b z / coefficient a z) 2
      (WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)) :=
  WeightedL2Transport.memLp_div _ _ (coefficient_measurable a)
    (ae_of_all _ (coefficient_ne_zero a)) ((Lp.memLp _).restrict _)

/-- The actual quotient L² class in the actual sigma-squared weighted measure. -/
def representer (a b : ℝ≥0) :
    Lp ℝ 2 (WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)) :=
  (quotient_memLp a b).toLp (fun z => gradientField a b z / coefficient a z)

theorem representer_coeFn (a b : ℝ≥0) :
    representer a b =ᵐ[WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)]
      fun z => gradientField a b z / coefficient a z := MemLp.coeFn_toLp _

theorem quotient_formula (a b : ℝ≥0) :
    (fun z => gradientField a b z / coefficient a z) =ᵐ[horizonMeasure b]
      fun z => 1 + (Ioc 0 (a : ℝ)).indicator (fun _ => (1 : ℝ)) z.1 *
        (2 * process a z.2 * (process b z.2 - process a z.2)) := by
  have hc := (ae_restrict_of_ae (correctionField_coeFn a b) :
    correctionField a b =ᵐ[horizonMeasure b] _)
  have hs := (ae_restrict_of_ae (Lp.coeFn_add (volatilityField a b : TimeProbabilityL2)
    (correctionField a b)) : gradientField a b =ᵐ[horizonMeasure b] _)
  filter_upwards [hc, hs, coefficient_eq_field a b] with z hc hs he
  simp only [Pi.add_apply] at hs
  rw [hs, ← he, hc]
  by_cases ha : z.1 ≤ (a : ℝ)
  · simp [coefficient, ha]
  · have hi : z.1 ∉ Ioc 0 (a : ℝ) := fun h => ha h.2
    simp only [indicator_of_notMem hi, zero_mul, add_zero, div_self (coefficient_ne_zero a z)]

theorem representer_formula (a b : ℝ≥0) :
    representer a b =ᵐ[WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)]
      fun z => 1 + (Ioc 0 (a : ℝ)).indicator (fun _ => (1 : ℝ)) z.1 *
        (2 * process a z.2 * (process b z.2 - process a z.2)) :=
  (representer_coeFn a b).trans
    ((WeightedL2Transport.weightedMeasure_absolutelyContinuous _ _).ae_eq (quotient_formula a b))


/-- The future correction is not almost everywhere any deterministic scalar. -/
theorem correction_not_constant (a b : ℝ≥0) (ha : 0 < a) (hab : a < b) (c : ℝ) :
    ¬ (fun ω => 2 * process a ω * (process b ω - process a ω)) =ᵐ[gaussianProduct]
      fun _ => c := by
  intro he
  let A : GaussianL2 := (2 : ℝ) •
    incrementProductL2 (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b
  have hA : A =ᵐ[gaussianProduct]
      fun ω => 2 * process a ω * (process b ω - process a ω) := by
    filter_upwards [Lp.coeFn_smul (2 : ℝ)
      (incrementProductL2 (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b),
      incrementProductL2_coeFn (fun _ : Fin 1 => a) (MvPolynomial.X 0) a b] with ω hm hp
    change A ω = _ at hm
    simp only [Pi.smul_apply, smul_eq_mul, MvPolynomial.eval_X] at hm hp
    rw [hm, hp]
    ring
  have hcenter : ∫ ω, A ω ∂gaussianProduct = 0 := by
    have hj := itoIntegral_centered ((2 : ℝ) • GaussianSensitivityCore.pastStep a b
      (fun _ : Fin 1 => a) (fun _ => le_rfl) (MvPolynomial.X 0))
    simpa only [map_smul, GaussianSensitivityCore.ito_pastStep a b hab.le] using hj
  have hc : c = 0 := by
    have heq := integral_congr_ae (hA.trans he)
    simpa [hcenter] using heq.symm
  have hzero : A = 0 := by
    apply Lp.ext
    filter_upwards [hA.trans he, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct)] with ω hω hz
    simp only [hc, Pi.zero_apply] at hω hz
    exact hω.trans hz.symm
  have hs := sensitivity_eq a b hab.le
  change incrementSensitivity _ _ _ _ = scalarTensor _ A at hs
  rw [hzero, map_zero] at hs
  exact sensitivity_ne_zero a b ha hab hs

/-- No deterministic time profile represents this weighted L² class. -/
theorem representer_not_deterministic (a b : ℝ≥0) (ha : 0 < a) (hab : a < b)
    (k : ℝ → ℝ) :
    ¬ representer a b =ᵐ[WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)]
      fun z => k z.1 := by
  intro hk
  have hm := (WeightedL2Transport.absolutelyContinuous_weightedMeasure
    (horizonMeasure b) (coefficient a) (coefficient_measurable a)
    (ae_of_all _ (coefficient_ne_zero a))).ae_eq ((representer_formula a b).symm.trans hk)
  have hh := (ae_restrict_iff' (PredictableRealL2.horizon_measurable b)).1 hm
  have hsections := Measure.ae_ae_of_ae_prod hh
  have hvol : (volume : Measure ℝ) (Ioc 0 (a : ℝ)) ≠ 0 := by
    rw [Real.volume_Ioc, sub_zero]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  obtain ⟨s, hs, hsec⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae hsections)
  apply correction_not_constant a b ha hab (k s - 1)
  filter_upwards [hsec] with ω hω
  have hmem : (s, ω) ∈ PredictableRealL2.horizon b :=
    ⟨⟨hs.1, hs.2.trans (show (a : ℝ) ≤ b from hab.le)⟩, mem_univ _⟩
  have he := hω hmem
  simp only [indicator_of_mem hs, one_mul] at he
  linarith

theorem representer_sq_integrable (a b : ℝ≥0) :
    Integrable (fun z => representer a b z ^ 2)
      (WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a)) :=
  (Lp.memLp _).integrable_sq

theorem gradientField_sq_integrable (a b : ℝ≥0) :
    Integrable (fun z => gradientField a b z ^ 2) (horizonMeasure b) :=
  ((Lp.memLp _).restrict _).integrable_sq

/-- Actual recovery of the already proved source gradient, on the finite horizon. -/
theorem coefficient_mul_representer (a b : ℝ≥0) :
    (fun z => coefficient a z * representer a b z) =ᵐ[horizonMeasure b] gradientField a b := by
  have hr := (WeightedL2Transport.absolutelyContinuous_weightedMeasure
    (horizonMeasure b) (coefficient a) (coefficient_measurable a)
    (ae_of_all _ (coefficient_ne_zero a))).ae_eq (representer_coeFn a b)
  filter_upwards [hr] with z hz
  rw [hz]
  field_simp [coefficient_ne_zero a z]

/-- Weighted representer energy equals source derivative energy; both integrals are finite. -/
theorem representer_energy (a b : ℝ≥0) :
    ∫ z, representer a b z ^ 2
        ∂WeightedL2Transport.weightedMeasure (horizonMeasure b) (coefficient a) =
      ∫ z, gradientField a b z ^ 2 ∂horizonMeasure b := by
  rw [WeightedL2Transport.integral_weighted _ _ (coefficient_measurable a)]
  apply integral_congr_ae
  filter_upwards [coefficient_mul_representer a b] with z hz
  rw [← mul_pow, hz]
end OperatorDerivativeRewrite.Foundation.GaussianVolatilityRepresenter
