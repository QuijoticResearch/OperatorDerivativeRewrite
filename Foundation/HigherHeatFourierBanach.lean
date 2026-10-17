import Foundation.L1SeriesSynthesis
import Foundation.HigherHeatMixedFourierPaths
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! A genuine completed Fourier path test space and its normalized continuous expectation. -/
noncomputable section
open MeasureTheory Filter
open scoped lp ENNReal NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierBanach
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatMixedFourierPaths HigherHeatInterpolatedPaths HigherHeatWeightedPaths

def spectrumLevels (levels : ℕ → ℕ) : ℕ → ℕ | 0 => 0 | i+1 => levels i

def spectrumFrequency (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i)) :
    (i : ℕ) → Grid (spectrumLevels levels i)
  | 0 => 0
  | i+1 => ξ i

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def characterTest (i : ℕ) : Path →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (character (spectrumLevels levels) (spectrumFrequency levels ξ) i)
    (character_continuous _ _ i) 1 (fun ω => (character_norm _ _ i ω).le)

theorem characterTest_apply (i : ℕ) (ω : Path) : characterTest levels ξ i ω=
    character (spectrumLevels levels) (spectrumFrequency levels ξ) i ω := rfl

theorem characterTest_bound (i : ℕ) : ‖characterTest levels ξ i‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).mpr (fun ω => (character_norm _ _ i ω).le)

def realization : Coeff →L[ℂ] (Path →ᵇ ℂ) := synthesis (characterTest levels ξ) (characterTest_bound levels ξ)

theorem realization_apply (a : Coeff) (ω : Path) : realization levels ξ a ω=
    series (spectrumLevels levels) (spectrumFrequency levels ξ) a ω := by
  rw [realization, synthesis_apply]
  have he := (BoundedContinuousFunction.evalCLM ℂ ω).map_tsum
    (terms_summable (characterTest levels ξ) (characterTest_bound levels ξ) a)
  simpa only [BoundedContinuousFunction.evalCLM_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, characterTest_apply, series] using he

theorem realization_bound (a : Coeff) : ‖realization levels ξ a‖ ≤ ‖a‖ :=
  synthesis_bound _ _ a

theorem expectedCharacter_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖expectedCharacter (spectrumLevels levels) (spectrumFrequency levels ξ) m hm T hT i‖ ≤ 1 := by
  have hh := character_expectation_bound (spectrumLevels levels) (spectrumFrequency levels ξ)
    m hm T hT (spectrumLevels levels i) i
  rwa [character_expectation_coarse _ _ m hm T hT _ i le_rfl] at hh

def coefficientExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Coeff →L[ℂ] ℂ :=
  synthesis (expectedCharacter (spectrumLevels levels) (spectrumFrequency levels ξ) m hm T hT)
    (expectedCharacter_bound levels ξ m hm T hT)

theorem coefficientExpectation_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    coefficientExpectation levels ξ m hm T hT a=
      expectedSeries (spectrumLevels levels) (spectrumFrequency levels ξ) a m hm T hT := by
  simp only [coefficientExpectation, synthesis_apply, smul_eq_mul, expectedSeries]

theorem coefficientExpectation_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    ‖coefficientExpectation levels ξ m hm T hT a‖ ≤ ‖a‖ := synthesis_bound _ _ a

def kernel : Submodule ℂ Coeff := (realization levels ξ).ker

instance kernel_closed : IsClosed (kernel levels ξ : Set Coeff) := (realization levels ξ).isClosed_ker

theorem kernel_le_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    kernel levels ξ ≤ (coefficientExpectation levels ξ m hm T hT).ker := by
  intro a ha
  change realization levels ξ a=0 at ha
  change coefficientExpectation levels ξ m hm T hT a=0
  have hf : ∀ ω, series (spectrumLevels levels) (spectrumFrequency levels ξ) a ω=
      series (spectrumLevels levels) (spectrumFrequency levels ξ) (0 : Coeff) ω := by
    intro ω
    rw [← realization_apply levels ξ a ω, ← realization_apply levels ξ (0 : Coeff) ω, ha, map_zero]
  have he := representation_independent (spectrumLevels levels) (spectrumFrequency levels ξ) a
    (coeff_summable a) (spectrumLevels levels) (spectrumFrequency levels ξ) (0 : Coeff)
    (coeff_summable 0) hf m hm T hT
  rw [← coefficientExpectation_apply, ← coefficientExpectation_apply, map_zero] at he
  exact he

abbrev TestSpace := Coeff ⧸ kernel levels ξ

theorem testSpace_complete : CompleteSpace (TestSpace levels ξ) := inferInstance

def realize : TestSpace levels ξ →L[ℂ] (Path →ᵇ ℂ) :=
  (kernel levels ξ).liftQL (realization levels ξ) le_rfl

def expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : TestSpace levels ξ →L[ℂ] ℂ :=
  (kernel levels ξ).liftQL (coefficientExpectation levels ξ m hm T hT) (kernel_le_expectation levels ξ m hm T hT)

theorem realize_mk (a : Coeff) : realize levels ξ ((kernel levels ξ).mkQ a)=realization levels ξ a := rfl

theorem expectation_mk (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    expectation levels ξ m hm T hT ((kernel levels ξ).mkQ a)=coefficientExpectation levels ξ m hm T hT a := rfl

theorem realize_injective : Function.Injective (realize levels ξ) := by
  intro x y hxy
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective x
  obtain ⟨b,rfl⟩ := (kernel levels ξ).mkQ_surjective y
  apply (Submodule.Quotient.eq (kernel levels ξ)).mpr
  change realization levels ξ (a-b)=0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

theorem realize_bound (q : TestSpace levels ξ) : ‖realize levels ξ q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : realize levels ξ q=realization levels ξ a := by rw [← ha]; rfl
  rw [he]
  exact (realization_bound levels ξ a).trans hna.le

theorem expectation_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖expectation levels ξ m hm T hT q‖ ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q hε
  have he : expectation levels ξ m hm T hT q=coefficientExpectation levels ξ m hm T hT a := by rw [← ha]; rfl
  rw [he]
  exact (coefficientExpectation_bound levels ξ m hm T hT a).trans hna.le

theorem expectation_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    Tendsto (fun n => ∫ᵛ ω, realize levels ξ q ω ∂<•signedPath m hm T hT n) atTop
      (𝓝 (expectation levels ξ m hm T hT q)) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  simpa only [realize_mk, realization_apply, expectation_mk, coefficientExpectation_apply] using
    series_expectation_tendsto (spectrumLevels levels) (spectrumFrequency levels ξ) a
      (coeff_summable a) m hm T hT

theorem weighted_expectation_limit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    Tendsto (fun n => ∫ ω, pathWeight m hm T hT n ω • realize levels ξ q ω ∂probabilityPath m hm T hT n)
      atTop (𝓝 (expectation levels ξ m hm T hT q)) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  simpa only [realize_mk, realization_apply, expectation_mk, coefficientExpectation_apply] using
    weighted_series_tendsto (spectrumLevels levels) (spectrumFrequency levels ξ) a
      (coeff_summable a) m hm T hT

def unit : TestSpace levels ξ := (kernel levels ξ).mkQ (lp.single 1 0 (1 : ℂ))

theorem realize_unit : realize levels ξ (unit levels ξ)=1 := by
  rw [unit, realize_mk, realization, synthesis_apply]
  rw [tsum_eq_single 0]
  · rw [lp.coeFn_single, Pi.single_eq_same, one_smul]
    ext ω
    change SignedDensityIntegral.configurationPhase (0 : Grid 0) (sample 0 ω)=1
    simp [SignedDensityIntegral.configurationPhase]
  · intro i hi
    rw [lp.coeFn_single, Pi.single_eq_of_ne hi, zero_smul]

theorem expectation_unit (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    expectation levels ξ m hm T hT (unit levels ξ)=1 := by
  rw [unit, expectation_mk, coefficientExpectation, synthesis_apply]
  rw [tsum_eq_single 0]
  · rw [lp.coeFn_single, Pi.single_eq_same, one_smul]
    change (∫ᵛ y, SignedDensityIntegral.configurationPhase (0 : Grid 0) y ∂<•law m hm T hT 0)=1
    simp only [SignedDensityIntegral.configurationPhase, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      neg_zero, map_zero]
    rw [VectorMeasure.integral_const, law_mass]
    simp
  · intro i hi
    rw [lp.coeFn_single, Pi.single_eq_of_ne hi, zero_smul]

theorem unit_norm : ‖unit levels ξ‖=1 := by
  apply le_antisymm
  · calc
      ‖unit levels ξ‖ ≤ ‖(lp.single 1 0 (1 : ℂ) : Coeff)‖ := Submodule.Quotient.norm_mk_le _ _
      _ = 1 := by simp
  · have hh := expectation_bound levels ξ 1 (by norm_num) 1 (by norm_num) (unit levels ξ)
    simpa only [expectation_unit, norm_one] using hh

theorem expectation_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖expectation levels ξ m hm T hT‖=1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa only [one_mul] using expectation_bound levels ξ m hm T hT q
  · have hh := (expectation levels ξ m hm T hT).le_opNorm (unit levels ξ)
    simpa only [expectation_unit, norm_one, unit_norm, mul_one] using hh

def generator (i : ℕ) : TestSpace levels ξ := (kernel levels ξ).mkQ (lp.single 1 i (1 : ℂ))

theorem realize_generator (i : ℕ) : realize levels ξ (generator levels ξ i)=characterTest levels ξ i := by
  rw [generator, realize_mk, realization, synthesis_apply, tsum_eq_single i]
  · rw [lp.coeFn_single, Pi.single_eq_same, one_smul]
  · intro j hj
    rw [lp.coeFn_single, Pi.single_eq_of_ne hj, zero_smul]

theorem partial_sums_tendsto (a : Coeff) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, a i • generator levels ξ i) atTop
      (𝓝 ((kernel levels ξ).mkQ a)) := by
  have ht := ((kernel levels ξ).mkQL).continuous.tendsto a |>.comp
    (lp.hasSum_single (p := 1) (by simp) a).tendsto_sum_nat
  have he (i : ℕ) : (kernel levels ξ).mkQL (lp.single 1 i (a i))=a i • generator levels ξ i := by
    have hs : (lp.single 1 i (a i) : Coeff)=a i • (lp.single 1 i (1 : ℂ) : Coeff) := by
      rw [← lp.single_smul]
      simp
    rw [hs, map_smul]
    rfl
  change Tendsto (fun n => (kernel levels ξ).mkQL (∑ i ∈ Finset.range n, lp.single 1 i (a i)))
    atTop (𝓝 ((kernel levels ξ).mkQL a)) at ht
  simpa only [map_sum, he, Submodule.mkQL_apply] using ht

theorem finite_core_dense :
    Dense (Submodule.span ℂ (Set.range (generator levels ξ)) : Set (TestSpace levels ξ)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  apply mem_closure_of_tendsto (partial_sums_tendsto levels ξ a)
  exact Eventually.of_forall fun n => Submodule.sum_mem _ (fun i hi =>
    Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i,rfl⟩))

theorem test_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (q : TestSpace levels ξ) : (signedPath m hm T hT n).Integrable (realize levels ξ q) :=
  SignedDensityIntegral.bounded_signed_integrable _ _ (realize levels ξ q).continuous.measurable
    ‖realize levels ξ q‖ (fun ω => (realize levels ξ q).norm_coe_le_norm ω)

theorem weighted_test_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (q : TestSpace levels ξ) :
    Integrable (fun ω => pathWeight m hm T hT n ω • realize levels ξ q ω) (probabilityPath m hm T hT n) :=
  path_weighted_integrable m hm T hT n _ (test_integrable levels ξ m hm T hT n q)

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierBanach
