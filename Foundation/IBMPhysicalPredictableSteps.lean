import Foundation.IBMPhysicalCorrectionSteps

/-! Genuine physical predictable inputs for arbitrary L2 past coefficients.
The original physical Ito map is identified with the actual increment product. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPredictableSteps
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianTimeHilbert
open IBMPhysicalWeakWiener IBMPhysicalPastIncrement
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def field (a b : ℝ≥0) (f : SampleSpace → Kernel) (z : ℝ × SampleSpace) : Kernel :=
  (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => f z.2) z.1

private theorem nonnegative_predictable (a b : ℝ≥0) (f : SampleSpace → Kernel)
    (hf : StronglyMeasurable[naturalFiltration a] f) :
    StronglyMeasurable[naturalFiltration.predictable]
      ((Ioc a b ×ˢ (univ : Set SampleSpace)).indicator (fun z => f z.2)) := by
  classical
  let Y0 : SampleSpace := Classical.choice inferInstance
  let mask (z : ℝ≥0 × SampleSpace) : SampleSpace := if z.1 ∈ Ioc a b then z.2 else Y0
  have hI := measurableSet_predictable_Ioc_prod (𝓕 := naturalFiltration) a b
    (s := (univ : Set SampleSpace)) MeasurableSet.univ
  have hm : Measurable[naturalFiltration.predictable, naturalFiltration a] mask := by
    intro A hA
    have hrect := measurableSet_predictable_Ioc_prod (𝓕 := naturalFiltration) a b hA
    by_cases h0 : Y0 ∈ A
    · convert hrect.union hI.compl using 1
      ext z
      by_cases hz : a < z.1 ∧ z.1 ≤ b <;> simp [mask, mem_Ioc, hz, h0]
    · convert hrect using 1
      ext z
      by_cases hz : a < z.1 ∧ z.1 ≤ b <;> simp [mask, mem_Ioc, hz, h0]
  convert (hf.comp_measurable hm).indicator hI using 1
  funext z
  by_cases hz : a < z.1 ∧ z.1 ≤ b <;> simp [mask, mem_Ioc, hz]

private theorem real_cell_iff (a b : ℝ≥0) (r : ℝ) :
    r.toNNReal ∈ Ioc a b ↔ r ∈ Ioc (a : ℝ) (b : ℝ) := by
  by_cases hr : 0 ≤ r
  · simp only [mem_Ioc]
    rw [← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal r hr]
  · have hr0 : r ≤ 0 := (lt_of_not_ge hr).le
    have hn : ¬r ∈ Ioc (a : ℝ) (b : ℝ) := fun h =>
      (not_lt_of_ge (hr0.trans a.coe_nonneg)) h.1
    rw [Real.toNNReal_of_nonpos hr0]
    simp only [mem_Ioc, not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ a), false_and, hn]
    constructor
    · intro h
      exact (not_lt_of_ge (bot_le : (0 : ℝ≥0) ≤ a)) h.1
    · exact False.elim

theorem field_stronglyPredictable (a b : ℝ≥0) (f : SampleSpace → Kernel)
    (hf : StronglyMeasurable[naturalFiltration a] f) :
    StronglyMeasurable[PredictableRealL2.predictable naturalFiltration] (field a b f) := by
  have hm := (nonnegative_predictable a b f hf).comp_measurable
    (show Measurable[PredictableRealL2.predictable naturalFiltration, naturalFiltration.predictable]
      PredictableRealL2.toNonnegative from Measurable.of_comap_le le_rfl)
  convert hm using 1
  funext z
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ)
  · have hn := (real_cell_iff a b z.1).mpr hz
    simp [field, Function.comp_def, PredictableRealL2.toNonnegative, hz, hn]
  · have hn : z.1.toNNReal ∉ Ioc a b := fun h => hz ((real_cell_iff a b z.1).mp h)
    simp [field, Function.comp_def, PredictableRealL2.toNonnegative, hz, hn]

theorem field_predictable (a b : ℝ≥0) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration] (field a b U) timeProbability := by
  have h := field_stronglyPredictable a b (hU.mk U) hU.stronglyMeasurable_mk
  apply h.aestronglyMeasurable.congr
  have he := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp hU.ae_eq_mk
  filter_upwards [he] with z hz
  simp only [Function.comp_apply] at hz
  simp only [field, hz]

theorem field_memLp (a b : ℝ≥0) (U : Lp Kernel 2 gaussianProduct) :
    MemLp (field a b U) 2 timeProbability := by
  have hm : AEStronglyMeasurable (field a b U) timeProbability := by
    have h : StronglyMeasurable ((Ioc (a : ℝ) (b : ℝ) ×ˢ (univ : Set SampleSpace)).indicator
        (fun z => U z.2)) :=
      ((Lp.stronglyMeasurable U).comp_measurable measurable_snd).indicator
        (measurableSet_Ioc.prod MeasurableSet.univ)
    convert h.aestronglyMeasurable using 1
    funext z
    by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;> simp [field, hz]
  apply (Lp.memLp (productTensor (intervalVector a b) (normClass U))).of_le hm
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn a b)
  have hu := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (normClass_ae U)
  filter_upwards [productTensor_coeFn (intervalVector a b) (normClass U), ht, hu] with z hp ht hu
  simp only [Function.comp_apply] at ht hu
  rw [hp, ht, hu]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;>
    simp [field, hz, Real.norm_of_nonneg (norm_nonneg (U z.2))]

def fieldClass (a b : ℝ≥0) (U : Lp Kernel 2 gaussianProduct) : Lp Kernel 2 timeProbability :=
  (field_memLp a b U).toLp (field a b U)

theorem fieldClass_ae (a b : ℝ≥0) (U : Lp Kernel 2 gaussianProduct) :
    fieldClass a b U =ᵐ[timeProbability] field a b U := (field_memLp a b U).coeFn_toLp

def input (a b T : ℝ≥0) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) : IBMPhysicalClockIto.Domain T :=
  ⟨IBMSchwartzPhysicalClockIntegral.restriction T (fieldClass a b U),
    ((field_predictable a b U hU).congr (fieldClass_ae a b U).symm).restrict.congr
      (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (fieldClass a b U)).symm⟩

theorem input_ae (a b T : ℝ≥0) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    (input a b T U hU).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct] field a b U :=
  (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (fieldClass a b U)).trans
    (ae_restrict_of_ae (fieldClass_ae a b U))

theorem input_zero_extension (a b T : ℝ≥0) (hbT : b ≤ T) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    (PredictableRealL2.horizon T).indicator (fun z => (input a b T U hU).val z) =ᵐ[timeProbability]
      field a b U := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (input_ae a b T U hU)
  apply h.trans
  apply Eventually.of_forall
  intro z
  by_cases hh : z ∈ PredictableRealL2.horizon T
  · exact indicator_of_mem hh _
  · have hz : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := by
      intro hz
      exact hh ⟨⟨a.coe_nonneg.trans_lt hz.1, hz.2.trans (show (b : ℝ) ≤ T from hbT)⟩, mem_univ _⟩
    simp only [indicator_of_notMem hh, field, indicator_of_notMem hz]

theorem integral_input (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    IBMPhysicalClockIto.integral T (input a b T U hU) = IBMPhysicalPastIncrement.product a b hab U hU :=
  IBMPhysicalPastIncrement.integral_eq_product a b T hab U hU (input a b T U hU)
    (input_zero_extension a b T hbT U hU)

theorem input_norm_sq (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    ‖input a b T U hU‖^2 = ((b : ℝ)-a)*‖U‖^2 := by
  rw [← IBMPhysicalClockIto.integral_norm T, integral_input a b T hab hbT]
  exact IBMPhysicalPastIncrement.product_energy a b hab U hU

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPredictableSteps
