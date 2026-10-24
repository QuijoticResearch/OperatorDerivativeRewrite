import Foundation.IBMPhysicalHorizonCompatibility

/-! Actual physical random past coefficients times Brownian increments.
Integrability follows from the existing scalar independence theorem applied
to the norm of the coefficient. No bounded coefficient assumption is added. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPastIncrement
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeHilbert GaussianPastStepCompletion IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

def normClass (U : Lp Kernel 2 gaussianProduct) : GaussianL2 :=
  (Lp.memLp U).norm.toLp (fun Y => ‖U Y‖)

theorem normClass_ae (U : Lp Kernel 2 gaussianProduct) :
    normClass U =ᵐ[gaussianProduct] fun Y => ‖U Y‖ :=
  (Lp.memLp U).norm.coeFn_toLp

theorem normClass_past (a : ℝ≥0) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    AEStronglyMeasurable[naturalFiltration a] (normClass U) gaussianProduct :=
  (continuous_norm.comp_aestronglyMeasurable hU).congr (normClass_ae U).symm

theorem product_memLp (a b : ℝ≥0) (hab : a ≤ b) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    MemLp (fun Y => (process b Y-process a Y) • U Y) 2 gaussianProduct := by
  apply (memLp_two_iff_integrable_sq_norm
    (((process_stronglyMeasurable b).sub (process_stronglyMeasurable a)).smul
      (Lp.stronglyMeasurable U)).aestronglyMeasurable).mpr
  have hi := (past_increment_sq a b hab (normClass U) (normClass_past a U hU)).1
  apply hi.congr
  filter_upwards [normClass_ae U] with Y he
  change (normClass U Y * (process b Y-process a Y))^2 =
    ‖(process b Y-process a Y) • U Y‖^2
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  ring

def product (a b : ℝ≥0) (hab : a ≤ b) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    Lp Kernel 2 gaussianProduct := (product_memLp a b hab U hU).toLp _

theorem product_ae (a b : ℝ≥0) (hab : a ≤ b) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    product a b hab U hU =ᵐ[gaussianProduct]
      fun Y => (process b Y-process a Y) • U Y :=
  (product_memLp a b hab U hU).coeFn_toLp

theorem product_scalarization (a b : ℝ≥0) (hab : a ≤ b)
    (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) (L : Tests) :
    L.compLpL 2 gaussianProduct (product a b hab U hU) =
      pastIncrement a b hab (L.compLpL 2 gaussianProduct U)
        ((L.continuous.comp_aestronglyMeasurable hU).congr
          (L.coeFn_compLpL U).symm) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (product a b hab U hU), product_ae a b hab U hU,
    pastIncrement_coeFn a b hab (L.compLpL 2 gaussianProduct U)
      ((L.continuous.comp_aestronglyMeasurable hU).congr (L.coeFn_compLpL U).symm),
    L.coeFn_compLpL U] with Y hl hp hr hu
  rw [hl, hp, hr, hu, map_smul]
  change (process b Y-process a Y)*L (U Y) = L (U Y)*(process b Y-process a Y)
  ring

theorem product_energy (a b : ℝ≥0) (hab : a ≤ b) (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    ‖product a b hab U hU‖^2 = ((b : ℝ)-a)*‖U‖^2 := by
  rw [BochnerL2Dominated.norm_sq_integral, BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ Y, (normClass U Y * (process b Y-process a Y))^2 ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [product_ae a b hab U hU, normClass_ae U] with Y hp hn
      rw [hp, hn, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
      ring
    _ = _ := by
      rw [(past_increment_sq a b hab (normClass U) (normClass_past a U hU)).2]
      congr 1
      apply integral_congr_ae
      filter_upwards [normClass_ae U] with Y hn
      rw [hn]

/- The premise is equality of actual physical fields, not a definition of
the integral. The conclusion uses the original Ito map. -/
theorem integral_eq_product (a b T : ℝ≥0) (hab : a ≤ b)
    (U : Lp Kernel 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct)
    (u : IBMPhysicalClockIto.Domain T)
    (hu : (PredictableRealL2.horizon T).indicator (fun z => u.val z)
      =ᵐ[GaussianTimeProductL2.timeProbability] fun z =>
        (Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => U z.2) z.1) :
    IBMPhysicalClockIto.integral T u = product a b hab U hU := by
  apply IBMPhysicalLpSeparation.ext
  intro L
  let A := L.compLpL 2 gaussianProduct U
  have hA : AEStronglyMeasurable[naturalFiltration a] A gaussianProduct :=
    (L.continuous.comp_aestronglyMeasurable hU).congr (L.coeFn_compLpL U).symm
  let v : GaussianPredictableFull.fullPredictable :=
    ⟨GaussianTimeProductL2.productTensor (intervalVector a b) A,
      GaussianPredictableFull.past_step_mem_fullPredictable a b A hA⟩
  have hv : IBMPhysicalHorizonCompatibility.scalarField T L u = v := by
    apply Subtype.ext
    apply Lp.ext
    have ht := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn a b)
    have hc := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (L.coeFn_compLpL U)
    filter_upwards [IBMPhysicalHorizonCompatibility.scalarField_ae T L u, hu,
      GaussianTimeProductL2.productTensor_coeFn (intervalVector a b) A, ht, hc]
      with z hs hu hp ht hc
    change v.val z = _ at hp
    simp only [Function.comp_apply] at ht hc
    change A z.2 = L (U z.2) at hc
    rw [hs, hp, ht]
    have he := congrArg L hu
    by_cases hh : z ∈ PredictableRealL2.horizon T <;>
      by_cases hi : z.1 ∈ Set.Ioc (a : ℝ) (b : ℝ) <;>
      simpa [hh, hi, hc] using he
  rw [IBMPhysicalHorizonCompatibility.scalarization, hv]
  apply Lp.ext
  filter_upwards [GaussianPredictableFull.itoIntegral_past_step a b hab A hA,
    L.coeFn_compLpL (product a b hab U hU), product_ae a b hab U hU,
    L.coeFn_compLpL U] with Y hi hl hp hu
  rw [hi, hl, hp, map_smul, hu]
  change L (U Y)*(process b Y-process a Y) = (process b Y-process a Y)*L (U Y)
  ring

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPastIncrement
