import Foundation.IBMSpatialHilbertRetract

/-! Ordinary spatial L2 predictable steps, using the ORIGINAL parameter Ito map.
The auxiliary Hilbert retract only transports existing step verification. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPredictableSteps
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianComplexHorizonIto
open IBMPhysicalWeakWiener IBMSpatialHilbertRetract
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

abbrev Domain (T : ℝ≥0) := lpMeas TimeHilbert ℝ
  (PredictableRealL2.predictable naturalFiltration) 2
  (PredictableRealL2.horizonMeasure T gaussianProduct)

def trim (T : ℝ≥0) : Domain T ≃ₗᵢ[ℝ] Lp TimeHilbert 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie TimeHilbert ℝ 2
    (PredictableRealL2.horizonMeasure T gaussianProduct)
    (PredictableRealL2.predictable_le naturalFiltration)

def integral (T : ℝ≥0) (u : Domain T) : Lp TimeHilbert 2 gaussianProduct :=
  GaussianParameterizedIto.realIntegral volume T (trim T u)

private theorem trim_scalar_match (T : ℝ≥0) (u : Domain T)
    (v : IBMPhysicalClockIto.Domain T)
    (h : model.toContinuousLinearMap.compLpL 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) u.val = v.val) (L : Tests) :
    (L.comp model.toContinuousLinearMap).compLpL 2 (predictableMeasure T) (trim T u) =
      L.compLpL 2 (predictableMeasure T) (IBMPhysicalClockIto.trimEquiv T v) := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply Lp.ext
  apply ae_eq_trim_of_measurable (PredictableRealL2.predictable_le naturalFiltration)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have ho := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration) u
  have hp := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration) v
  have he := model.toContinuousLinearMap.coeFn_compLpL u.val
  rw [h] at he
  filter_upwards [ae_eq_of_ae_eq_trim
    ((L.comp model.toContinuousLinearMap).coeFn_compLpL (trim T u)),
    ae_eq_of_ae_eq_trim (L.coeFn_compLpL (IBMPhysicalClockIto.trimEquiv T v)),
    ho, hp, he] with z hl hr ho hp he
  change trim T u z = _ at ho
  change IBMPhysicalClockIto.trimEquiv T v z = _ at hp
  rw [hl, hr, ho, hp, he]
  rfl

theorem model_integral (T : ℝ≥0) (u : Domain T) (v : IBMPhysicalClockIto.Domain T)
    (h : model.toContinuousLinearMap.compLpL 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) u.val = v.val) :
    lift (integral T u) = IBMPhysicalClockIto.integral T v := by
  apply IBMPhysicalLpSeparation.ext
  intro L
  have hc : L.compLpL 2 gaussianProduct (lift (integral T u)) =
      (L.comp model.toContinuousLinearMap).compLpL 2 gaussianProduct (integral T u) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (lift (integral T u)), lift_ae (integral T u),
      (L.comp model.toContinuousLinearMap).coeFn_compLpL (integral T u)] with Y hl hu hr
    rw [hl, hu, hr]
    rfl
  rw [hc]
  change (L.comp model.toContinuousLinearMap).compLpL 2 gaussianProduct
    (GaussianParameterizedIto.realIntegral volume T (trim T u)) = _
  rw [GaussianRealParameterizedItoScalar.realIntegral_scalarization,
    trim_scalar_match T u v h, ← IBMPhysicalClockItoScalar.native_scalarization]

theorem lift_past (a : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    AEStronglyMeasurable[naturalFiltration a] (lift U) gaussianProduct :=
  (model.continuous.comp_aestronglyMeasurable hU).congr (lift_ae U).symm

def input (a b T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) : Domain T :=
  let v := IBMPhysicalPredictableSteps.input a b T (lift U) (lift_past a U hU)
  ⟨recover.compLpL 2 (PredictableRealL2.horizonMeasure T gaussianProduct) v.val,
    (recover.continuous.comp_aestronglyMeasurable v.property).congr
      (recover.coeFn_compLpL v.val).symm⟩

theorem input_ae (a b T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    (input a b T U hU).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => (Set.Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => U z.2) z.1 := by
  have hu := ae_restrict_of_ae (s := PredictableRealL2.horizon T)
    ((Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (lift_ae U))
  filter_upwards [recover.coeFn_compLpL
    (IBMPhysicalPredictableSteps.input a b T (lift U) (lift_past a U hU)).val,
    IBMPhysicalPredictableSteps.input_ae a b T (lift U) (lift_past a U hU), hu]
    with z hr hv hu
  change (input a b T U hU).val z = _ at hr
  simp only [Function.comp_apply] at hu
  rw [hr, hv]
  by_cases hz : z.1 ∈ Set.Ioc (a : ℝ) (b : ℝ)
  · simp only [IBMPhysicalPredictableSteps.field, Set.indicator_of_mem hz, hu, recover_model]
  · simp only [IBMPhysicalPredictableSteps.field, Set.indicator_of_notMem hz, map_zero]

theorem model_input (a b T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    model.toContinuousLinearMap.compLpL 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) (input a b T U hU).val =
        (IBMPhysicalPredictableSteps.input a b T (lift U) (lift_past a U hU)).val := by
  apply Lp.ext
  have hu := ae_restrict_of_ae (s := PredictableRealL2.horizon T)
    ((Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (lift_ae U))
  filter_upwards [model.toContinuousLinearMap.coeFn_compLpL (input a b T U hU).val,
    input_ae a b T U hU,
    IBMPhysicalPredictableSteps.input_ae a b T (lift U) (lift_past a U hU), hu]
    with z hm hi hv hu
  simp only [Function.comp_apply] at hu
  rw [hm, hi, hv]
  by_cases hz : z.1 ∈ Set.Ioc (a : ℝ) (b : ℝ)
  · simp only [IBMPhysicalPredictableSteps.field, Set.indicator_of_mem hz, hu]
    rfl
  · simp only [IBMPhysicalPredictableSteps.field, Set.indicator_of_notMem hz, map_zero]

def product (a b : ℝ≥0) (hab : a ≤ b) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    Lp TimeHilbert 2 gaussianProduct :=
  recover.compLpL 2 gaussianProduct
    (IBMPhysicalPastIncrement.product a b hab (lift U) (lift_past a U hU))

theorem product_ae (a b : ℝ≥0) (hab : a ≤ b) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    product a b hab U hU =ᵐ[gaussianProduct] fun Y => (process b Y-process a Y) • U Y := by
  filter_upwards [recover.coeFn_compLpL
    (IBMPhysicalPastIncrement.product a b hab (lift U) (lift_past a U hU)),
    IBMPhysicalPastIncrement.product_ae a b hab (lift U) (lift_past a U hU), lift_ae U]
    with Y hr hp hu
  change product a b hab U hU Y = _ at hr
  rw [hr, hp, map_smul, hu, recover_model]

theorem integral_input (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[naturalFiltration a] U gaussianProduct) :
    integral T (input a b T U hU) = product a b hab U hU := by
  have h := model_integral T (input a b T U hU)
    (IBMPhysicalPredictableSteps.input a b T (lift U) (lift_past a U hU))
    (model_input a b T U hU)
  have hr := congrArg (recover.compLpL 2 gaussianProduct) h
  rw [recover_lift, IBMPhysicalPredictableSteps.integral_input a b T hab hbT] at hr
  exact hr

end OperatorDerivativeRewrite.Foundation.IBMSpatialPredictableSteps
