import Foundation.GaussianSourceHorizonRegularization
import Foundation.IBMRegularizedStochasticIdentity

/-! Actual time sections of native source-valued predictable fields.
All sections come from the original product L2 equivalence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableSourceSlices
open InfiniteGaussian GaussianTimeProductL2 GaussianProductDerivative
open GaussianClockValueOperators GaussianSourceClockIto GaussianSourceHorizonRegularization
open GaussianComplexHorizonIto GaussianHorizonChaosIntertwining
open GaussianPredictableHorizon GaussianFiniteHorizonAdjoint GaussianPredictableFull
open GaussianRoughFiniteHorizon GaussianPredictableCutoff GaussianItoChaosIntertwining
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev Ambient := Lp GaussianL2 2 timeProbability

def sourceCurry : Ambient ≃ₗᵢ[ℝ] Lp Field 2 (volume : Measure ℝ) :=
  ProductL2Curry.curryEquiv volume gaussianProduct

def zeroValue (T : ℝ≥0) (u : Domain T) : Ambient :=
  ((memLp_indicator_iff_restrict (PredictableRealL2.horizon_measurable T)).mpr
    (Lp.memLp u.val)).toLp _

theorem zeroValue_ae (T : ℝ≥0) (u : Domain T) :
    zeroValue T u =ᵐ[timeProbability] (PredictableRealL2.horizon T).indicator u.val :=
  MemLp.coeFn_toLp _

def zeroExtend (T : ℝ≥0) : Domain T →ₗᵢ[ℝ] Ambient where
  toFun := zeroValue T
  map_add' u v := by
    apply Lp.ext
    have ht := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
      (Lp.coeFn_add u.val v.val)
    filter_upwards [zeroValue_ae T (u+v),zeroValue_ae T u,zeroValue_ae T v,
      Lp.coeFn_add (zeroValue T u) (zeroValue T v),ht] with z hz hu hv hadd ht
    rw [hz,hadd]
    simp only [Pi.add_apply]
    rw [hu,hv]
    change (PredictableRealL2.horizon T).indicator (u.val+v.val) z = _
    rw [ht]
    by_cases hz : z ∈ PredictableRealL2.horizon T <;> simp [hz]
  map_smul' c u := by
    apply Lp.ext
    have ht := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
      (Lp.coeFn_smul c u.val)
    filter_upwards [zeroValue_ae T (c • u),zeroValue_ae T u,
      Lp.coeFn_smul c (zeroValue T u),ht] with z hz hu hsm ht
    change zeroValue T (c • u) z = (c • zeroValue T u) z
    rw [hz,hsm]
    simp only [Pi.smul_apply]
    rw [hu]
    change (PredictableRealL2.horizon T).indicator (c • u.val) z = _
    rw [ht]
    by_cases hz : z ∈ PredictableRealL2.horizon T <;> simp [hz]
  norm_map' u := by
    change ‖zeroValue T u‖ = ‖u.val‖
    rw [zeroValue,Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict
      (PredictableRealL2.horizon_measurable T),Lp.norm_def]

def testedNative (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) (u : Domain T) : PredictableDomain T :=
  (GaussianComplexHorizonIto.trimEquiv T).symm
    (L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T u))

theorem testedNative_ae (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) (u : Domain T) :
    (testedNative T L u).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => L (u.val z) := by
  let a := L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T u)
  have hs := lpTrimToLpMeas_ae_eq (𝕜 := ℝ)
    (PredictableRealL2.predictable_le GaussianTimeProcess.naturalFiltration) a
  have hc := ae_eq_of_ae_eq_trim (L.coeFn_compLpL (GaussianSourceClockIto.trimEquiv T u))
  have hu := lpMeasToLpTrim_ae_eq (𝕜 := ℝ)
    (PredictableRealL2.predictable_le GaussianTimeProcess.naturalFiltration) u
  filter_upwards [hs,hc,hu] with z hs hc hu
  change (testedNative T L u).val z = a z at hs
  change a z = L (GaussianSourceClockIto.trimEquiv T u z) at hc
  change GaussianSourceClockIto.trimEquiv T u z = u.val z at hu
  rw [hs,hc,hu]

theorem zeroExtend_test (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) (u : Domain T) :
    L.compLpL 2 timeProbability (zeroExtend T u) =
      (extendPredictable T (testedNative T L u) : TimeProbabilityL2) := by
  apply Lp.ext
  have ht := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (testedNative_ae T L u)
  filter_upwards [L.coeFn_compLpL (zeroExtend T u),
    zeroValue_ae T u,
    L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) (testedNative T L u).val,ht]
    with z hL hu hv ht
  change zeroExtend T u z = _ at hu
  change (extendPredictable T (testedNative T L u) : TimeProbabilityL2) z = _ at hv
  rw [hL,hu,hv,ht]
  by_cases hz : z ∈ PredictableRealL2.horizon T <;> simp [hz]

/-- Continuous source tests commute with ACTUAL product-L2 time sections. -/
theorem sourceCurry_test (L : GaussianL2 →L[ℝ] ℝ) (u : Ambient) :
    (L.compLpL 2 gaussianProduct).compLpL 2 volume (sourceCurry u) =
      scalarCurry (L.compLpL 2 timeProbability u) := by
  apply Lp.ext
  filter_upwards [(L.compLpL 2 gaussianProduct).coeFn_compLpL (sourceCurry u),
    ProductL2Curry.curryEquiv_coeFn volume gaussianProduct u,
    ProductL2Curry.curryEquiv_coeFn volume gaussianProduct (L.compLpL 2 timeProbability u),
    Measure.ae_ae_of_ae_prod (L.coeFn_compLpL u)] with t hL hu hv ht
  change sourceCurry u t =ᵐ[gaussianProduct] fun ω => u (t,ω) at hu
  change scalarCurry (L.compLpL 2 timeProbability u) t =ᵐ[gaussianProduct]
    fun ω => L.compLpL 2 timeProbability u (t,ω) at hv
  rw [hL]
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (sourceCurry u t),hu,hv,ht] with ω hL hu hv ht
  rw [hL,hu,hv,ht]

def timeLift (A : GaussianL2 →L[ℝ] GaussianL2) : Ambient →L[ℝ] Ambient :=
  sourceCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    (((clockLift A).compLpL 2 volume).comp sourceCurry.toLinearIsometry.toContinuousLinearMap)

theorem timeLift_curry (A : GaussianL2 →L[ℝ] GaussianL2) (u : Ambient) :
    sourceCurry (timeLift A u) = (clockLift A).compLpL 2 volume (sourceCurry u) :=
  sourceCurry.apply_symm_apply _

set_option maxHeartbeats 1000000 in
theorem timeLift_test (A : GaussianL2 →L[ℝ] GaussianL2) (L : GaussianL2 →L[ℝ] ℝ) (u : Ambient) :
    L.compLpL 2 timeProbability (timeLift A u) =
      GaussianPredictableChaosCore.scalarLift A (L.compLpL 2 timeProbability u) := by
  apply scalarCurry.injective
  have hc (f : TimeProbabilityL2) : scalarCurry (GaussianPredictableChaosCore.scalarLift A f) =
      A.compLpL 2 volume (scalarCurry f) := scalarCurry.apply_symm_apply _
  rw [hc]
  rw [← sourceCurry_test L (timeLift A u),timeLift_curry]
  conv_rhs => rw [← sourceCurry_test L u]
  apply Lp.ext
  filter_upwards [(L.compLpL 2 gaussianProduct).coeFn_compLpL
      ((clockLift A).compLpL 2 volume (sourceCurry u)),
    (clockLift A).coeFn_compLpL (sourceCurry u),
    A.coeFn_compLpL ((L.compLpL 2 gaussianProduct).compLpL 2 volume (sourceCurry u)),
    (L.compLpL 2 gaussianProduct).coeFn_compLpL (sourceCurry u)] with t hL hA ha hl
  rw [hL,hA,ha,hl]
  exact clockLift_test A L (sourceCurry u t)

theorem ambient_eq_of_tests {u v : Ambient}
    (h : ∀ L : GaussianL2 →L[ℝ] ℝ, L.compLpL 2 timeProbability u = L.compLpL 2 timeProbability v) :
    u = v := by
  have hz : (fun z => u z - v z) =ᵐ[timeProbability] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [L.coeFn_compLpL u,L.coeFn_compLpL v] with z hu hv
    change L (u z - v z) = 0
    rw [map_sub,← hu,← hv,h L,sub_self]
  apply Lp.ext
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp hz

theorem testedNative_sourceProjection (k : ℕ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ)
    (u : Domain T) :
    testedNative T L (sourceProjection k T u) = horizonProjection k T (testedNative T L u) := by
  apply (GaussianComplexHorizonIto.trimEquiv T).injective
  change GaussianComplexHorizonIto.trimEquiv T ((GaussianComplexHorizonIto.trimEquiv T).symm
    (L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T (sourceProjection k T u)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change L.compLpL 2 (predictableMeasure T)
    (GaussianSourceClockIto.trimEquiv T (mapPredictable T (realProjection k T) u)) =
      realProjection k T (L.compLpL 2 (predictableMeasure T) (GaussianSourceClockIto.trimEquiv T u))
  exact mapPredictable_test T _ L u

theorem extend_restrict (T : ℝ≥0) (u : fullPredictable) :
    extendPredictable T (restrictPredictable T u) = predictableCut T u := by
  apply Subtype.ext
  change L2ZeroExtension (PredictableRealL2.horizon_measurable T)
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (PredictableRealL2.horizon T) u) = cut T u
  rfl

theorem extend_horizonProjection (k : ℕ) (T : ℝ≥0) (u : PredictableDomain T) :
    extendPredictable T (horizonProjection k T u) = projectedPredictable k (extendPredictable T u) := by
  rw [horizonProjection_eq,extend_restrict,projected_extended_supported]

/-- The SOURCE-valued predictable projector is genuinely the CLOCK
probability projection acting on the original time sections. -/
theorem zeroExtend_sourceProjection (k : ℕ) (T : ℝ≥0) (u : Domain T) :
    zeroExtend T (sourceProjection k T u) = timeLift (GaussianNumberSectors.projection k) (zeroExtend T u) := by
  apply ambient_eq_of_tests
  intro L
  rw [zeroExtend_test,timeLift_test,zeroExtend_test,testedNative_sourceProjection,
    extend_horizonProjection]
  rfl

theorem sourceProjection_curry (k : ℕ) (T : ℝ≥0) (u : Domain T) :
    sourceCurry (zeroExtend T (sourceProjection k T u)) =
      (clockLift (GaussianNumberSectors.projection k)).compLpL 2 volume (sourceCurry (zeroExtend T u)) := by
  exact (congrArg sourceCurry (zeroExtend_sourceProjection k T u)).trans
    (timeLift_curry (GaussianNumberSectors.projection k) (zeroExtend T u))

theorem sourceProjection_slices (k : ℕ) (T : ℝ≥0) (u : Domain T) :
    sourceCurry (zeroExtend T (sourceProjection k T u)) =ᵐ[volume]
      fun t => clockLift (GaussianNumberSectors.projection k) (sourceCurry (zeroExtend T u) t) := by
  rw [sourceProjection_curry]
  exact (clockLift (GaussianNumberSectors.projection k)).coeFn_compLpL _

set_option maxHeartbeats 1000000 in
theorem finite_regularization_slices (N : ℕ) (T : ℝ≥0) (u : Domain T) :
    sourceCurry (zeroExtend T (∑ k ∈ Finset.range (N + 1),
      (k + 1 : ℝ)⁻¹ • sourceProjection k T u)) =ᵐ[volume] fun t =>
        ∑ k ∈ Finset.range (N + 1), (k + 1 : ℝ)⁻¹ •
          clockLift (GaussianNumberSectors.projection k) (sourceCurry (zeroExtend T u) t) := by
  have he : sourceCurry (zeroExtend T (∑ k ∈ Finset.range (N + 1),
      (k + 1 : ℝ)⁻¹ • sourceProjection k T u)) =
      ∑ k ∈ Finset.range (N + 1), (k + 1 : ℝ)⁻¹ •
        sourceCurry (zeroExtend T (sourceProjection k T u)) := by
    simp only [map_sum,map_smul]
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (N + 1)) (fun k =>
      (k + 1 : ℝ)⁻¹ • sourceCurry (zeroExtend T (sourceProjection k T u))),
    ae_all_iff.mpr (fun k : ℕ => Lp.coeFn_smul (k + 1 : ℝ)⁻¹
      (sourceCurry (zeroExtend T (sourceProjection k T u)))),
    ae_all_iff.mpr (fun k : ℕ => sourceProjection_slices k T u)] with t hsum hsm hp
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hsm k,Pi.smul_apply,hp k]

/-- The actual predictable regularization realizes any verified strong
clock-slice limit, without assuming measurability of that proposed limit. -/
theorem regularization_slices_of_clock_limit (T : ℝ≥0) (u : Domain T) (q : ℝ → Field)
    (hq : ∀ᵐ t ∂volume, Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      (k + 1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k)
        (sourceCurry (zeroExtend T u) t)) atTop (𝓝 (q t))) :
    sourceCurry (zeroExtend T (sourceRegularization T u)) =ᵐ[volume] q := by
  have hs := ((sourceCurry.toLinearIsometry.comp (zeroExtend T)).continuous.tendsto
    (sourceRegularization T u)).comp (sourceRegularization_chaos_tendsto T u)
  obtain ⟨ns,hns,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr (fun N => finite_regularization_slices N T u)
  filter_upwards [hAE,hall,hq] with t ht hall hqt
  change Tendsto (fun j => sourceCurry (zeroExtend T
    (∑ k ∈ Finset.range (ns j + 1), (k + 1 : ℝ)⁻¹ • sourceProjection k T u)) t)
      atTop (𝓝 (sourceCurry (zeroExtend T (sourceRegularization T u)) t)) at ht
  apply tendsto_nhds_unique ?_ (hqt.comp hns.tendsto_atTop)
  simpa only [hall,Function.comp_def] using ht

end OperatorDerivativeRewrite.Foundation.GaussianPredictableSourceSlices
