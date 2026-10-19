import Foundation.GaussianSourceClockIto
import Foundation.IBMSchwartzFullGlobalBounds
import Foundation.GaussianReflectedC2Ito
import Foundation.IBMSchwartzPhysicalPrimitiveClock
import Foundation.IBMSchwartzPhysicalSlopeClock
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open IBMConstructedSources BrownianClockWeightedEnergy IBMSchwartzSecondProjection
open IBMSchwartzSourceSecondDerivative GaussianHermiteIntegrand GaussianHermiteRepresentation
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzFullReflectedIto
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def signedSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : GaussianL2 :=
  BrownianSignIntegral.signum r • spatialSlope g a n |r|

theorem signedSlope_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    StronglyMeasurable (signedSlope g a n) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((continuous_iff_continuousAt.mpr fun r => (spatialSlope_hasDerivAt g a n r).continuousAt).stronglyMeasurable.comp_measurable
      continuous_abs.measurable)

theorem field_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (fun z => signedSlope g a n (sigma z)) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  obtain ⟨C,hC,hb⟩ := IBMSchwartzFullGlobalBounds.slope_bound g a n
  apply MemLp.of_bound ((signedSlope_measurable g a n).comp_measurable sigma_measurable).aestronglyMeasurable C
  exact Eventually.of_forall fun z => by
    change ‖signedSlope g a n (sigma z)‖ ≤ C
    rw [signedSlope,norm_smul]
    exact (mul_le_mul (BrownianSignIntegral.signum_bound _) (hb _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

def field (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp GaussianL2 2 (PredictableRealL2.horizonMeasure T gaussianProduct) :=
  (field_memLp g a n T).toLp _

theorem field_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    field g a n T =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => signedSlope g a n (sigma z) := MemLp.coeFn_toLp _

theorem field_predictable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (field g a n T) (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨signedSlope g a n ∘ b, (signedSlope_measurable g a n).comp_measurable hb.measurable, ?_⟩
  filter_upwards [field_ae g a n T,ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint T),
    ae_restrict_of_ae he,ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hf hB hb hz
  rw [hf]
  change signedSlope g a n (sigma z) = signedSlope g a n (b z)
  rw [← hb,hB,indicator_of_mem hz]

def integrand (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : GaussianSourceClockIto.Domain T :=
  ⟨field g a n T,field_predictable g a n T⟩

def integralValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  GaussianSourceClockIto.integral T (integrand g a n T)

def scalarPrimitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) : ℝ := L (IBMFullSchwartzTerminal.spatial g a n r)

theorem scalarPrimitive_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (L : GaussianL2 →L[ℝ] ℝ) :
    ContDiff ℝ 2 (scalarPrimitive g a n L) :=
  L.contDiff.comp (IBMSchwartzFullGlobalBounds.spatial_C2 g a n)

theorem scalarPrimitive_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) :
    deriv (scalarPrimitive g a n L) r = L (spatialSlope g a n r) :=
  (L.hasFDerivAt.comp_hasDerivAt r (spatial_hasDerivAt g a n r)).deriv

theorem scalarPrimitive_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) :
    deriv (deriv (scalarPrimitive g a n L)) r = L (mollifiedClass g a n r) := by
  rw [show deriv (scalarPrimitive g a n L) = fun r => L (spatialSlope g a n r) from
    funext (scalarPrimitive_deriv g a n L)]
  exact (L.hasFDerivAt.comp_hasDerivAt r (spatialSlope_hasDerivAt g a n r)).deriv

theorem scalarPrimitive_bounds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (L : GaussianL2 →L[ℝ] ℝ) :
    ∃ K0 K1 : ℝ≥0, (∀ r, ‖deriv (scalarPrimitive g a n L) r‖ ≤ (K0 : ℝ)) ∧
      (∀ r, ‖deriv (deriv (scalarPrimitive g a n L)) r‖ ≤ (K1 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := IBMSchwartzFullGlobalBounds.slope_bound g a n
  obtain ⟨D,hD,hd⟩ := IBMSchwartzFullGlobalBounds.curvature_bound g a n
  refine ⟨⟨‖L‖*C,by positivity⟩,⟨‖L‖*D,by positivity⟩,?_,?_⟩
  · intro r
    rw [scalarPrimitive_deriv]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _))
  · intro r
    rw [scalarPrimitive_second_deriv]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hd r) (norm_nonneg _))

theorem integral_test (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) (K1 : ℝ≥0)
    (h1 : ∀ r, ‖deriv (deriv (scalarPrimitive g a n L)) r‖ ≤ (K1 : ℝ)) :
    L.compLpL 2 gaussianProduct (integralValue g a n T) =
      itoIntegral (GaussianReflectedC2Ito.running (scalarPrimitive g a n L)
        (scalarPrimitive_C2 g a n L) K1 h1 T) := by
  apply GaussianSourceClockIto.scalarization_full
  have he : (fun z => L ((integrand g a n T).val z)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z)*deriv (scalarPrimitive g a n L) |sigma z| := by
    filter_upwards [field_ae g a n T] with z hz
    change L (field g a n T z) = _
    rw [hz,signedSlope,map_smul,scalarPrimitive_deriv]
    rfl
  exact (GaussianReflectedC2Ito.running_coeFn (scalarPrimitive g a n L)
    (scalarPrimitive_C2 g a n L) K1 h1 T).trans
      ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).symm

theorem tested_reflected_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) :
    ∀ᵐ ω ∂gaussianProduct,
      L (IBMFullSchwartzTerminal.spatial g a n |clockPath ω T|-IBMFullSchwartzTerminal.spatial g a n 0) =
        L (integralValue g a n T ω)+L (IBMSchwartzTimeProjection.wholeCorrection g a n T ω) := by
  obtain ⟨K0,K1,h0,h1⟩ := scalarPrimitive_bounds g a n L
  let f := scalarPrimitive g a n L
  let hf := scalarPrimitive_C2 g a n L
  have hi := GaussianReflectedC2Ito.reflected_ito_pathwise f hf K1 h1 K0 h0 T
  have hs := L.coeFn_compLpL (integralValue g a n T)
  rw [integral_test g a n T L K1 h1] at hs
  have hm : BrownianMassLimitIdentification.coordinateClass T =ᵐ[gaussianProduct]
      fun ω => BrownianMassContinuousLimit.limitPath ω T := MemLp.coeFn_toLp _
  filter_upwards [hi,hs,hm] with ω hi hs hm
  have hk : IntervalIntegrable (fun s : ℝ => mollifiedClass g a n |clockPath ω s.toNNReal|)
      volume 0 T := (IBMSchwartzTimeProjection.mollified_path_continuous g a n ω).intervalIntegrable 0 T
  have hd := L.intervalIntegral_comp_comm (μ := volume) hk
  simp only [f,scalarPrimitive_deriv,scalarPrimitive_second_deriv] at hi
  rw [hs] at hi
  rw [map_sub,IBMSchwartzTimeProjection.wholeCorrection,map_add,map_smul,map_smul,← hd,hm]
  change L (IBMFullSchwartzTerminal.spatial g a n |clockPath ω T|)-L (IBMFullSchwartzTerminal.spatial g a n 0) =
    L (integralValue g a n T ω)+
      (BrownianMassContinuousLimit.limitPath ω T • L (spatialSlope g a n 0)+
        (1/2 : ℝ) • ∫ s in 0..(T : ℝ), L (mollifiedClass g a n |clockPath ω s.toNNReal|))
  simp only [scalarPrimitive,smul_eq_mul] at hi ⊢
  linear_combination hi

theorem reflected_identity_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (fun ω => IBMFullSchwartzTerminal.spatial g a n |clockPath ω T|-IBMFullSchwartzTerminal.spatial g a n 0)
      =ᵐ[gaussianProduct] fun ω => integralValue g a n T ω+IBMSchwartzTimeProjection.wholeCorrection g a n T ω := by
  have hz : (fun ω => IBMFullSchwartzTerminal.spatial g a n |clockPath ω T|-IBMFullSchwartzTerminal.spatial g a n 0-
      (integralValue g a n T ω+IBMSchwartzTimeProjection.wholeCorrection g a n T ω)) =ᵐ[gaussianProduct] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [tested_reflected_identity g a n T L] with ω hω
    simpa only [map_sub,map_add,Pi.zero_apply,sub_eq_zero] using hω
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

def endpointClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  IBMSchwartzPhysicalPrimitiveClock.endpoint g a n T-Lp.const 2 gaussianProduct (IBMFullSchwartzTerminal.spatial g a n 0)

theorem endpointClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpointClass g a n T =ᵐ[gaussianProduct]
      fun ω => IBMFullSchwartzTerminal.spatial g a n |clockPath ω T|-IBMFullSchwartzTerminal.spatial g a n 0 := by
  filter_upwards [Lp.coeFn_sub (IBMSchwartzPhysicalPrimitiveClock.endpoint g a n T)
    (Lp.const 2 gaussianProduct (IBMFullSchwartzTerminal.spatial g a n 0)),
    IBMSchwartzPhysicalPrimitiveClock.endpoint_ae g a n T,Lp.coeFn_const (p := 2) (μ := gaussianProduct)
      (c := IBMFullSchwartzTerminal.spatial g a n 0)] with ω hs he hc
  change endpointClass g a n T ω = _ at hs
  rw [hs]
  simp only [Pi.sub_apply,he,hc,Function.const_apply]

theorem finite_mollifier_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpointClass g a n T = integralValue g a n T+IBMSchwartzBochnerDomain.wholeClass g a n T := by
  apply Lp.ext
  filter_upwards [endpointClass_ae g a n T,IBMSchwartzBochnerDomain.wholeClass_coeFn g a n T,
    reflected_identity_ae g a n T,Lp.coeFn_add (integralValue g a n T)
      (IBMSchwartzBochnerDomain.wholeClass g a n T)] with ω he hw hi ha
  rw [he,ha]
  simp only [Pi.add_apply,hw]
  exact hi

def endpointLimitClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T-
    Lp.const 2 gaussianProduct (IBMFullSchwartzTerminal.spatialLimit g a 0)

theorem endpointClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => endpointClass g a n T) atTop (𝓝 (endpointLimitClass g a T)) :=
  (IBMSchwartzPhysicalPrimitiveClock.endpoint_tendsto g a T).sub
    ((Lp.constL 2 gaussianProduct ℝ).continuous.tendsto _ |>.comp (IBMFullSchwartzTerminal.spatial_tendsto g a 0))

/-- In native joint source/clock L2, no singular correction limit is gained
without the genuine stochastic-integrand Cauchy condition. -/
theorem whole_cauchy_iff_integrand (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    CauchySeq (fun n => IBMSchwartzBochnerDomain.wholeClass g a n T) ↔
      CauchySeq (fun n => integrand g a n T) := by
  have hI : CauchySeq (fun n => integralValue g a n T) ↔ CauchySeq (fun n => integrand g a n T) := by
    simp only [Metric.cauchySeq_iff,integralValue,(GaussianSourceClockIto.integral T).isometry.dist_eq]
  constructor
  · intro hC
    apply hI.mp
    obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hC
    have h := ((endpointClass_tendsto g a T).sub hc).cauchySeq
    simpa only [finite_mollifier_identity,add_sub_cancel_right] using h
  · intro hU
    obtain ⟨i,hi⟩ := cauchySeq_tendsto_of_complete (hI.mpr hU)
    have h := ((endpointClass_tendsto g a T).sub hi).cauchySeq
    simpa only [finite_mollifier_identity,add_sub_cancel_left] using h

/-- Every source sector is identified against the actual Brownian integral;
no clock projection, source truncation or summability assumption is inserted. -/
theorem source_projection_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    (GaussianNumberSectors.projection k).compLpL 2 gaussianProduct (endpointClass g a n T) =
      GaussianSourceClockIto.integral T (GaussianSourceClockIto.mapField T
        (GaussianNumberSectors.projection k) (integrand g a n T))+
      (GaussianNumberSectors.projection k).compLpL 2 gaussianProduct
        (IBMSchwartzBochnerDomain.wholeClass g a n T) := by
  rw [finite_mollifier_identity,map_add]
  congr 1
  exact GaussianSourceClockIto.integral_mapField T (GaussianNumberSectors.projection k) (integrand g a n T)

theorem source_integrand_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    (GaussianSourceClockIto.mapField T (GaussianNumberSectors.projection k) (integrand g a n T)).val =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z) •
        GaussianNumberSectors.projection k (spatialSlope g a n |sigma z|) := by
  filter_upwards [GaussianSourceClockIto.mapField_ae T (GaussianNumberSectors.projection k)
    (integrand g a n T),field_ae g a n T] with z hm hf
  change _ = GaussianNumberSectors.projection k (field g a n T z) at hm
  rw [hm,hf,signedSlope,map_smul]

theorem spatialLimit_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    IBMFullSchwartzTerminal.spatialLimit g a 0 = g a • gaussianOne := by
  have hz : IBMQuarticPrimitiveLimit.baseCoefficient 0 = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp (by simpa only [abs_zero] using IBMPhysicalNoiseRealization.base_norm_sq 0)
  simp only [IBMFullSchwartzTerminal.spatialLimit,IBMSchwartzSourceDerivative.observable,hz,
    IBMScalarSecondProjection.testClass_zero,IBMCorrectionStein.shiftedJet,IBMCorrectionStein.jet,add_zero]

theorem spatialLimit_zero_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    IBMFullSchwartzTerminal.spatialLimit g a 0 =ᵐ[gaussianProduct] fun _ => g a := by
  rw [spatialLimit_zero]
  filter_upwards [Lp.coeFn_smul (g a) gaussianOne,gaussianOne_coeFn] with ω hs h1
  simp only [hs,Pi.smul_apply,smul_eq_mul,h1,mul_one]

theorem endpointLimitClass_actual_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, endpointLimitClass g a T ωY =ᵐ[gaussianProduct]
      fun ωX => g (a+ibmValue T (ωX,ωY))-g a := by
  filter_upwards [Lp.coeFn_sub (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T)
    (Lp.const 2 gaussianProduct (IBMFullSchwartzTerminal.spatialLimit g a 0)),
    IBMSchwartzPhysicalPrimitiveClock.endpointLimit_actual_sections g a T,
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := IBMFullSchwartzTerminal.spatialLimit g a 0)]
      with ωY hs he hc
  change endpointLimitClass g a T ωY = _ at hs
  rw [hs]
  simp only [Pi.sub_apply,hc,Function.const_apply]
  filter_upwards [Lp.coeFn_sub (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T ωY)
    (IBMFullSchwartzTerminal.spatialLimit g a 0),he,spatialLimit_zero_ae g a] with ωX hd he h0
  simp only [hd,Pi.sub_apply,he,h0]

/-- Concrete reuse of the existing explicit second-source slope kernel. -/
theorem source_two_integrand_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (GaussianSourceClockIto.mapField T (GaussianNumberSectors.projection 2) (integrand g a n T)).val =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z) •
        IBMSchwartzSpatialPrimitive.spatialSlope g a n |sigma z| := by
  filter_upwards [source_integrand_ae g a n T 2] with z hz
  rw [hz]
  congr 1
  exact (IBMSchwartzSpatialPrimitive.spatialSlope_eq_origin_projection g a n |sigma z|).symm
end OperatorDerivativeRewrite.Foundation.IBMSchwartzFullReflectedIto
