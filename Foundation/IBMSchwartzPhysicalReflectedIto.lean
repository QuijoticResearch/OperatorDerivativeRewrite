import Foundation.IBMPhysicalClockItoScalar
import Foundation.GaussianReflectedC2Ito
import Foundation.IBMSchwartzPhysicalGlobalBounds
import Foundation.IBMSchwartzPhysicalClockIntegral
import Foundation.IBMSchwartzPhysicalPrimitiveClock
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BesselPotentialSpace
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open GaussianComplexHorizonIto IBMPhysicalClockIto
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalReflectedIto
local instance : NormedSpace ℝ H^{(-1 : ℝ)}(ℝ) := NormedSpace.restrictScalars ℝ ℂ _
theorem scalarization_full (T : ℝ≥0) (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ)
    (u : Domain T) (v : fullPredictable)
    (hv : (v : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => L (u.val z))) :
    L.compLpL 2 gaussianProduct (IBMPhysicalClockIto.integral T u) = itoIntegral v := by
  let a := L.compLpL 2 (predictableMeasure T) (IBMPhysicalClockIto.trimEquiv T u)
  let S := (GaussianComplexHorizonIto.trimEquiv T).symm a
  have he : (S : Lp ℝ 2 (PredictableRealL2.horizonMeasure T gaussianProduct)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct] fun z => L (u.val z) := by
    have hs := lpTrimToLpMeas_ae_eq (𝕜 := ℝ) (PredictableRealL2.predictable_le naturalFiltration) a
    have hc := ae_eq_of_ae_eq_trim (L.coeFn_compLpL (IBMPhysicalClockIto.trimEquiv T u))
    have hu := lpMeasToLpTrim_ae_eq (𝕜 := ℂ) (PredictableRealL2.predictable_le naturalFiltration) u
    filter_upwards [hs,hc,hu] with z hs hc hu
    change S.val z = a z at hs
    change a z = L (IBMPhysicalClockIto.trimEquiv T u z) at hc
    change IBMPhysicalClockIto.trimEquiv T u z = u.val z at hu
    rw [hs,hc,hu]
  have hzero : L2ZeroExtension (PredictableRealL2.horizon_measurable T) S.val = v.val := by
    apply Lp.ext
    exact (L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) S.val).trans
      (((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).trans hv.symm)
  rw [IBMPhysicalClockItoScalar.native_scalarization]
  change GaussianPredictableHorizon.itoIntegral T S = itoIntegral v
  change GaussianPredictableL2Completion.productIntegral (GaussianPredictableHorizon.horizonEmbedding T S) =
    GaussianPredictableL2Completion.productIntegral (domainEquiv v)
  congr 1
  apply Subtype.ext
  exact hzero

open GaussianTimeHilbert IBMSchwartzPhysicalPrimitive IBMSchwartzPhysicalFirstKernel
open IBMPhysicalNegativeEmbedding IBMConstructedSources BrownianClockWeightedEnergy

def testMap (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) : TimeHilbert →L[ℝ] ℝ := L.comp embedding

def scalarPrimitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) (r : ℝ) : ℝ := testMap L (primitive g a n r)

theorem scalarPrimitive_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) : ContDiff ℝ 2 (scalarPrimitive g a n L) :=
  (testMap L).contDiff.comp (primitive_C2 g a n)

theorem scalarPrimitive_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) (r : ℝ) :
    deriv (scalarPrimitive g a n L) r = testMap L (slope g a n r) :=
  ((testMap L).hasFDerivAt.comp_hasDerivAt r (primitive_hasDerivAt g a n r)).deriv

theorem scalarPrimitive_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) (r : ℝ) :
    deriv (deriv (scalarPrimitive g a n L)) r = testMap L (curvatureKernel g a n r) := by
  rw [show deriv (scalarPrimitive g a n L) = fun r => testMap L (slope g a n r) from
    funext (scalarPrimitive_deriv g a n L)]
  exact ((testMap L).hasFDerivAt.comp_hasDerivAt r (slope_hasDerivAt g a n r)).deriv

theorem scalarPrimitive_bounds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) : ∃ K0 K1 : ℝ≥0,
      (∀ r, ‖deriv (scalarPrimitive g a n L) r‖ ≤ (K0 : ℝ)) ∧
      (∀ r, ‖deriv (deriv (scalarPrimitive g a n L)) r‖ ≤ (K1 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := IBMSchwartzPhysicalGlobalBounds.slope_global_bound g a n
  obtain ⟨D,hD,hd⟩ := IBMSchwartzPhysicalGlobalBounds.curvature_global_bound g a n
  refine ⟨⟨‖testMap L‖*C,by positivity⟩,⟨‖testMap L‖*D,by positivity⟩,?_,?_⟩
  · intro r
    rw [scalarPrimitive_deriv]
    exact ((testMap L).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _))
  · intro r
    rw [scalarPrimitive_second_deriv]
    exact ((testMap L).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hd r) (norm_nonneg _))

theorem native_integrand_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (IBMSchwartzPhysicalClockIntegral.integrand g a n T).val =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z) • embedding (slope g a n |sigma z|) := by
  have he := LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T)
    (IBMSchwartzPhysicalSlopeClock.field g a n T)
  filter_upwards [he, ae_restrict_of_ae (IBMSchwartzPhysicalSlopeClock.field_ae g a n T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z he hf hz
  change (IBMSchwartzPhysicalClockIntegral.integrand g a n T).val z = _ at he
  rw [he,hf,indicator_of_mem hz]
  rfl

theorem integral_test (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) (K1 : ℝ≥0)
    (h1 : ∀ r, ‖deriv (deriv (scalarPrimitive g a n L)) r‖ ≤ (K1 : ℝ)) :
    L.compLpL 2 gaussianProduct (IBMSchwartzPhysicalClockIntegral.integralValue g a n T) =
      itoIntegral (GaussianReflectedC2Ito.running (scalarPrimitive g a n L)
        (scalarPrimitive_C2 g a n L) K1 h1 T) := by
  apply scalarization_full
  have he : (fun z => L ((IBMSchwartzPhysicalClockIntegral.integrand g a n T).val z)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z)*deriv (scalarPrimitive g a n L) |sigma z| := by
    filter_upwards [native_integrand_ae g a n T] with z hz
    rw [hz,map_smul,scalarPrimitive_deriv]
    rfl
  exact (GaussianReflectedC2Ito.running_coeFn (scalarPrimitive g a n L)
    (scalarPrimitive_C2 g a n L) K1 h1 T).trans
      ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).symm

theorem tested_reflected_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) :
    ∀ᵐ ω ∂gaussianProduct,
      testMap L (primitive g a n |clockPath ω T|-primitive g a n 0) =
        L (IBMSchwartzPhysicalClockIntegral.integralValue g a n T ω)+
          testMap L (wholeKernel g a n T ω) := by
  obtain ⟨K0,K1,h0,h1⟩ := scalarPrimitive_bounds g a n L
  let f := scalarPrimitive g a n L
  let hf := scalarPrimitive_C2 g a n L
  have hi := GaussianReflectedC2Ito.reflected_ito_pathwise f hf K1 h1 K0 h0 T
  have hs := L.coeFn_compLpL (IBMSchwartzPhysicalClockIntegral.integralValue g a n T)
  rw [integral_test g a n T L K1 h1] at hs
  have hm : BrownianMassLimitIdentification.coordinateClass T =ᵐ[gaussianProduct]
      fun ω => BrownianMassContinuousLimit.limitPath ω T := MemLp.coeFn_toLp _
  filter_upwards [hi,hs,hm] with ω hi hs hm
  have hk : IntervalIntegrable (fun s : ℝ => curvatureKernel g a n
      |clockPath ω s.toNNReal|) volume 0 T :=
    ((curvatureKernel_continuous g a n).comp (continuous_abs.comp
      ((clockPath ω).continuous.comp continuous_real_toNNReal))).intervalIntegrable 0 T
  have hd := (testMap L).intervalIntegral_comp_comm (μ := volume) hk
  simp only [f,scalarPrimitive_deriv,scalarPrimitive_second_deriv] at hi
  rw [hs] at hi
  rw [map_sub,wholeKernel,map_add,map_smul,map_smul,← hd,hm,← slope_origin]
  simp only [scalarPrimitive,smul_eq_mul] at hi ⊢
  linear_combination hi

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : SecondCountableTopology H^{(-1 : ℝ)}(ℝ) :=
  (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).isometry.isEmbedding.secondCountableTopology

theorem reflected_identity_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    (fun ω => embedding (primitive g a n |clockPath ω T|-primitive g a n 0)) =ᵐ[gaussianProduct]
      fun ω => IBMSchwartzPhysicalClockIntegral.integralValue g a n T ω+
        embedding (wholeKernel g a n T ω) := by
  have hz : (fun ω => embedding (primitive g a n |clockPath ω T|-primitive g a n 0)-
      (IBMSchwartzPhysicalClockIntegral.integralValue g a n T ω+
        embedding (wholeKernel g a n T ω))) =ᵐ[gaussianProduct] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [tested_reflected_identity g a n T L] with ω hω
    change L (embedding (primitive g a n |clockPath ω T|-primitive g a n 0)) =
      L (IBMSchwartzPhysicalClockIntegral.integralValue g a n T ω)+L (embedding (wholeKernel g a n T ω)) at hω
    simpa only [map_sub,map_add,Pi.zero_apply,sub_eq_zero] using hω
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

def endpointClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  embedding.compLpL 2 gaussianProduct (IBMSchwartzPhysicalPrimitiveClock.primitiveClass g a n T-
    Lp.const 2 gaussianProduct (primitive g a n 0))

def endpointLimitClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  embedding.compLpL 2 gaussianProduct (IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass g a T-
    Lp.const 2 gaussianProduct (primitiveLimit g a 0))

def wholeClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  embedding.compLpL 2 gaussianProduct (wholeKernelClass g a n T)

theorem endpointClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpointClass g a n T =ᵐ[gaussianProduct]
      fun ω => embedding (primitive g a n |clockPath ω T|-primitive g a n 0) := by
  filter_upwards [embedding.coeFn_compLpL
      (IBMSchwartzPhysicalPrimitiveClock.primitiveClass g a n T-Lp.const 2 gaussianProduct (primitive g a n 0)),
    Lp.coeFn_sub (IBMSchwartzPhysicalPrimitiveClock.primitiveClass g a n T)
      (Lp.const 2 gaussianProduct (primitive g a n 0)),
    IBMSchwartzPhysicalPrimitiveClock.primitiveClass_ae g a n T,
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := primitive g a n 0)] with ω he hs hp hc
  change endpointClass g a n T ω = _ at he
  rw [he,hs]
  simp only [Pi.sub_apply,hp,hc,Function.const_apply]

theorem wholeClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    wholeClass g a n T =ᵐ[gaussianProduct] fun ω => embedding (wholeKernel g a n T ω) := by
  filter_upwards [embedding.coeFn_compLpL (wholeKernelClass g a n T),wholeKernelClass_ae g a n T]
    with ω he hw
  change wholeClass g a n T ω = _ at he
  rw [he,hw]

/-- The actual native stochastic integral, not a residual definition. -/
theorem finite_mollifier_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpointClass g a n T = IBMSchwartzPhysicalClockIntegral.integralValue g a n T+wholeClass g a n T := by
  apply Lp.ext
  filter_upwards [endpointClass_ae g a n T,wholeClass_ae g a n T,
    reflected_identity_ae g a n T,Lp.coeFn_add
      (IBMSchwartzPhysicalClockIntegral.integralValue g a n T) (wholeClass g a n T)] with ω he hw hi ha
  rw [he,ha]
  simp only [Pi.add_apply,hw]
  exact hi

theorem endpointClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => endpointClass g a n T) atTop (𝓝 (endpointLimitClass g a T)) :=
  (embedding.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp
    ((IBMSchwartzPhysicalPrimitiveClock.primitiveClass_tendsto g a T).sub
      ((Lp.constL 2 gaussianProduct ℝ).continuous.tendsto _ |>.comp (primitive_tendsto g a 0)))

/-- Strong clock-L2(H^-1) limit of the actual ENTIRE first-source correction,
including the origin layer and every clock chaos degree. -/
theorem wholeClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => wholeClass g a n T) atTop
      (𝓝 (endpointLimitClass g a T-IBMSchwartzPhysicalClockIntegral.limitIntegralValue g a T)) := by
  have he (n : ℕ) : wholeClass g a n T = endpointClass g a n T-
      IBMSchwartzPhysicalClockIntegral.integralValue g a n T := by
    rw [finite_mollifier_identity]
    abel
  simp only [he]
  exact (endpointClass_tendsto g a T).sub (IBMSchwartzPhysicalClockIntegral.integralValue_tendsto g a T)

theorem primitiveLimit_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) : primitiveLimit g a 0 = 0 := by
  rw [primitiveLimit_eq,IBMPhysicalNoiseVectors.vector_zero,smul_zero]

theorem endpointLimitClass_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    endpointLimitClass g a T =
      embedding.compLpL 2 gaussianProduct (IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass g a T) := by
  have h0 : Lp.const 2 gaussianProduct (0 : TimeHilbert) = 0 :=
    (Lp.constₗ 2 gaussianProduct ℝ).map_zero
  simp only [endpointLimitClass,primitiveLimit_zero,h0,sub_zero]

theorem endpointLimitClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    endpointLimitClass g a T =ᵐ[gaussianProduct]
      fun ω => embedding (primitiveLimit g a |clockPath ω T|) := by
  rw [endpointLimitClass_eq]
  filter_upwards [embedding.coeFn_compLpL (IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass g a T),
    IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass_ae g a T] with ω he hp
  rw [he,hp]

/-- The origin subtraction disappears only AFTER the verified singular limit. -/
theorem wholeClass_tendsto_uncentered (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => wholeClass g a n T) atTop
      (𝓝 (embedding.compLpL 2 gaussianProduct
        (IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass g a T)-
        IBMSchwartzPhysicalClockIntegral.limitIntegralValue g a T)) := by
  simpa only [endpointLimitClass_eq] using wholeClass_tendsto g a T
end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalReflectedIto
