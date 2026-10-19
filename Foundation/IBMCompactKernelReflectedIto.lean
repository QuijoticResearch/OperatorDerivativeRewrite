import Foundation.IBMCompactKernelSchwartz
import Foundation.IBMSchwartzFullReflectedIto

/-! The actual source-valued reflected stochastic identity for every compact
C3 kernel. The boundary and curvature are constructed before their L2 class. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactKernelReflectedIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open IBMConstructedSources BrownianClockWeightedEnergy GaussianHermiteIntegrand
open GaussianHermiteRepresentation IBMCompactKernelSchwartz IBMCorrectionStein
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def signedSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : GaussianL2 :=
  BrownianSignIntegral.signum r • slope g a ρ |r|

theorem signedSlope_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) : StronglyMeasurable (signedSlope g a ρ) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((continuous_iff_continuousAt.mpr fun r =>
      (slope_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).continuousAt).stronglyMeasurable.comp_measurable
        continuous_abs.measurable)

theorem field_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    MemLp (fun z => signedSlope g a ρ (sigma z)) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  obtain ⟨C,hC,hb⟩ := slope_bound g a hc (hρ.of_le (by norm_num))
  apply MemLp.of_bound ((signedSlope_measurable g a hc hρ).comp_measurable
    sigma_measurable).aestronglyMeasurable C
  exact Eventually.of_forall fun z => by
    change ‖signedSlope g a ρ (sigma z)‖ ≤ C
    rw [signedSlope,norm_smul]
    exact (mul_le_mul (BrownianSignIntegral.signum_bound _) (hb _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

def field (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    Lp GaussianL2 2 (PredictableRealL2.horizonMeasure T gaussianProduct) :=
  (field_memLp g a hc hρ T).toLp _

theorem field_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    field g a hc hρ T =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => signedSlope g a ρ (sigma z) := MemLp.coeFn_toLp _

theorem field_predictable (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (field g a hc hρ T) (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨signedSlope g a ρ ∘ b,
    (signedSlope_measurable g a hc hρ).comp_measurable hb.measurable, ?_⟩
  filter_upwards [field_ae g a hc hρ T,
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint T),
    ae_restrict_of_ae he,ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hf hB hb hz
  rw [hf]
  change signedSlope g a ρ (sigma z) = signedSlope g a ρ (b z)
  rw [← hb,hB,indicator_of_mem hz]

def integrand (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : GaussianSourceClockIto.Domain T :=
  ⟨field g a hc hρ T,field_predictable g a hc hρ T⟩

def integralValue (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  GaussianSourceClockIto.integral T (integrand g a hc hρ T)

def scalarPrimitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ)
    (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) : ℝ := L (spatial g a ρ r)

theorem scalarPrimitive_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (L : GaussianL2 →L[ℝ] ℝ) :
    ContDiff ℝ 2 (scalarPrimitive g a ρ L) := L.contDiff.comp (spatial_C2 g a hc hρ)

theorem scalarPrimitive_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) :
    deriv (scalarPrimitive g a ρ L) r = L (slope g a ρ r) :=
  (L.hasFDerivAt.comp_hasDerivAt r
    (spatial_hasDerivAt g a hc (hρ.of_le (by norm_num)) r)).deriv

theorem scalarPrimitive_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (L : GaussianL2 →L[ℝ] ℝ) (r : ℝ) :
    deriv (deriv (scalarPrimitive g a ρ L)) r = L (curvature g a ρ r) := by
  rw [show deriv (scalarPrimitive g a ρ L) = fun r => L (slope g a ρ r) from
    funext (scalarPrimitive_deriv g a hc hρ L)]
  exact (L.hasFDerivAt.comp_hasDerivAt r
    (slope_hasDerivAt g a hc (hρ.of_le (by norm_num)) r)).deriv

theorem scalarPrimitive_bounds (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (L : GaussianL2 →L[ℝ] ℝ) :
    ∃ K0 K1 : ℝ≥0, (∀ r, ‖deriv (scalarPrimitive g a ρ L) r‖ ≤ (K0 : ℝ)) ∧
      (∀ r, ‖deriv (deriv (scalarPrimitive g a ρ L)) r‖ ≤ (K1 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := slope_bound g a hc (hρ.of_le (by norm_num))
  obtain ⟨D,hD,hd⟩ := curvature_bound g a hc (hρ.of_le (by norm_num))
  refine ⟨⟨‖L‖*C,by positivity⟩,⟨‖L‖*D,by positivity⟩,?_,?_⟩
  · intro r
    rw [scalarPrimitive_deriv g a hc hρ]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb r) (norm_nonneg _))
  · intro r
    rw [scalarPrimitive_second_deriv g a hc hρ]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hd r) (norm_nonneg _))

theorem integral_test (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) (K1 : ℝ≥0)
    (h1 : ∀ r, ‖deriv (deriv (scalarPrimitive g a ρ L)) r‖ ≤ (K1 : ℝ)) :
    L.compLpL 2 gaussianProduct (integralValue g a hc hρ T) =
      itoIntegral (GaussianReflectedC2Ito.running (scalarPrimitive g a ρ L)
        (scalarPrimitive_C2 g a hc hρ L) K1 h1 T) := by
  apply GaussianSourceClockIto.scalarization_full
  have he : (fun z => L ((integrand g a hc hρ T).val z)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => BrownianSignIntegral.signum (sigma z)*deriv (scalarPrimitive g a ρ L) |sigma z| := by
    filter_upwards [field_ae g a hc hρ T] with z hz
    change L (field g a hc hρ T z) = _
    rw [hz,signedSlope,map_smul,scalarPrimitive_deriv g a hc hρ]
    rfl
  exact (GaussianReflectedC2Ito.running_coeFn (scalarPrimitive g a ρ L)
    (scalarPrimitive_C2 g a hc hρ L) K1 h1 T).trans
      ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).symm

def wholeCorrection (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ)
    (T : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  BrownianMassLimitIdentification.coordinateClass T ω • slope g a ρ 0 +
    (1/2 : ℝ) • ∫ s in 0..(T : ℝ), curvature g a ρ |clockPath ω s.toNNReal|

theorem tested_reflected_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) :
    ∀ᵐ ω ∂gaussianProduct,
      L (spatial g a ρ |clockPath ω T|-spatial g a ρ 0) =
        L (integralValue g a hc hρ T ω)+L (wholeCorrection g a ρ T ω) := by
  obtain ⟨K0,K1,h0,h1⟩ := scalarPrimitive_bounds g a hc hρ L
  let f := scalarPrimitive g a ρ L
  let hf := scalarPrimitive_C2 g a hc hρ L
  have hi := GaussianReflectedC2Ito.reflected_ito_pathwise f hf K1 h1 K0 h0 T
  have hs := L.coeFn_compLpL (integralValue g a hc hρ T)
  rw [integral_test g a hc hρ T L K1 h1] at hs
  have hm : BrownianMassLimitIdentification.coordinateClass T =ᵐ[gaussianProduct]
      fun ω => BrownianMassContinuousLimit.limitPath ω T := MemLp.coeFn_toLp _
  filter_upwards [hi,hs,hm] with ω hi hs hm
  have hk : IntervalIntegrable (fun s : ℝ => curvature g a ρ |clockPath ω s.toNNReal|)
      volume 0 T := ((curvature_continuous g a hc hρ).comp (continuous_abs.comp
        ((clockPath ω).continuous.comp continuous_real_toNNReal))).intervalIntegrable 0 T
  have hd := L.intervalIntegral_comp_comm (μ := volume) hk
  simp only [f,scalarPrimitive_deriv g a hc hρ,scalarPrimitive_second_deriv g a hc hρ] at hi
  rw [hs] at hi
  rw [map_sub,wholeCorrection,map_add,map_smul,map_smul,← hd,hm]
  change L (spatial g a ρ |clockPath ω T|)-L (spatial g a ρ 0) =
    L (integralValue g a hc hρ T ω)+
      (BrownianMassContinuousLimit.limitPath ω T • L (slope g a ρ 0)+
        (1/2 : ℝ) • ∫ s in 0..(T : ℝ), L (curvature g a ρ |clockPath ω s.toNNReal|))
  simp only [scalarPrimitive,smul_eq_mul] at hi ⊢
  linear_combination hi

/-- Full source-valued identity in the actual clock probability space. -/
theorem reflected_identity_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    (fun ω => spatial g a ρ |clockPath ω T|-spatial g a ρ 0) =ᵐ[gaussianProduct]
      fun ω => integralValue g a hc hρ T ω+wholeCorrection g a ρ T ω := by
  have hz : (fun ω => spatial g a ρ |clockPath ω T|-spatial g a ρ 0-
      (integralValue g a hc hρ T ω+wholeCorrection g a ρ T ω)) =ᵐ[gaussianProduct] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [tested_reflected_identity g a hc hρ T L] with ω hω
    simpa only [map_sub,map_add,Pi.zero_apply,sub_eq_zero] using hω
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

theorem endpoint_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    MemLp (fun ω => spatial g a ρ |clockPath ω T|) 2 gaussianProduct := by
  apply MemLp.of_bound
    (((spatial_C2 g a hc hρ).continuous).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable T)).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 (jet g 0))
  exact Eventually.of_forall fun ω => IBMSchwartzSourceDerivative.observable_bound g a 0 _

def endpointClass (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (endpoint_memLp g a hc hρ T).toLp _-Lp.const 2 gaussianProduct (spatial g a ρ 0)

theorem endpointClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    endpointClass g a hc hρ T =ᵐ[gaussianProduct]
      fun ω => spatial g a ρ |clockPath ω T|-spatial g a ρ 0 := by
  filter_upwards [Lp.coeFn_sub ((endpoint_memLp g a hc hρ T).toLp _)
    (Lp.const 2 gaussianProduct (spatial g a ρ 0)),
    (endpoint_memLp g a hc hρ T).coeFn_toLp,
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := spatial g a ρ 0)] with ω hs he hk
  change endpointClass g a hc hρ T ω = _ at hs
  rw [hs]
  simp only [Pi.sub_apply,he,hk,Function.const_apply]

theorem wholeCorrection_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    MemLp (wholeCorrection g a ρ T) 2 gaussianProduct := by
  have he : (fun ω => endpointClass g a hc hρ T ω-integralValue g a hc hρ T ω)
      =ᵐ[gaussianProduct] wholeCorrection g a ρ T := by
    filter_upwards [endpointClass_ae g a hc hρ T,reflected_identity_ae g a hc hρ T] with ω he hi
    rw [he,hi]
    abel
  exact (memLp_congr_ae he).mp ((Lp.memLp (endpointClass g a hc hρ T)).sub
    (Lp.memLp (integralValue g a hc hρ T)))

def wholeClass (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (wholeCorrection_memLp g a hc hρ T).toLp _

/-- Actual stochastic integral plus the separately constructed boundary and curvature. -/
theorem finite_kernel_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    endpointClass g a hc hρ T = integralValue g a hc hρ T+wholeClass g a hc hρ T := by
  apply Lp.ext
  filter_upwards [endpointClass_ae g a hc hρ T,
    (wholeCorrection_memLp g a hc hρ T).coeFn_toLp,reflected_identity_ae g a hc hρ T,
    Lp.coeFn_add (integralValue g a hc hρ T) (wholeClass g a hc hρ T)] with ω he hw hi ha
  rw [he,ha]
  simp only [Pi.add_apply]
  change _ = integralValue g a hc hρ T ω+wholeClass g a hc hρ T ω
  rw [show wholeClass g a hc hρ T ω = wholeCorrection g a ρ T ω from hw]
  exact hi

/-- Every positive continuum width is the actual dilated kernel, with the original
predictable Ito integral and retained origin term. Positivity/mass are not needed
for this finite-width C3 stochastic identity. -/
theorem dilated_kernel_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    let hd := IBMDilatedMollifier.dilate_compact hc hε.ne'
    let hs := IBMDilatedMollifier.dilate_contDiff hρ ε
    endpointClass g a hd hs T = integralValue g a hd hs T+wholeClass g a hd hs T :=
  finite_kernel_identity g a _ _ T

end OperatorDerivativeRewrite.Foundation.IBMCompactKernelReflectedIto
