import Foundation.IBMCompactKernelIncrements
import Foundation.IBMCompactKernelReflectedIto
import Foundation.IBMNormalizedSlopeGraph

/-! Actual reflected clock graph and uniform endpoint energy for any compact
positive normalized kernel, using the original closed Gaussian derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactClockGraph
open InfiniteGaussian IBMCompactKernelSchwartz IBMCompactKernelReflectedIto
open IBMNormalizedClockProfiles IBMConstructedSources
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def profileValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  spatial g a ρ (Real.sqrt (T : ℝ)*|x|)-spatial g a ρ 0

theorem profile_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    MemLp (profileValue g a ρ T) 2 GaussianCore.γ := by
  apply MemLp.of_bound
    ((((spatial_C2 g a hc hρ).continuous.comp
      (continuous_const.mul continuous_abs)).sub continuous_const).aestronglyMeasurable)
    (2*SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g 0))
  apply ae_of_all
  intro x
  have h1 := IBMSchwartzSourceDerivative.observable_bound g a 0 (coefficient ρ (Real.sqrt (T : ℝ)*|x|))
  have h2 := IBMSchwartzSourceDerivative.observable_bound g a 0 (coefficient ρ 0)
  change ‖spatial g a ρ (Real.sqrt (T : ℝ)*|x|)-spatial g a ρ 0‖ ≤ _
  dsimp only [spatial]
  exact (norm_sub_le _ _).trans (by linarith)

def profile (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Lp GaussianL2 2 GaussianCore.γ :=
  (profile_memLp g a hc hρ T).toLp _

theorem profile_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    profile g a hc hρ T =ᵐ[GaussianCore.γ] profileValue g a ρ T := MemLp.coeFn_toLp _

theorem sampledProfile_eq_endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {T : ℝ≥0} (hT : 0 < T) :
    (Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding (unitDirection T))
      (IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT)))
      (profile g a hc hρ T) = endpointClass g a hc hρ T := by
  apply Lp.ext
  let hm := IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (profile_ae g a hc hρ T)
  filter_upwards [Lp.coeFn_compMeasurePreserving (profile g a hc hρ T) hm,hp,
    endpointClass_ae g a hc hρ T,clock_coordinate hT] with ω hs hp he hb
  dsimp only [Function.comp_def] at hs hp
  change ((Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding (unitDirection T)) hm)
    (profile g a hc hρ T)) ω = _ at hs
  rw [hs,hp,he,hb,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

theorem profile_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    ‖profile g a hc hρ T‖^2 ≤ slopeBound g^2*Real.sqrt (T : ℝ)*absoluteMoment := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have hi := GaussianReflectedSecondBoundary.absolute_memLp.integrable (by simp : (1 : ℝ≥0∞) ≤ 2)
  have hb : ∀ᵐ x ∂GaussianCore.γ, ‖profile g a hc hρ T x‖^2 ≤
      slopeBound g^2*Real.sqrt (T : ℝ)*|x| := by
    filter_upwards [profile_ae g a hc hρ T] with x hx
    rw [hx]
    have hp := IBMCompactKernelIncrements.spatial_increment g a hc hρ.continuous hpos hmass
      (Real.sqrt (T : ℝ)*|x|) 0
    have hnon : 0 ≤ Real.sqrt (T : ℝ)*|x| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    simp only [sub_zero,abs_of_nonneg hnon] at hp
    calc
      _ ≤ (slopeBound g*Real.sqrt (Real.sqrt (T : ℝ)*|x|))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hp 2
      _ = _ := by rw [mul_pow,Real.sq_sqrt hnon]; ring
  have hh := integral_mono_ae ((Lp.memLp (profile g a hc hρ T)).norm.integrable_sq)
    (hi.const_mul (slopeBound g^2*Real.sqrt (T : ℝ))) hb
  rw [integral_const_mul] at hh
  exact hh

theorem endpoint_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) {T : ℝ≥0} (hT : 0 < T) :
    ‖endpointClass g a hc hρ T‖^2 ≤ slopeBound g^2*Real.sqrt (T : ℝ)*absoluteMoment := by
  rw [← sampledProfile_eq_endpoint g a hc hρ hT,LinearIsometry.norm_map]
  exact profile_uniform_energy g a hc hρ hpos hmass T

theorem pointSlope_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    MemLp (fun ω => signedSlope g a ρ (clockPath ω T)) 2 gaussianProduct := by
  obtain ⟨C,hC,hb⟩ := slope_bound g a hc (hρ.of_le (by norm_num))
  apply MemLp.of_bound ((signedSlope_measurable g a hc hρ).comp_measurable
    ((continuous_eval_const T).measurable.comp clockPath_measurable)).aestronglyMeasurable C
  exact ae_of_all _ fun ω => by
    change ‖signedSlope g a ρ (clockPath ω T)‖ ≤ C
    rw [signedSlope,norm_smul]
    exact (mul_le_mul (BrownianSignIntegral.signum_bound _) (hb _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

def pointSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (pointSlope_memLp g a hc hρ T).toLp _

theorem pointSlope_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) :
    pointSlope g a hc hρ T =ᵐ[gaussianProduct] fun ω => signedSlope g a ρ (clockPath ω T) :=
  MemLp.coeFn_toLp _

/-- The actual closed clock derivative of the full source-valued endpoint,
under every source functional. The reflection cusp is handled weakly. -/
theorem tested_closed_graph (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {T : ℝ≥0}
    (hT : 0 < T) (L : GaussianL2 →L[ℝ] ℝ) :
    (L.compLpL 2 gaussianProduct (endpointClass g a hc hρ T),
      scalarTensor (unitDirection T) (L.compLpL 2 gaussianProduct
        (Real.sqrt (T : ℝ) • pointSlope g a hc hρ T))) ∈ closedCylindricalDerivative.graph := by
  let c := Real.sqrt (T : ℝ)
  let f : ℝ → ℝ := fun r => L (spatial g a ρ (c*r))-L (spatial g a ρ 0)
  let h : ℝ → ℝ := fun r => c*L (slope g a ρ (c*r))
  have hd (r : ℝ) : HasDerivAt f (h r) r := by
    have hh := ((L.hasFDerivAt.comp_hasDerivAt (c*r)
      (spatial_hasDerivAt g a hc (hρ.of_le (by norm_num)) (c*r))).comp r
        ((hasDerivAt_id r).const_mul c)).sub_const (L (spatial g a ρ 0))
    simpa only [f,h,Function.comp_def,mul_one,one_mul,mul_comm] using hh
  have hhcont : Continuous h := continuous_const.mul
    (L.continuous.comp ((continuous_iff_continuousAt.mpr fun r =>
      (slope_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).continuousAt).comp
        (continuous_const.mul continuous_id)))
  obtain ⟨C,hC,hb⟩ := slope_bound g a hc (hρ.of_le (by norm_num))
  let K : ℝ≥0 := ⟨c*‖L‖*C,by dsimp [c]; positivity⟩
  have hk (r : ℝ) : ‖h r‖ ≤ (K : ℝ) := by
    change ‖h r‖ ≤ c*‖L‖*C
    dsimp only [h]
    rw [norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg L)))
        (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨hf,hh,hgraph⟩ := IBMReflectedGaussianSobolev.reflected_closed_graph hd hhcont hk
  let v := unitDirection T
  let hv := unitDirection_norm hT
  let hm := IBMClockObservationGraph.observation_measurePreserving v hv
  have h1 : IBMClockObservationGraph.pullback v hv (hf.toLp _) =
      L.compLpL 2 gaussianProduct (endpointClass g a hc hρ T) := by
    have ha := hm.quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
    apply Lp.ext
    filter_upwards [IBMClockObservationGraph.pullback_ae v hv (hf.toLp _),ha,
      L.coeFn_compLpL (endpointClass g a hc hρ T),endpointClass_ae g a hc hρ T,
      clock_coordinate hT] with ω hp ha hL he hb
    dsimp only [Function.comp_def] at ha
    rw [hp,ha,hL,he,hb,map_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : IBMClockObservationGraph.pullback v hv (hh.toLp _) =
      L.compLpL 2 gaussianProduct (Real.sqrt (T : ℝ) • pointSlope g a hc hρ T) := by
    have ha := hm.quasiMeasurePreserving.ae_eq_comp hh.coeFn_toLp
    apply Lp.ext
    filter_upwards [IBMClockObservationGraph.pullback_ae v hv (hh.toLp _),ha,
      L.coeFn_compLpL (Real.sqrt (T : ℝ) • pointSlope g a hc hρ T),
      Lp.coeFn_smul (Real.sqrt (T : ℝ)) (pointSlope g a hc hρ T),
      pointSlope_ae g a hc hρ T,clock_coordinate hT] with ω hp ha hL hs he hb
    dsimp only [Function.comp_def] at ha
    rw [hp,ha,hL,hs,Pi.smul_apply,he,hb,signedSlope,
      IBMNormalizedSlopeGraph.signum_pos_mul (Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT)),
      abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [h,c,map_smul,smul_eq_mul]
    ring
  have hg := IBMClockObservationGraph.pullback_closed_graph v hv hgraph
  rwa [h1,h2] at hg

end OperatorDerivativeRewrite.Foundation.IBMCompactClockGraph
