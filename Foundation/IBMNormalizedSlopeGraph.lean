import Foundation.IBMNormalizedClockProfiles
import Foundation.GaussianDirectionalRecovery

/-! Actual reflected normalized IBM slopes in the original closed Gaussian
derivative graph, tested by arbitrary continuous source functionals. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNormalizedSlopeGraph
open InfiniteGaussian IBMNormalizedClockProfiles IBMFullSchwartzTerminal
open IBMSchwartzSourceSecondDerivative IBMSchwartzFullReflectedIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def slopeValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  BrownianSignIntegral.signum x •
    (Real.sqrt (T : ℝ) • spatialSlope g a n (Real.sqrt (T : ℝ) * |x|))

theorem slopeValue_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (slopeValue g a n T) := by
  apply BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
  have hs : Continuous (spatialSlope g a n) :=
    continuous_iff_continuousAt.mpr fun r => (spatialSlope_hasDerivAt g a n r).continuousAt
  have hr : Continuous (fun x : ℝ => Real.sqrt (T : ℝ) * |x|) :=
    continuous_const.mul continuous_abs
  have hc : Continuous (fun x : ℝ => Real.sqrt (T : ℝ) •
      spatialSlope g a n (Real.sqrt (T : ℝ) * |x|)) :=
    (hs.comp hr).const_smul (Real.sqrt (T : ℝ))
  exact hc.stronglyMeasurable

theorem slope_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (slopeValue g a n T) 2 GaussianCore.γ := by
  obtain ⟨C,hC,hb⟩ := IBMSchwartzFullGlobalBounds.slope_bound g a n
  apply MemLp.of_bound (slopeValue_measurable g a n T).aestronglyMeasurable
    (Real.sqrt (T : ℝ) * C)
  apply ae_of_all
  intro x
  rw [slopeValue, norm_smul, norm_smul,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_right (BrownianSignIntegral.signum_bound x)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_left (hb _) (Real.sqrt_nonneg _))

def slope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp GaussianL2 2 GaussianCore.γ := (slope_memLp g a n T).toLp _

theorem slope_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    slope g a n T =ᵐ[GaussianCore.γ] slopeValue g a n T :=
  (slope_memLp g a n T).coeFn_toLp

/-- The full source-valued profile has its genuine weak Gaussian derivative,
under EVERY continuous source functional, including the reflection cusp. -/
theorem tested_closed_graph (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) :
    (L.compLpL 2 GaussianCore.γ (profile g a n T),
      L.compLpL 2 GaussianCore.γ (slope g a n T)) ∈ GaussianCore.closedDerivative.graph := by
  let c := Real.sqrt (T : ℝ)
  let f : ℝ → ℝ := fun r => L (spatial g a n (c*r)) - L (spatial g a n 0)
  let h : ℝ → ℝ := fun r => c * L (spatialSlope g a n (c*r))
  have hd (r : ℝ) : HasDerivAt f (h r) r := by
    have hh := ((L.hasFDerivAt.comp_hasDerivAt (c*r)
      (IBMSchwartzSourceSecondDerivative.spatial_hasDerivAt g a n (c*r))).comp r
        ((hasDerivAt_id r).const_mul c)).sub_const (L (spatial g a n 0))
    simpa only [f,h,Function.comp_def,mul_one,one_mul,mul_comm] using hh
  have hc : Continuous h := continuous_const.mul
    (L.continuous.comp
      ((continuous_iff_continuousAt.mpr fun r => (spatialSlope_hasDerivAt g a n r).continuousAt).comp
        (continuous_const.mul continuous_id)))
  obtain ⟨C,hC,hb⟩ := IBMSchwartzFullGlobalBounds.slope_bound g a n
  let K : ℝ≥0 := ⟨c*‖L‖*C, by dsimp [c]; positivity⟩
  have hk (r : ℝ) : ‖h r‖ ≤ (K : ℝ) := by
    change ‖h r‖ ≤ c*‖L‖*C
    dsimp only [h]
    rw [norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left
      ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg L)))
        (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨hf,hh,hgraph⟩ := IBMReflectedGaussianSobolev.reflected_closed_graph hd hc hk
  have he1 : L.compLpL 2 GaussianCore.γ (profile g a n T) = hf.toLp _ := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (profile g a n T),profile_ae g a n T,hf.coeFn_toLp]
      with x hL hp hf
    rw [hL,hp,hf]
    simp only [profileValue,map_sub,f,c]
  have he2 : L.compLpL 2 GaussianCore.γ (slope g a n T) = hh.toLp _ := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (slope g a n T),slope_ae g a n T,hh.coeFn_toLp]
      with x hL hp hh
    rw [hL,hp,hh]
    simp only [slopeValue,map_smul,smul_eq_mul,h,c]
    ring
  rwa [he1,he2]

def sampledSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Lp GaussianL2 2 gaussianProduct :=
  (Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding (unitDirection T))
    (IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT)))
      (slope g a n T)

theorem test_pullback (v : CoefficientSpace) (hv : ‖v‖ = 1)
    (q : Lp GaussianL2 2 GaussianCore.γ) (L : GaussianL2 →L[ℝ] ℝ) :
    IBMClockObservationGraph.pullback v hv (L.compLpL 2 GaussianCore.γ q) =
      L.compLpL 2 gaussianProduct
        ((Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding v)
          (IBMClockObservationGraph.observation_measurePreserving v hv)) q) := by
  apply Lp.ext
  let hm := IBMClockObservationGraph.observation_measurePreserving v hv
  have hc := hm.quasiMeasurePreserving.ae_eq_comp (L.coeFn_compLpL q)
  filter_upwards [IBMClockObservationGraph.pullback_ae v hv (L.compLpL 2 GaussianCore.γ q),
    hc,L.coeFn_compLpL ((Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding v) hm) q),
    Lp.coeFn_compMeasurePreserving q hm] with ω hj hc hL hq
  dsimp only [Function.comp_def] at hc hq
  change ((Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding v) hm) q) ω = _ at hq
  rw [hj,hc,hL,hq]

/-- The genuine clock derivative of the actual full endpoint is the normalized
signed slope, after every continuous source test. -/
theorem tested_sampled_closed_graph (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) (L : GaussianL2 →L[ℝ] ℝ) :
    (L.compLpL 2 gaussianProduct (endpointClass g a n T),
      scalarTensor (unitDirection T) (L.compLpL 2 gaussianProduct (sampledSlope g a n T hT))) ∈
        closedCylindricalDerivative.graph := by
  have hg := IBMClockObservationGraph.pullback_closed_graph (unitDirection T)
    (unitDirection_norm hT) (tested_closed_graph g a n T L)
  rw [test_pullback,test_pullback] at hg
  change (L.compLpL 2 gaussianProduct (sampledProfile g a n T hT),
    scalarTensor (unitDirection T) (L.compLpL 2 gaussianProduct (sampledSlope g a n T hT))) ∈ _ at hg
  rwa [sampledProfile_eq_endpoint g a n hT] at hg

theorem signum_pos_mul {c : ℝ} (hc : 0 < c) (x : ℝ) :
    BrownianSignIntegral.signum (c*x) = BrownianSignIntegral.signum x := by
  simp [BrownianSignIntegral.signum,mul_pos_iff_of_pos_left hc,
    mul_neg_iff,hc,not_lt.mpr hc.le]

theorem sampledSlope_actual_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    sampledSlope g a n T hT =ᵐ[gaussianProduct] fun ω =>
      Real.sqrt (T : ℝ) • signedSlope g a n (IBMConstructedSources.clockPath ω T) := by
  let hm := IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (slope_ae g a n T)
  filter_upwards [Lp.coeFn_compMeasurePreserving (slope g a n T) hm,hp,clock_coordinate hT]
    with ω hs hp hc
  change sampledSlope g a n T hT ω = _ at hs
  have hpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT)
  dsimp only [Function.comp_def] at hp hs
  rw [hs,hp,hc,slopeValue,signedSlope,signum_pos_mul hpos,
    abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact smul_comm _ _ _

theorem actual_slope_recovery_hasSum (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) (L : GaussianL2 →L[ℝ] ℝ) :
    HasSum (fun k : ℕ => (k + 1 : ℝ)⁻¹ • GaussianNumberSectors.projection k
      (L.compLpL 2 gaussianProduct (sampledSlope g a n T hT)))
      (GaussianDirectionalRecovery.directionalRecovery (unitDirection T)
        (L.compLpL 2 gaussianProduct (endpointClass g a n T))) :=
  GaussianDirectionalRecovery.shifted_derivative_hasSum _ (unitDirection_norm hT)
    (tested_sampled_closed_graph g a n hT L)

end OperatorDerivativeRewrite.Foundation.IBMNormalizedSlopeGraph
