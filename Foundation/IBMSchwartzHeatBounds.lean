import Foundation.IBMSchwartzPrimitiveLimit
import Foundation.IBMQuarticHeatDomain

/-! Fixed-mollifier growth and continuity for the actual nonlinear source
projection. Bounds use the realized products before projection. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatBounds
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments IBMGaussianSteinMoments
open IBMSchwartzSecondProjection IBMSchwartzSpatialPrimitive IBMSchwartzPrimitiveLimit
open GaussianNumberSectors IBMQuarticSecondChaos IBMQuadraticSpatialCalculus
open FractionalControlledEstimate

theorem weightedClass_norm_le (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : CoefficientSpace) (j : ℕ) (f : GaussianL2) :
    ‖weightedClass g a u j f‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g j)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedClass_coeFn g a u j f] with ω hf
  rw [hf, norm_mul]
  exact mul_le_mul_of_nonneg_right (shiftedJet_bound g a j _) (norm_nonneg _)

theorem square_norm_le (v : CoefficientSpace) : ‖square v‖ ≤ 2*‖v‖^2 := by
  have he := square_norm_sq v
  nlinarith [norm_nonneg (square v), sq_nonneg (‖v‖^2)]

theorem correction_norm_le (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) :
    ‖correctionClass g a u v w‖ ≤
      2*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*‖v‖^2 +
        SchwartzMap.seminorm ℝ 0 0 (jet g 1)*‖w‖ := by
  have h2 := weightedClass_norm_le g a u 2 (square v)
  have h1 := weightedClass_norm_le g a u 1 (firstChaosEmbedding w)
  rw [firstChaosEmbedding.norm_map] at h1
  have hs := mul_le_mul_of_nonneg_left (square_norm_le v)
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 2))
  exact (norm_add_le _ _).trans (by linarith)

/-- Only linear growth is needed: the slope is a projection of a bounded
jet times the actual first-chaos derivative field. -/
theorem slope_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖spatialSlope g a n r‖ ≤ C*(1+|r|) := by
  obtain ⟨B,hB,hb⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 1
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (jet g 1)*B, by positivity, fun r => ?_⟩
  rw [spatialSlope_eq_origin_projection]
  apply (projection_norm_le 2 _).trans
  apply (weightedClass_norm_le g a _ 1 _).trans
  rw [firstChaosEmbedding.norm_map]
  exact (mul_le_mul_of_nonneg_left (hb r)
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1))).trans_eq (by ring)

theorem projected_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖projection 2 (mollifiedClass g a n r)‖ ≤ C*(1+|r|)^2 := by
  obtain ⟨B,hB,hb⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 1
  obtain ⟨D,hD,hd⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 2
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*B^2+
    SchwartzMap.seminorm ℝ 0 0 (jet g 1)*D, by positivity, fun r => ?_⟩
  have hq : 1+|r| ≤ (1+|r|)^2 := by nlinarith [abs_nonneg r]
  have hv := pow_le_pow_left₀ (norm_nonneg _) (hb r) 2
  have h1 := mul_le_mul_of_nonneg_left (hd r)
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1))
  have h2 := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ 2*SchwartzMap.seminorm ℝ 0 0 (jet g 2))
  have h3 := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1)*D)
  apply (projection_norm_le 2 _).trans
  apply (correction_norm_le g a _ _ _).trans
  nlinarith

theorem slope_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (spatialSlope g a n) :=
  continuous_iff_continuousAt.mpr fun r => (spatialSlope_hasDerivAt g a n r).continuousAt

theorem projected_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (fun r => projection 2 (mollifiedClass g a n r)) := by
  have hc := IBMClockCubicTimeProjection.tripleCoefficient_continuous n
  have hq (j : ℕ) : Continuous (fun r => M g a (tripleCoefficient n r 0) j 0) :=
    (continuous_iff_continuousAt.mpr fun u =>
      (IBMGaussianMeanDerivative.mean_hasFDerivAt g a u j).continuousAt).comp (hc 0)
  have hw (i : Fin 3) : Continuous (fun r =>
      (GaussianTimeSpaceHermite.wick (tripleCoefficient n r i) 2 : GaussianL2)) :=
    (GaussianWickContinuity.wick_continuous 2).comp (hc i)
  have hx (i j : Fin 3) : Continuous (fun r =>
      cross (tripleCoefficient n r i) (tripleCoefficient n r j)) :=
    (crossBilinear.continuous.comp (hc i)).clm_apply (hc j)
  have hd : Continuous (fun r => inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)) :=
    (hc 0).inner (hc 1)
  have he : Continuous (fun r => inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 2)) :=
    (hc 0).inner (hc 2)
  simp_rw [mollified_projection_two]
  exact ((((((hc 1).norm.pow 2).add he).mul (hq 4)).add
    ((hd.pow 2).mul (hq 6))).div_const 2).smul (hw 0) |>.add
    (((hd.const_mul 2).mul (hq 4)).smul (hx 0 1)) |>.add
    ((hq 2).smul ((hw 1).add (hx 0 2)))

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatBounds
