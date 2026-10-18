import Foundation.IBMQuarticClockMean
import Foundation.IBMQuarticOriginProjection

/-! Projection of the actual source-L2-valued quartic correction before
clock averaging. The source time integral has its native continuous domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticTimeProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick
open IBMEvenCorrectionProjection IBMQuarticSecondGeometry IBMQuarticClockMean
open GaussianNumberSectors IBMConstructedSources IBMQuarticOriginProjection

theorem quartic_continuous : Continuous quartic := by
  have hn : Continuous (fun u : CoefficientSpace => ‖u‖^2) := continuous_norm.pow 2
  change Continuous (fun u : CoefficientSpace => (wick u 4 : GaussianL2) +
    (6*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2) + (3*(‖u‖^2)^2 : ℝ) • (wick u 0 : GaussianL2))
  exact ((GaussianWickContinuity.wick_continuous 4).add
    ((hn.const_mul 6).smul (GaussianWickContinuity.wick_continuous 2))).add
    (((hn.pow 2).const_mul 3).smul (GaussianWickContinuity.wick_continuous 0))

theorem squareProduct_continuous_of {u v : ℝ → CoefficientSpace} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun r => squareProduct (u r) (v r)) := by
  exact (((quartic_continuous.comp (hu.add hv)).add (quartic_continuous.comp (hu.sub hv))).sub
    ((quartic_continuous.comp hu).const_smul (2 : ℝ))).sub
    ((quartic_continuous.comp hv).const_smul (2 : ℝ)) |>.const_smul (1/12 : ℝ)

theorem cubeProduct_continuous_of {u w : ℝ → CoefficientSpace} (hu : Continuous u) (hw : Continuous w) :
    Continuous (fun r => cubeProduct (u r) (w r)) := by
  exact (((quartic_continuous.comp ((hu.const_smul (2 : ℝ)).add hw)).sub
    (quartic_continuous.comp ((hu.const_smul (2 : ℝ)).sub hw))).sub
    ((quartic_continuous.comp (hu.add hw)).const_smul (2 : ℝ))).add
    ((quartic_continuous.comp (hu.sub hw)).const_smul (2 : ℝ)) |>.const_smul (1/48 : ℝ)

theorem spatialQuartic_continuous (n : ℕ) : Continuous (spatialQuartic n) := by
  have hc := IBMClockCubicTimeProjection.tripleCoefficient_continuous n
  change Continuous (fun r => (1/2 : ℝ) • squareProduct
    (IBMGaussianSteinMoments.tripleCoefficient n r 0) (IBMGaussianSteinMoments.tripleCoefficient n r 1) +
    (1/6 : ℝ) • cubeProduct (IBMGaussianSteinMoments.tripleCoefficient n r 0)
      (IBMGaussianSteinMoments.tripleCoefficient n r 2))
  exact ((squareProduct_continuous_of (hc 0) (hc 1)).const_smul (1/2 : ℝ)).add
    ((cubeProduct_continuous_of (hc 0) (hc 2)).const_smul (1/6 : ℝ))

theorem spatialQuartic_path_continuous (n : ℕ) (ω : SampleSpace) :
    Continuous (fun s : ℝ => spatialQuartic n |clockPath ω s.toNNReal|) :=
  (spatialQuartic_continuous n).comp (continuous_abs.comp
    ((clockPath ω).continuous.comp continuous_real_toNNReal))

theorem integrated_projection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    projection 2 (∫ s in 0..(T : ℝ), spatialQuartic n |clockPath ω s.toNNReal|) =
      integratedValue n T ω := by
  exact ((projection 2).intervalIntegral_comp_comm
    ((spatialQuartic_path_continuous n ω).intervalIntegrable 0 T)).symm

def wholeCorrection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  BrownianMassLimitIdentification.coordinateClass T ω • originClass n +
    (1/2 : ℝ) • ∫ s in 0..(T : ℝ), spatialQuartic n |clockPath ω s.toNNReal|

theorem wholeCorrection_projection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    projection 2 (wholeCorrection n T ω) =
      BrownianMassLimitIdentification.coordinateClass T ω • IBMQuarticSecondPrimitive.slope n 0 +
        (1/2 : ℝ) • integratedValue n T ω := by
  rw [wholeCorrection, map_add, map_smul, map_smul, origin_projection, integrated_projection]

theorem projected_whole_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun ω => projection 2 (wholeCorrection n T ω)) gaussianProduct := by
  have hm := ((Lp.memLp (BrownianMassLimitIdentification.coordinateClass T)).integrable (by norm_num)).smul_const
    (IBMQuarticSecondPrimitive.slope n 0)
  have hi := hm.add ((integratedValue_integrable n T hT).smul (1/2 : ℝ))
  convert hi using 1
  funext ω
  exact wholeCorrection_projection n T ω

/-- The actual second-source projection of the whole source-valued time
correction has the previously identified clock mean. -/
theorem projected_whole_mean (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, projection 2 (wholeCorrection n T ω) ∂gaussianProduct) = correctedMean n T := by
  simp_rw [wholeCorrection_projection]
  have hi : Integrable (fun ω => (1/2 : ℝ) • integratedValue n T ω) gaussianProduct :=
    (integratedValue_integrable n T hT).smul (1/2 : ℝ)
  have hs : (∫ ω, (1/2 : ℝ) • integratedValue n T ω ∂gaussianProduct) =
      (1/2 : ℝ) • ∫ ω, integratedValue n T ω ∂gaussianProduct := integral_smul _ _
  rw [integral_add
    (((Lp.memLp (BrownianMassLimitIdentification.coordinateClass T)).integrable (by norm_num)).smul_const
      (IBMQuarticSecondPrimitive.slope n 0))
    hi, integral_smul_const, hs]
  rfl

theorem projected_whole_mean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, projection 2 (wholeCorrection n T ω) ∂gaussianProduct) atTop
      (𝓝 (IBMQuarticClockTerminal.terminalLimit T)) := by
  simp_rw [projected_whole_mean _ T hT]
  exact correctedMean_tendsto T hT

end OperatorDerivativeRewrite.Foundation.IBMQuarticTimeProjection
