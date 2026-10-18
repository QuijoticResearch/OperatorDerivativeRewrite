import Foundation.IBMCorrectionStein
import Foundation.IBMGaussianSteinMoments

/-! Identification of the original shifted Schwartz correction expectation
with the actual two-term boundary residual, and its random L² closure. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMOriginalBoundaryResidual
open InfiniteGaussian IBMCorrectionStein IBMGaussianSteinMoments
open IBMJointMollifierGaussian IBMContinuousScenery IBMMollifier IBMConstructedSources

theorem triple_embedding (n : ℕ) (r : ℝ) (i : Fin 3) :
    firstChaosEmbedding (tripleCoefficient n r i) =
      wholeLineScenery (derivativeKernel n i) r :=
  (wholeLineScenery_eq_sourceEmbedding _ _).symm

theorem triple_inner (n : ℕ) (r : ℝ) (i j : Fin 3) :
    inner ℝ (tripleCoefficient n r i) (tripleCoefficient n r j) =
      inner ℝ (wholeLineScenery (derivativeKernel n i) r)
        (wholeLineScenery (derivativeKernel n j) r) :=
  (tripleCoefficient_inner n r i j).trans (gaussianTriple_covariance_eq_L2_inner n r i j)

theorem actual_bracket (n : ℕ) (r : ℝ) :
    ‖tripleCoefficient n r 1‖^2 +
      inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 2) = kernel n r := by
  rw [← real_inner_self_eq_norm_sq, triple_inner, triple_inner]
  simp only [derivativeKernel, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_neg, if_pos, ite_false, ite_true, real_inner_self_eq_norm_sq]
  have he := congrFun (IBMVarianceClockGeometry.variance_second n) r
  rw [IBMVarianceClockGeometry.variance,
    wholeLineVariance_second_deriv (kernel n) (kernel_compactSupport n)
      ((kernel_smooth n).of_le (by norm_num)) r] at he
  linarith

/-- The actual residual uses the original correction expectation and its
interior fourth-derivative term, rather than being defined by its limit. -/
def originalResidual (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  correction g a (tripleCoefficient n r 0) (tripleCoefficient n r 1)
    (tripleCoefficient n r 2) -
    (1/4 : ℝ) * ∫ ω, shiftedJet g a 4 (wholeLineScenery (kernel n) r ω) ∂gaussianProduct

theorem originalResidual_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    originalResidual g a n r =
      IBMBoundaryResidualLimit.coefficient (shiftedJet_lipschitz g a 2)
        (shiftedJet_lipschitz g a 4) n r := by
  unfold originalResidual
  rw [correction_identity, actual_bracket,
    IBMBoundaryResidualLimit.coefficient_eq_covariance, triple_inner, triple_embedding]
  simp only [derivativeKernel, if_pos, show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true]
  ring

theorem original_correction_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    Integrable (fun ω =>
      shiftedJet g a 2 (wholeLineScenery (kernel n) r ω) *
          (wholeLineScenery (deriv (kernel n)) r ω)^2 +
      shiftedJet g a 1 (wholeLineScenery (kernel n) r ω) *
          wholeLineScenery (deriv (deriv (kernel n))) r ω) gaussianProduct := by
  have he := correction_integrable g a (tripleCoefficient n r 0)
    (tripleCoefficient n r 1) (tripleCoefficient n r 2)
  simp only [triple_embedding, derivativeKernel,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_neg, if_pos, ite_false, ite_true] at he
  exact he

theorem originalResidual_literal (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    originalResidual g a n r =
      (∫ ω, shiftedJet g a 2 (wholeLineScenery (kernel n) r ω) *
          (wholeLineScenery (deriv (kernel n)) r ω)^2 +
        shiftedJet g a 1 (wholeLineScenery (kernel n) r ω) *
          wholeLineScenery (deriv (deriv (kernel n))) r ω ∂gaussianProduct) -
      (1/4 : ℝ) * ∫ ω, shiftedJet g a 4 (wholeLineScenery (kernel n) r ω) ∂gaussianProduct := by
  simp only [originalResidual, correction, triple_embedding, derivativeKernel,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_neg, if_pos, ite_false, ite_true]

def originalPathIntegral (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), originalResidual g a n |clockPath ω t.toNNReal|

theorem originalPathIntegral_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    originalPathIntegral g a n T =
      IBMBoundaryResidualLimit.pathIntegral (shiftedJet_lipschitz g a 2)
        (shiftedJet_lipschitz g a 4) n T := by
  funext ω
  unfold originalPathIntegral IBMBoundaryResidualLimit.pathIntegral
  simp_rw [originalResidual_identity]

theorem originalPathIntegral_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (originalPathIntegral g a n T) 2 gaussianProduct := by
  rw [originalPathIntegral_eq]
  exact IBMBoundaryResidualLimit.pathIntegral_memLp
    (shiftedJet_lipschitz g a 2) (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4) n T

/-- Strong random L² convergence for every fixed shift and finite horizon. -/
theorem originalPathIntegral_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => (originalPathIntegral_memLp g a n T).toLp _) atTop
      (𝓝 (jet g 2 a • BrownianMassLimitIdentification.coordinateClass T)) := by
  have he (n : ℕ) : (originalPathIntegral_memLp g a n T).toLp _ =
      (IBMBoundaryResidualLimit.pathIntegral_memLp (shiftedJet_lipschitz g a 2)
        (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4) n T).toLp _ := by
    apply Lp.ext
    exact (originalPathIntegral_memLp g a n T).coeFn_toLp.trans
      ((originalPathIntegral_eq g a n T).eventuallyEq.trans
        (IBMBoundaryResidualLimit.pathIntegral_memLp (shiftedJet_lipschitz g a 2)
          (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4) n T).coeFn_toLp.symm)
  simp only [he]
  simpa only [shiftedJet, add_zero] using
    IBMBoundaryResidualLimit.pathIntegral_tendsto (shiftedJet_lipschitz g a 2)
      (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4) T

theorem half_originalPathIntegral_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => (1/2 : ℝ) • (originalPathIntegral_memLp g a n T).toLp _) atTop
      (𝓝 ((jet g 2 a / 2) • BrownianMassLimitIdentification.coordinateClass T)) := by
  have he := (originalPathIntegral_tendsto g a T).const_smul (1/2 : ℝ)
  simpa only [smul_smul, one_div_mul_eq_div] using he

end OperatorDerivativeRewrite.Foundation.IBMOriginalBoundaryResidual
