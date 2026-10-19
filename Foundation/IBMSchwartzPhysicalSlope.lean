import Foundation.IBMPhysicalNegativeEmbedding
import Foundation.IBMSchwartzPhysicalPrimitive

/-! The full first spatial slope in the actual physical H^-1 space,
including its nonlinear weights and the degenerate origin. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalSlope
local instance : InnerProductSpace ℝ H^{(-1 : ℝ)}(ℝ) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
open InfiniteGaussian GaussianTimeHilbert IBMCorrectionStein IBMShiftedJetMoments
open IBMGaussianSteinMoments IBMQuarticPrimitiveLimit IBMPhysicalNoiseVectors
open IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus IBMPhysicalNoiseClock
open IBMPhysicalDirac IBMPhysicalNegativeEmbedding IBMSchwartzPhysicalFirstKernel
open IBMSchwartzPhysicalPrimitive IBMGaussianMeanDerivative

theorem mean_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) :
    Continuous (fun u : CoefficientSpace => M g a u j 0) :=
  continuous_iff_continuousAt.mpr fun u => (mean_hasFDerivAt g a u j).continuousAt

theorem mean_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    ‖M g a u j 0‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g j) := by
  rw [moment_zero]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := gaussianProduct)
      (Eventually.of_forall fun ω => shiftedJet_bound g a j (firstChaosEmbedding u ω)))

def covariance (n : ℕ) (r : ℝ) : ℝ :=
  inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)

theorem covariance_eq (n : ℕ) (r : ℝ) :
    covariance n r = deriv (IBMVarianceClockGeometry.variance n) r/2 := by
  have he := IBMQuarticSecondGeometry.coefficient_slope n r
  change 2*covariance n r = _ at he
  linarith

theorem covariance_bound (n : ℕ) (r : ℝ) : ‖covariance n r‖ ≤ 1 := by
  rw [covariance_eq, norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hb := IBMVarianceClockGeometry.slope_bound n r
  linarith [norm_nonneg (deriv (IBMVarianceClockGeometry.variance n) r)]

theorem covariance_tendsto (r : ℝ) :
    Tendsto (fun n => covariance n r) atTop (𝓝 (BrownianSignIntegral.signum r/2)) := by
  simp_rw [covariance_eq]
  exact (IBMVarianceClockGeometry.slope_tendsto r).div_const 2

theorem physicalJet_one_embedding (n : ℕ) (r : ℝ) :
    embedding (physicalJet n r 1) = translated n r := by
  change l2Value (convolutionKernel (deriv (IBMMollifier.kernel n)) r) = _
  rw [IBMPhysicalDerivativeKernel.derivative_eq_translated
    ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
    (IBMMollifier.kernel_compactSupport n)]
  rfl

def value (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  embedding (slope g a n r)

theorem value_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    value g a n r =
      (covariance n r*M g a (tripleCoefficient n r 0) 3 0) • embedding (physicalJet n r 0)+
        M g a (tripleCoefficient n r 0) 1 0 • translated n r := by
  rw [value, slope_eq, map_add, map_smul, map_smul, physicalJet_one_embedding]
  rfl

def limitValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  (BrownianSignIntegral.signum r/2*M g a (baseCoefficient r) 3 0) • embedding (vector r)+
    M g a (baseCoefficient r) 1 0 • dirac r

theorem value_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    Tendsto (fun n => value g a n r) atTop (𝓝 (limitValue g a r)) := by
  have hM (j : ℕ) := (mean_continuous g a j).continuousAt.tendsto.comp (coefficient_tendsto r)
  have hK := embedding.continuous.tendsto _ |>.comp (mollifier_kernel_tendsto r)
  simpa only [value_eq, limitValue, physicalJet,
    IBMJointMollifierGaussian.derivativeKernel, ite_true, Function.comp_def] using
    (((covariance_tendsto r).mul (hM 3)).smul hK).add
      ((hM 1).smul (translated_tendsto r))

theorem value_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (value g a n) := embedding.continuous.comp (slope_continuous g a n)

theorem limitValue_stronglyMeasurable (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    StronglyMeasurable (limitValue g a) :=
  stronglyMeasurable_of_tendsto atTop
    (fun n => (value_continuous g a n).stronglyMeasurable)
    (tendsto_pi_nhds.mpr (value_tendsto g a))

theorem convolution_error (n : ℕ) (r : ℝ) :
    ‖convolutionKernel (IBMMollifier.kernel n) r-vector r‖ ≤ Real.sqrt (IBMMollifier.bump n).rOut := by
  rw [← physicalNoise.norm_map, map_sub, convolutionKernel_realizes
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n), physicalNoise_vector]
  exact IBMContinuousScenery.concreteMollifier_uniform_norm_le n r

theorem convolution_growth (n : ℕ) (r : ℝ) :
    ‖convolutionKernel (IBMMollifier.kernel n) r‖ ≤ 3*(1+|r|) := by
  have he := convolution_error n r
  have hr : (IBMMollifier.bump n).rOut ≤ 4 := by
    change 2/((n : ℝ)+1) ≤ 4
    rw [div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hs : Real.sqrt (IBMMollifier.bump n).rOut ≤ 2 := by
    nlinarith [Real.sq_sqrt (IBMMollifier.bump n).rOut_pos.le,
      Real.sqrt_nonneg (IBMMollifier.bump n).rOut]
  have hv : ‖vector r‖ ≤ 1+|r| := by
    have hn := vector_norm_sq r
    nlinarith [norm_nonneg (vector r), abs_nonneg r, sq_nonneg (|r|)]
  have ht := norm_add_le (convolutionKernel (IBMMollifier.kernel n) r-vector r) (vector r)
  rw [sub_add_cancel] at ht
  linarith [abs_nonneg r]

theorem translated_growth (n : ℕ) (r : ℝ) :
    ‖translated n r‖ ≤
      (‖IBMDeltaBoundary.deltaZeroHminusOne‖+3*‖physicalDerivative‖)*(1+|r|) := by
  rw [translated_eq]
  have hb := (physicalDerivative.le_opNorm (convolutionKernel (IBMMollifier.kernel n) r)).trans
    (mul_le_mul_of_nonneg_left (convolution_growth n r) (norm_nonneg _))
  have ht := norm_sub_le IBMDeltaBoundary.deltaZeroHminusOne
    (physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r))
  nlinarith [mul_nonneg (norm_nonneg IBMDeltaBoundary.deltaZeroHminusOne) (abs_nonneg r)]

def growthConstant (g : SchwartzMap ℝ ℝ) : ℝ :=
  3*SchwartzMap.seminorm ℝ 0 0 (jet g 3)*‖embedding‖+
    SchwartzMap.seminorm ℝ 0 0 (jet g 1)*
      (‖IBMDeltaBoundary.deltaZeroHminusOne‖+3*‖physicalDerivative‖)

theorem growthConstant_nonneg (g : SchwartzMap ℝ ℝ) : 0 ≤ growthConstant g := by
  unfold growthConstant
  positivity

theorem value_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    ‖value g a n r‖ ≤ growthConstant g*(1+|r|) := by
  rw [value_eq]
  have hc : ‖covariance n r*M g a (tripleCoefficient n r 0) 3 0‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g 3) := by
    rw [norm_mul]
    calc
      _ ≤ 1*SchwartzMap.seminorm ℝ 0 0 (jet g 3) :=
        mul_le_mul (covariance_bound n r) (mean_bound g a 3 _) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hq : ‖embedding (physicalJet n r 0)‖ ≤ ‖embedding‖*(3*(1+|r|)) :=
    (embedding.le_opNorm _).trans (mul_le_mul_of_nonneg_left (convolution_growth n r) (norm_nonneg _))
  have h1 := norm_add_le
    ((covariance n r*M g a (tripleCoefficient n r 0) 3 0) • embedding (physicalJet n r 0))
    (M g a (tripleCoefficient n r 0) 1 0 • translated n r)
  simp only [norm_smul] at h1
  have h2 := mul_le_mul hc hq (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul (mean_bound g a 1 (tripleCoefficient n r 0))
    (translated_growth n r) (norm_nonneg _) (by positivity)
  exact h1.trans ((add_le_add h2 h3).trans_eq (by unfold growthConstant; ring))

theorem limitValue_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    ‖limitValue g a r‖ ≤ growthConstant g*(1+|r|) :=
  le_of_tendsto (value_tendsto g a r).norm (Eventually.of_forall fun n => value_growth g a n r)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalSlope
