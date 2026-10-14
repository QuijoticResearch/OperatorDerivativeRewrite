import Foundation.PoissonExponentialTilt
import Foundation.BochnerL2Dominated
import Foundation.GaussianL2QuarticEmbeddingObstruction

/-! Actual square-root density geometry of Poisson exponential tilts. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonTiltHellingerGeometry
open PoissonDifferenceCore PoissonDifferenceOperators PoissonCoherentVectors PoissonExponentialTilt

def rootDensity (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (θ*(n : ℝ)/2-(rate : ℝ)*(Real.exp θ-1)/2)

theorem rootDensity_sq (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    (rootDensity rate θ n)^2=density rate θ n := by
  rw [rootDensity,← Real.exp_nat_mul,density]
  congr 1
  ring

theorem rootDensity_memLp (rate : ℝ≥0) (θ : ℝ) : MemLp (rootDensity rate θ) 2 (poissonLaw rate) := by
  have he : rootDensity rate θ=(fun n => Real.exp (-(rate : ℝ)*(Real.exp θ-1)/2)*exponential (θ/2) n) := by
    funext n
    rw [rootDensity,exponential,← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (exponential_memLp rate (θ/2)).const_mul _

def rootClass (rate : ℝ≥0) (θ : ℝ) : ScalarL2 rate :=
  (rootDensity_memLp rate θ).toLp (rootDensity rate θ)

theorem rootClass_coeFn (rate : ℝ≥0) (θ : ℝ) : rootClass rate θ =ᵐ[poissonLaw rate] rootDensity rate θ :=
  (rootDensity_memLp rate θ).coeFn_toLp

theorem rootClass_norm_sq (rate : ℝ≥0) (θ : ℝ) : ‖rootClass rate θ‖^2=1 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ n, density rate θ n ∂poissonLaw rate := by
      apply integral_congr_ae
      filter_upwards [rootClass_coeFn rate θ] with n hn
      rw [hn,Real.norm_eq_abs,sq_abs,rootDensity_sq]
    _ = 1 := density_mean_one rate θ

theorem rootClass_inner (rate : ℝ≥0) (θ η : ℝ) :
    inner ℝ (rootClass rate θ) (rootClass rate η)=
      Real.exp (-(rate : ℝ)/2*(Real.exp (θ/2)-Real.exp (η/2))^2) := by
  rw [L2_inner_eq_integral]
  have he : (∫ n, inner ℝ (rootClass rate θ n) (rootClass rate η n) ∂poissonLaw rate)=
      Real.exp (-(rate : ℝ)*(Real.exp θ+Real.exp η-2)/2)*
        (∫ n, exponential ((θ+η)/2) n ∂poissonLaw rate) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [rootClass_coeFn rate θ,rootClass_coeFn rate η] with n ht hη
    rw [ht,hη]
    simp only [Real.inner_apply,rootDensity,exponential]
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [he,exponential_integral,← Real.exp_add]
  have hθ : (Real.exp (θ/2))^2=Real.exp θ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hη : (Real.exp (η/2))^2=Real.exp η := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hm : Real.exp (θ/2)*Real.exp (η/2)=Real.exp ((θ+η)/2) := by rw [← Real.exp_add]; congr 1; ring
  congr 1
  nlinarith [hθ,hη,hm]

theorem hellinger_distance_sq (rate : ℝ≥0) (θ η : ℝ) :
    ‖rootClass rate θ-rootClass rate η‖^2=
      2*(1-Real.exp (-(rate : ℝ)/2*(Real.exp (θ/2)-Real.exp (η/2))^2)) := by
  rw [norm_sub_sq_real,rootClass_norm_sq,rootClass_norm_sq,rootClass_inner]
  ring

def sqrtRate (rate : ℝ≥0) (θ : ℝ) : ℝ := Real.sqrt rate*Real.exp (θ/2)

theorem sqrtRate_eq_sqrt_tilted (rate : ℝ≥0) (θ : ℝ) :
    sqrtRate rate θ=Real.sqrt (tiltedRate rate θ) := by
  have hp : 0≤sqrtRate rate θ := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hs : (sqrtRate rate θ)^2=(tiltedRate rate θ : ℝ) := by
    rw [sqrtRate,mul_pow,Real.sq_sqrt rate.coe_nonneg,← Real.exp_nat_mul]
    change (rate : ℝ)*Real.exp ((2 : ℕ)*(θ/2))=(rate : ℝ)*Real.exp θ
    congr 2
    ring
  have hr := Real.sq_sqrt (tiltedRate rate θ).coe_nonneg
  nlinarith [Real.sqrt_nonneg (tiltedRate rate θ)]

theorem rootClass_inner_sqrtRate (rate : ℝ≥0) (θ η : ℝ) :
    inner ℝ (rootClass rate θ) (rootClass rate η)=
      Real.exp (-((sqrtRate rate θ-sqrtRate rate η)^2)/2) := by
  rw [rootClass_inner]
  have he : (sqrtRate rate θ-sqrtRate rate η)^2=
      (rate : ℝ)*(Real.exp (θ/2)-Real.exp (η/2))^2 := by
    rw [sqrtRate,sqrtRate,← mul_sub,mul_pow,Real.sq_sqrt rate.coe_nonneg]
  rw [he]
  congr 1
  ring

def gaussianRoot (a : ℝ) : GaussianCore.GaussianL2 :=
  Real.exp (-a^2) • GaussianL2QuarticEmbeddingObstruction.classTwo a

theorem gaussianRoot_norm (a : ℝ) : ‖gaussianRoot a‖=1 := by
  rw [gaussianRoot,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    GaussianL2QuarticEmbeddingObstruction.classTwo_norm,← Real.exp_add,neg_add_cancel,Real.exp_zero]

theorem gaussianRoot_inner (a b : ℝ) :
    inner ℝ (gaussianRoot a) (gaussianRoot b)=Real.exp (-((a-b)^2)/2) := by
  have hp : inner ℝ (GaussianL2QuarticEmbeddingObstruction.classTwo a)
      (GaussianL2QuarticEmbeddingObstruction.classTwo b)=Real.exp ((a+b)^2/2) := by
    rw [L2_inner_eq_integral]
    calc
      _ = ∫ x, Real.exp ((a+b)*x) ∂GaussianCore.γ := by
        apply integral_congr_ae
        filter_upwards [(GaussianCore.gaussian_exp_memLp_two a).coeFn_toLp,
          (GaussianCore.gaussian_exp_memLp_two b).coeFn_toLp] with x ha hb
        change GaussianL2QuarticEmbeddingObstruction.classTwo a x=Real.exp (a*x) at ha
        change GaussianL2QuarticEmbeddingObstruction.classTwo b x=Real.exp (b*x) at hb
        rw [ha,hb]
        simp only [Real.inner_apply]
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := GaussianL2QuarticEmbeddingObstruction.exponential_integral (a+b)
  rw [gaussianRoot,gaussianRoot,real_inner_smul_left,real_inner_smul_right,hp,
    ← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem poisson_gaussian_affinity_transfer (rate : ℝ≥0) (θ η : ℝ) :
    inner ℝ (rootClass rate θ) (rootClass rate η)=
      inner ℝ (gaussianRoot (sqrtRate rate θ)) (gaussianRoot (sqrtRate rate η)) := by
  rw [rootClass_inner_sqrtRate,gaussianRoot_inner]

theorem finite_affinity_inner_transfer (rate : ℝ≥0) {I : Type*} [Fintype I]
    (θ : I → ℝ) (c d : I → ℝ) :
    inner ℝ (∑ i, c i • rootClass rate (θ i)) (∑ i, d i • rootClass rate (θ i))=
      inner ℝ (∑ i, c i • gaussianRoot (sqrtRate rate (θ i)))
        (∑ i, d i • gaussianRoot (sqrtRate rate (θ i))) := by
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    poisson_gaussian_affinity_transfer]

end OperatorDerivativeRewrite.Foundation.PoissonTiltHellingerGeometry
