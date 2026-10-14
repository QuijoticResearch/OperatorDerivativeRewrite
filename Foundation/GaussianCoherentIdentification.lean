import Foundation.GaussianExponentialSobolevObstruction
import Foundation.GaussianDisplacementFromPoisson
import Foundation.PoissonCoherentRecovery

/-! Physical Gaussian coherent vectors identified through the actual Poisson gauge and full graphs. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianCoherentIdentification
open PoissonDifferenceOperators PoissonCharlierHilbertBasis PoissonTiltHellingerGeometry
open PoissonExponentialTilt PoissonTiltSourceGauge PoissonCoherentRecovery GaussianDisplacementFromPoisson
open GaussianExponentialSobolevObstruction
open PoissonCoordinateEvaluation

theorem gaussianRoot_derivative_graph (d : ℝ) :
    (gaussianRoot d,d • gaussianRoot d)∈GaussianCore.closedDerivative.graph := by
  have hg := GaussianCore.closedDerivative.graph.smul_mem (Real.exp (-d^2)) (exponential_derivative_graph d)
  change (Real.exp (-d^2) • GaussianL2QuarticEmbeddingObstruction.classTwo d,
    d • (Real.exp (-d^2) • GaussianL2QuarticEmbeddingObstruction.classTwo d))∈_
  rw [smul_comm d (Real.exp (-d^2))]
  exact hg

theorem gaussian_vacuum_root : GaussianCore.normalizedHermite 0=gaussianRoot 0 := by
  have hv : GaussianCore.normalizedHermite 0=GaussianCore.polynomialL2 1 := by
    simp [GaussianCore.normalizedHermite,GaussianCore.hermiteVector,GaussianCore.hermitePolynomial_zero]
  rw [hv,gaussianRoot]
  simp only [zero_pow (by decide : (2 : ℕ)≠0),neg_zero,Real.exp_zero,one_smul]
  apply Lp.ext
  filter_upwards [GaussianCore.polynomialL2_coeFn 1,(GaussianCore.gaussian_exp_memLp_two 0).coeFn_toLp] with x hp he
  change GaussianL2QuarticEmbeddingObstruction.classTwo 0 x=Real.exp (0*x) at he
  rw [hp,he]
  simp

theorem poisson_vacuum_root (rate : ℝ≥0) (hr : 0<rate) : normalized rate hr 0=rootClass rate 0 := by
  apply Lp.ext
  filter_upwards [rootClass_coeFn rate 0] with n hn
  rw [hn,normalized,scalar_smul_apply rate hr,PoissonCharlierLadder.scalar_apply]
  simp [normalizer,PoissonCharlierLadder.value_zero,rootDensity]

theorem gaussianRoot_vacuum_pairing (d : ℝ) :
    inner ℝ (GaussianCore.normalizedHermite 0) (gaussianRoot d)=Real.exp (-d^2/2) := by
  rw [gaussian_vacuum_root,gaussianRoot_inner]
  simp

theorem transferred_root_vacuum_pairing (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    inner ℝ (GaussianCore.normalizedHermite 0) (gaussianTransfer rate hr (rootClass rate θ))=
      Real.exp (-(displacement rate θ)^2/2) := by
  rw [transfer_coefficient,poisson_vacuum_root,rootClass_inner_sqrtRate,
    displacement,← sqrtRate_eq_sqrt_tilted rate θ]
  simp only [sqrtRate,zero_div,Real.exp_zero,mul_one]
  congr 1
  ring

theorem gaussian_shifted_kernel (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f : GaussianCore.GaussianL2)
    (hf : (f,displacement rate θ • f)∈GaussianCore.closedDerivative.graph) :
    f=inner ℝ (gaussianTransfer rate hr (rootClass rate θ)) f • gaussianTransfer rate hr (rootClass rate θ) := by
  let Q := gaussianTransfer rate hr
  have hg : annihilationGraph rate hr (Q.symm f) (displacement rate θ • Q.symm f) := by
    apply (annihilation_scalar_transfer rate hr _ _).mpr
    simpa only [Q,map_smul,LinearIsometryEquiv.apply_symm_apply] using hf
  have hk := (shifted_annihilation_kernel rate hr θ (Q.symm f)).mp hg
  have he := congrArg Q hk
  simp only [map_smul,LinearIsometryEquiv.apply_symm_apply] at he
  have hp := Q.inner_map_map (rootClass rate θ) (Q.symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at hp
  rw [← hp] at he
  exact he

theorem transferred_root_identification (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    gaussianTransfer rate hr (rootClass rate θ)=gaussianRoot (displacement rate θ) := by
  let d := displacement rate θ
  let v := gaussianTransfer rate hr (rootClass rate θ)
  let c := inner ℝ v (gaussianRoot d)
  have he : gaussianRoot d=c • v := gaussian_shifted_kernel rate hr θ _ (gaussianRoot_derivative_graph d)
  have hi := congrArg (fun f : GaussianCore.GaussianL2 => inner ℝ (GaussianCore.normalizedHermite 0) f) he
  rw [real_inner_smul_right,gaussianRoot_vacuum_pairing,transferred_root_vacuum_pairing] at hi
  have hc : c=1 := by
    have hp : 0<Real.exp (-d^2/2) := Real.exp_pos _
    change Real.exp (-d^2/2)=c*Real.exp (-d^2/2) at hi
    nlinarith
  rw [hc,one_smul] at he
  exact he.symm

theorem displacement_vacuum_physical (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) :
    gaussianDisplacement rate hr θ (GaussianCore.normalizedHermite 0)=gaussianRoot (displacement rate θ) := by
  have hv : (gaussianTransfer (tiltedRate rate θ) (tiltedRate_pos rate hr θ)).symm
      (GaussianCore.normalizedHermite 0)=normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0 := by
    rw [← transfer_normalized (tiltedRate rate θ) (tiltedRate_pos rate hr θ) 0]
    exact LinearIsometryEquiv.symm_apply_apply _ _
  change gaussianTransfer rate hr (gauge rate θ ((gaussianTransfer (tiltedRate rate θ)
    (tiltedRate_pos rate hr θ)).symm (GaussianCore.normalizedHermite 0)))=_
  rw [hv,gauge_vacuum rate hr θ,transferred_root_identification rate hr θ]

theorem gaussian_eigenvector_iff (d : ℝ) (f : GaussianCore.GaussianL2) :
    (f,d • f)∈GaussianCore.closedDerivative.graph ↔ f=inner ℝ (gaussianRoot d) f • gaussianRoot d := by
  constructor
  · intro hf
    obtain ⟨rate,hr,θ,hd⟩ := exists_positive_reference_displacement d
    rw [← hd] at hf
    have he := gaussian_shifted_kernel rate hr θ f hf
    rwa [transferred_root_identification,hd] at he
  · intro hf
    rw [hf]
    have hg := GaussianCore.closedDerivative.graph.smul_mem (inner ℝ (gaussianRoot d) f)
      (gaussianRoot_derivative_graph d)
    rw [smul_comm d (inner ℝ (gaussianRoot d) f)]
    exact hg

end OperatorDerivativeRewrite.Foundation.GaussianCoherentIdentification
