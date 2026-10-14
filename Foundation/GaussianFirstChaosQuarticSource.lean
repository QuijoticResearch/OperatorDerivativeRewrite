import Foundation.BanachQuarticWeightedStability
import Foundation.IBMCubicFirstChaos

/-! An actual infinite-dimensional Gaussian first-chaos L4 source has
weighted coercivity at every nonzero source point. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianFirstChaosQuarticSource
open InfiniteGaussian BanachLpDualityFour BanachLpDualityFourContinuity
open BanachQuarticWeightedStability IBMGaussianSteinMoments
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def classFour (h : CoefficientSpace) : Lp ℝ 4 gaussianProduct :=
  ((firstChaos_hasGaussianLaw h).memLp (by norm_num : (4 : ℝ≥0∞)≠∞)).toLp
    (fun ω => firstChaosEmbedding h ω)

theorem classFour_coeFn (h : CoefficientSpace) :
    classFour h =ᵐ[gaussianProduct] firstChaosEmbedding h :=
  ((firstChaos_hasGaussianLaw h).memLp (by norm_num : (4 : ℝ≥0∞)≠∞)).coeFn_toLp

theorem classFour_norm_fourth (h : CoefficientSpace) : ‖classFour h‖^4=3*‖h‖^4 := by
  rw [← quartic_integral_eq_norm]
  have he : (∫ ω, (classFour h ω)^4 ∂gaussianProduct)=
      ∫ ω, (firstChaosEmbedding h ω)^2*(firstChaosEmbedding h ω)^2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [classFour_coeFn h] with ω hh
    rw [hh]
    ring
  rw [he,firstChaos_square_product,real_inner_self_eq_norm_sq]
  ring

theorem classFour_norm_bounds (h : CoefficientSpace) :
    ‖h‖ ≤ ‖classFour h‖ ∧ ‖classFour h‖ ≤ 2*‖h‖ := by
  have he := classFour_norm_fourth h
  constructor
  · by_contra hn
    have hp := pow_lt_pow_left₀ (lt_of_not_ge hn) (norm_nonneg (classFour h)) (by decide : (4 : ℕ)≠0)
    nlinarith [pow_nonneg (norm_nonneg h) 4]
  · by_contra hn
    have hp := pow_lt_pow_left₀ (lt_of_not_ge hn) (show 0≤2*‖h‖ by positivity) (by decide : (4 : ℕ)≠0)
    nlinarith [pow_nonneg (norm_nonneg h) 4]

def sourceLinear : CoefficientSpace →ₗ[ℝ] Lp ℝ 4 gaussianProduct where
  toFun := classFour
  map_add' h k := by
    apply Lp.ext
    filter_upwards [classFour_coeFn (h+k),classFour_coeFn h,classFour_coeFn k,
      Lp.coeFn_add (classFour h) (classFour k),Lp.coeFn_add (firstChaosEmbedding h) (firstChaosEmbedding k)]
      with ω hh hh1 hh2 ha hb
    rw [hh,ha]
    rw [map_add,hb]
    simpa only [Pi.add_apply] using congrArg₂ (fun a b : ℝ => a+b) hh1 hh2 |>.symm
  map_smul' c h := by
    apply Lp.ext
    filter_upwards [classFour_coeFn (c • h),classFour_coeFn h,
      Lp.coeFn_smul c (classFour h),Lp.coeFn_smul c (firstChaosEmbedding h)] with ω hh hh1 ha hb
    change classFour (c • h) ω=(c • classFour h) ω
    rw [hh,ha]
    rw [map_smul,hb]
    simpa only [Pi.smul_apply,smul_eq_mul] using congrArg (fun a : ℝ => c*a) hh1 |>.symm

def source : CoefficientSpace →L[ℝ] Lp ℝ 4 gaussianProduct :=
  sourceLinear.mkContinuous 2 (fun h => (classFour_norm_bounds h).2)

theorem weighted_source_energy (h k : CoefficientSpace) :
    ‖weightedSource source h k‖^2=‖h‖^2*‖k‖^2+2*(inner ℝ h k)^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ ω, ‖weightedSource source h k ω‖^2 ∂gaussianProduct)=
      ∫ ω, (firstChaosEmbedding h ω)^2*(firstChaosEmbedding k ω)^2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [squareProduct_ae (classFour h) (classFour k),classFour_coeFn h,classFour_coeFn k]
      with ω hp hh hk
    change ‖squareProduct (classFour h) (classFour k) ω‖^2=_
    rw [hp,hh,hk]
    simp only [Real.norm_eq_abs,sq_abs,mul_pow]
  rw [he,firstChaos_square_product]

theorem weighted_source_lower (h k : CoefficientSpace) :
    ‖h‖*‖k‖ ≤ ‖weightedSource source h k‖ := by
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [weighted_source_energy,mul_pow]
  nlinarith [sq_nonneg (inner ℝ h k)]

theorem normal_pairing (h k : CoefficientSpace) :
    normalFour source h k=3*‖h‖^2*inner ℝ h k := by
  rw [normalFour,BanachLpAdjoint.boundedBanachDerivative_apply]
  change (∫ ω, dualityFour (classFour h) ω*classFour k ω ∂gaussianProduct)=_
  calc
    _ = ∫ ω, (firstChaosEmbedding h ω)^3*firstChaosEmbedding k ω ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [dualityFour_ae (classFour h),classFour_coeFn h,classFour_coeFn k] with ω hd hh hk
      rw [hd,hh,hk]
    _ = inner ℝ (cube h) (GaussianTimeSpaceHermite.wick k 1 : GaussianL2) := by
      rw [IBMCubicFirstChaos.wick_one_eq_embedding,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [cube_coeFn h] with ω hh
      rw [hh]
      simp [Real.inner_apply,mul_comm]
    _ = _ := firstChaos_cube_first_inner h k

theorem normal_radial (h : CoefficientSpace) :
    normalFour source h=(3*‖h‖^2) • innerSL ℝ h := by
  ext k
  rw [normal_pairing]
  simp [innerSL_apply_apply]

def normalEquiv : CoefficientSpace ≃ StrongDual ℝ CoefficientSpace :=
  BanachLpDualityFourInfinite.normalFourEquiv source 1 (by norm_num)
    (fun h => by
      change 1*‖h‖≤‖classFour h‖
      simpa only [one_mul] using (classFour_norm_bounds h).1)

theorem inverse_regular_at_nonzero (h : CoefficientSpace) (hh : h≠0)
    (f : StrongDual ℝ CoefficientSpace) :
    ‖h-normalEquiv.symm f‖ ≤ (4/(3*‖h‖^2))*‖normalFour source h-f‖ := by
  have he := inverse_lipschitz_at_weighted_datum source h ‖h‖ (norm_pos_iff.mpr hh)
    (weighted_source_lower h) (normalEquiv.symm f)
  have hs : normalFour source (normalEquiv.symm f)=f := normalEquiv.apply_symm_apply f
  rwa [hs] at he

theorem inverse_regular_at_nonzero_datum (f₀ : StrongDual ℝ CoefficientSpace) (hf₀ : f₀≠0)
    (f : StrongDual ℝ CoefficientSpace) :
    ‖normalEquiv.symm f₀-normalEquiv.symm f‖ ≤
      (4/(3*‖normalEquiv.symm f₀‖^2))*‖f₀-f‖ := by
  have hs : normalFour source (normalEquiv.symm f₀)=f₀ := normalEquiv.apply_symm_apply f₀
  have hn : normalEquiv.symm f₀≠0 := by
    intro hz
    rw [hz,normal_radial] at hs
    have he : f₀=0 := by simpa using hs.symm
    exact hf₀ he
  have hb := inverse_regular_at_nonzero (normalEquiv.symm f₀) hn f
  rwa [hs] at hb

end OperatorDerivativeRewrite.Foundation.GaussianFirstChaosQuarticSource
