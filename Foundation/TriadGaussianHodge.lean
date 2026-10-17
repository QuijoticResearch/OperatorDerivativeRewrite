import Foundation.DictionaryTriadPotential
import Foundation.DivergenceKernelContrast
import Foundation.GaussianSourceHodge

/-! An explicit Gaussian/Hodge realization of the fixed-c triad rotation.
The coordinate law here is Gaussian; no invariant NS process is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.TriadGaussianHodge
open InfiniteGaussian GaussianTimeFieldNorm DivergenceKernelContrast
open GaussianSourceHodge GaussianNumberSectors GaussianDivergenceRecovery
set_option backward.isDefEq.respectTransparency false

def direction (n : ℕ) : CoefficientSpace := lp.single 2 n (1 : ℝ)
def coordinate (n : ℕ) : GaussianL2 := firstChaosEmbedding (direction n)

theorem coordinate_eq_original (n : ℕ) : coordinate n=coordinateL2 n := by
  simp [coordinate,direction,firstChaos_single]

theorem coordinate_coeFn (n : ℕ) :
    coordinate n =ᵐ[gaussianProduct] InfiniteGaussian.coordinate n := by
  rw [coordinate_eq_original]
  exact coordinateL2_coeFn n

theorem direction_norm_sq (n : ℕ) : ‖direction n‖^2=1 := by
  simp [direction,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]

theorem direction_inner (n m : ℕ) :
    inner ℝ (direction n) (direction m)=if n=m then 1 else 0 := by
  rw [direction,direction,lp.inner_single_left]
  simp [lp.single_apply,Pi.single_apply]

def component (n : ℕ) : GaussianVectorL2 →L[ℝ] GaussianL2 :=
  (innerSL ℝ (direction n)).compLpL 2 gaussianProduct

theorem component_tensor (n : ℕ) (h : CoefficientSpace) (f : GaussianL2) :
    component n (scalarTensor h f)=inner ℝ (direction n) h • f := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ (direction n)).coeFn_compLpL (scalarTensor h f),
    scalarTensor_coeFn h f,Lp.coeFn_smul (inner ℝ (direction n) h) f] with ω hc ht hs
  change ((innerSL ℝ (direction n)).compLpL 2 gaussianProduct (scalarTensor h f)) ω=_
  rw [hc,ht,hs]
  simp [smul_eq_mul,mul_comm]

def rotation (c : ℝ) : GaussianVectorL2 := c • skewField (direction 0) (direction 1)

theorem rotation_coeFn (c : ℝ) : rotation c =ᵐ[gaussianProduct]
    fun ω => c • (coordinate 1 ω • direction 0-coordinate 0 ω • direction 1) := by
  filter_upwards [Lp.coeFn_smul c (skewField (direction 0) (direction 1)),
    Lp.coeFn_sub (scalarTensor (direction 0) (coordinate 1))
      (scalarTensor (direction 1) (coordinate 0)),
    scalarTensor_coeFn (direction 0) (coordinate 1),
    scalarTensor_coeFn (direction 1) (coordinate 0)] with ω hc hs h0 h1
  change (c • skewField (direction 0) (direction 1)) ω=_
  rw [hc]
  change c • ((scalarTensor (direction 0) (coordinate 1)-
    scalarTensor (direction 1) (coordinate 0)) ω)=_
  rw [hs]
  simp only [Pi.sub_apply]
  rw [h0,h1]

theorem component_rotation_zero (c : ℝ) : component 0 (rotation c)=c • coordinate 1 := by
  rw [rotation,map_smul,skewField,map_sub,component_tensor,component_tensor]
  simp [direction_inner,direction_norm_sq,coordinate]

theorem component_rotation_one (c : ℝ) : component 1 (rotation c)=(-c) • coordinate 0 := by
  rw [rotation,map_smul,skewField,map_sub,component_tensor,component_tensor]
  simp [direction_inner,direction_norm_sq,coordinate,smul_neg,neg_smul]

theorem component_rotation_other (c : ℝ) (n : ℕ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    component n (rotation c)=0 := by
  rw [rotation,map_smul,skewField,map_sub,component_tensor,component_tensor]
  simp [direction_inner,hn0,hn1]

/-- Actual L2 representatives have precisely the finite triad rotation's coordinates. -/
theorem components_equal_triad (c : ℝ) : ∀ᵐ ω ∂gaussianProduct,
    component 0 (rotation c) ω=
      DictionaryTriadPotential.drift 0 ![coordinate 0 ω,coordinate 1 ω,c] 0 ∧
    component 1 (rotation c) ω=
      DictionaryTriadPotential.drift 0 ![coordinate 0 ω,coordinate 1 ω,c] 1 := by
  rw [component_rotation_zero,component_rotation_one]
  filter_upwards [Lp.coeFn_smul c (coordinate 1),Lp.coeFn_smul (-c) (coordinate 0)]
    with ω h0 h1
  simp only [Pi.smul_apply,smul_eq_mul] at h0 h1
  constructor
  · change (c • coordinate 1) ω=coordinate 1 ω*c-0*coordinate 0 ω
    rw [h0]
    ring
  · change ((-c) • coordinate 0) ω= -coordinate 0 ω*c-0*coordinate 1 ω
    rw [h1]
    ring

theorem rotation_norm_sq (c : ℝ) : ‖rotation c‖^2=2*c^2 := by
  rw [rotation,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,skewField_norm_sq,
    direction_norm_sq,direction_norm_sq,direction_inner]
  norm_num
  ring

theorem rotation_nonzero (c : ℝ) (hc : c ≠ 0) : rotation c ≠ 0 := by
  intro hz
  have h := rotation_norm_sq c
  rw [hz,norm_zero] at h
  nlinarith [sq_pos_of_ne_zero hc]

theorem rotation_divergence_zero (c : ℝ) : (rotation c,0) ∈ hilbertDivergence.graph := by
  have h := hilbertDivergence.graph.smul_mem c
    (skewField_divergence_zero (direction 0) (direction 1))
  simpa only [rotation,Prod.smul_mk,smul_zero] using h

theorem rotation_orthogonal (c : ℝ) : rotation c ∈ gradientRangeᗮ :=
  (gradientRange_orthogonal_iff_divergence_zero _).mpr (rotation_divergence_zero c)

theorem rotation_gradientProjection_zero (c : ℝ) : gradientProjection (rotation c)=0 := by
  change gradientRange.starProjection (rotation c)=0
  apply gradientRange.eq_starProjection_of_mem_orthogonal gradientRange.zero_mem
  simpa only [sub_zero] using rotation_orthogonal c

theorem rotation_recovery_adjoint_zero (c : ℝ) : recoveryOperator.adjoint (rotation c)=0 :=
  recovery_adjoint_kernel_zero _ (rotation_divergence_zero c)

theorem rotation_not_gradient (c : ℝ) (hc : c ≠ 0) : rotation c ∉ gradientRange := by
  intro h
  have hs := Submodule.starProjection_eq_self_iff.mpr h
  change gradientProjection (rotation c)=rotation c at hs
  rw [rotation_gradientProjection_zero] at hs
  exact rotation_nonzero c hc hs.symm

theorem no_closed_gradient_potential (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ f : GaussianL2, (f,rotation c) ∈ closedCylindricalDerivative.graph := by
  intro h
  exact rotation_not_gradient c hc ((mem_gradientRange_iff _).mpr h)

theorem gradient_pairing_zero (c : ℝ) {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) : inner ℝ g (rotation c)=0 := by
  simpa only [inner_zero_right] using graph_duality hf (rotation_divergence_zero c)

theorem weak_integral_zero (c : ℝ) {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) :
    (∫ ω, inner ℝ (g ω) (rotation c ω) ∂gaussianProduct)=0 := by
  rw [← L2_inner_eq_integral]
  exact gradient_pairing_zero c hf

/-- Zero is the closest closed-gradient field, with a quantitative nonzero residual. -/
theorem gradient_error_identity (c : ℝ) {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) :
    ‖rotation c-g‖^2=2*c^2+‖g‖^2 := by
  have ho : inner ℝ (rotation c) g=0 := by
    rw [real_inner_comm]
    exact gradient_pairing_zero c hf
  simp only [norm_sub_sq_real,ho,rotation_norm_sq,
    mul_zero,sub_zero]

end OperatorDerivativeRewrite.Foundation.TriadGaussianHodge
