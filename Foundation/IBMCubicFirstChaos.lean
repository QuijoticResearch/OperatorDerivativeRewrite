import Foundation.IBMGaussianSteinMoments
import Foundation.GaussianQuarticWick

/-! Actual cubic IBM spatial correction: Wick decomposition and projection
onto the existing complete first chaos, for arbitrary source directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace OperatorDerivativeRewrite.Foundation.IBMCubicFirstChaos
open InfiniteGaussian IBMGaussianSteinMoments GaussianTimeSpaceHermite
open GaussianPastFirstChaos

theorem wick_one_eq_embedding (h : CoefficientSpace) :
    (wick h 1 : GaussianL2) = firstChaosEmbedding h := by
  apply Lp.ext
  filter_upwards [core_coeFn h (‖h‖^2) 1] with ω hω
  simpa only [wick, value_one] using hω

theorem adjoint_cube (h : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (cube h) = (3*‖h‖^2) • h := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (cube h) (firstChaosEmbedding k) = _
  rw [← wick_one_eq_embedding, firstChaos_cube_first_inner, real_inner_smul_left]

/-- This class is independently realized by cubic polarization, not defined
through the desired first-chaos projection. -/
def mixedCube (u v : CoefficientSpace) : GaussianL2 :=
  (1/6 : ℝ) • (cube (u+v) + cube (u-v) - (2 : ℝ) • cube u)

theorem mixedCube_coeFn (u v : CoefficientSpace) :
    mixedCube u v =ᵐ[gaussianProduct]
      fun ω => firstChaosEmbedding u ω * (firstChaosEmbedding v ω)^2 := by
  filter_upwards [Lp.coeFn_smul (1/6 : ℝ) (cube (u+v)+cube (u-v)-(2 : ℝ)•cube u),
    Lp.coeFn_sub (cube (u+v)+cube (u-v)) ((2 : ℝ)•cube u),
    Lp.coeFn_add (cube (u+v)) (cube (u-v)), Lp.coeFn_smul (2 : ℝ) (cube u),
    cube_coeFn (u+v), cube_coeFn (u-v), cube_coeFn u,
    Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v),
    Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)]
      with ω hs hd ha h2 hp hm hu huv hsub
  rw [mixedCube, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  simp only [Pi.sub_apply]
  rw [ha, h2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hp, hm, hu, map_add, map_sub, huv, hsub]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem mixedCube_memLp (u v : CoefficientSpace) :
    MemLp (fun ω => firstChaosEmbedding u ω*(firstChaosEmbedding v ω)^2) 2 gaussianProduct :=
  (Lp.memLp (mixedCube u v)).ae_eq (mixedCube_coeFn u v)

theorem adjoint_mixedCube (u v : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (mixedCube u v) =
      ‖v‖^2 • u + (2*inner ℝ u v) • v := by
  simp only [mixedCube, map_smul, map_add, map_sub, adjoint_cube,
    norm_add_sq_real, norm_sub_sq_real]
  module

def correction (u v w : CoefficientSpace) : GaussianL2 :=
  mixedCube u v + (1/2 : ℝ) • mixedCube w u

def coefficient (u v w : CoefficientSpace) : CoefficientSpace :=
  (‖v‖^2 + inner ℝ u w) • u + (2*inner ℝ u v) • v + ((1/2 : ℝ)*‖u‖^2) • w

theorem correction_coeFn (u v w : CoefficientSpace) :
    correction u v w =ᵐ[gaussianProduct] fun ω =>
      firstChaosEmbedding u ω*(firstChaosEmbedding v ω)^2 +
        (1/2 : ℝ)*(firstChaosEmbedding u ω)^2*firstChaosEmbedding w ω := by
  filter_upwards [Lp.coeFn_add (mixedCube u v) ((1/2 : ℝ)•mixedCube w u),
    Lp.coeFn_smul (1/2 : ℝ) (mixedCube w u), mixedCube_coeFn u v,
    mixedCube_coeFn w u] with ω ha hs h1 h2
  rw [correction, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, h1, h2]
  ring

theorem correction_memLp (u v w : CoefficientSpace) :
    MemLp (fun ω => firstChaosEmbedding u ω*(firstChaosEmbedding v ω)^2 +
      (1/2 : ℝ)*(firstChaosEmbedding u ω)^2*firstChaosEmbedding w ω) 2 gaussianProduct :=
  (Lp.memLp (correction u v w)).ae_eq (correction_coeFn u v w)

/-- The true Hilbert adjoint identifies the first-chaos vector for the cubic
correction. No inverse covariance matrix or independence is assumed. -/
theorem adjoint_correction (u v w : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (correction u v w) = coefficient u v w := by
  simp only [correction, map_add, map_smul, adjoint_mixedCube, coefficient]
  rw [real_inner_comm w u]
  module

theorem projection_correction (u v w : CoefficientSpace) :
    GaussianPastFirstChaos.projection (correction u v w) = firstChaosEmbedding (coefficient u v w) := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint (correction u v w)) = _
  rw [adjoint_correction]

/-- The remainder is orthogonal to the entire first-chaos range. -/
theorem correction_residual_orthogonal (u v w : CoefficientSpace) :
    correction u v w - firstChaosEmbedding (coefficient u v w) ∈
      firstChaosEmbedding.toLinearMap.rangeᗮ := by
  rw [← projection_correction]
  exact projection_residual_orthogonal _

theorem wick_mem_sector (h : CoefficientSpace) (n : ℕ) :
    (wick h n : GaussianL2) ∈ GaussianNumberSectors.sector n := by
  apply (GaussianNumberSectors.mem_sector n _).mpr
  cases n with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · have hg := closedCylindricalDerivative_core_graph (wick h 0)
      simpa only [wick, core_zero_derivative] using hg
    · simpa using
        hilbertDivergence.graph.zero_mem
  | succ n =>
    refine ⟨polynomialDerivative (wick h (n+1)),
      closedCylindricalDerivative_core_graph (wick h (n+1)), ?_⟩
    have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
      (cylindricalDivergence_rank_graph (wick h n) h)
    rw [← wick_raising] at hg
    have hs := hilbertDivergence.graph.smul_mem (n+1 : ℝ) hg
    rw [show polynomialDerivative (wick h (n+1)) =
      (n+1 : ℝ) • scalarTensor h (wick h n) from core_derivative h (‖h‖^2) n]
    simpa using hs

def mixedWick (u v : CoefficientSpace) : GaussianL2 :=
  (1/6 : ℝ) • ((wick (u+v) 3 : GaussianL2) + (wick (u-v) 3 : GaussianL2) -
    (2 : ℝ) • (wick u 3 : GaussianL2))

theorem mixedCube_decomposition (u v : CoefficientSpace) :
    mixedCube u v = mixedWick u v +
      firstChaosEmbedding (‖v‖^2 • u + (2*inner ℝ u v) • v) := by
  simp only [mixedCube, mixedWick, cube, wick_one_eq_embedding,
    map_add, map_smul, norm_add_sq_real, norm_sub_sq_real, map_sub]
  module

def thirdPart (u v w : CoefficientSpace) : GaussianL2 := mixedWick u v + (1/2 : ℝ)•mixedWick w u

theorem correction_wick_decomposition (u v w : CoefficientSpace) :
    correction u v w = thirdPart u v w + firstChaosEmbedding (coefficient u v w) := by
  simp only [correction, thirdPart, mixedCube_decomposition, coefficient,
    map_add, map_smul, smul_add]
  rw [real_inner_comm w u]
  module

theorem thirdPart_mem_thirdChaos (u v w : CoefficientSpace) :
    thirdPart u v w ∈ GaussianNumberSectors.sector 3 := by
  have hm (h k : CoefficientSpace) : mixedWick h k ∈ GaussianNumberSectors.sector 3 :=
    (GaussianNumberSectors.sector 3).smul_mem _
      ((GaussianNumberSectors.sector 3).sub_mem
        ((GaussianNumberSectors.sector 3).add_mem (wick_mem_sector (h+k) 3) (wick_mem_sector (h-k) 3))
        ((GaussianNumberSectors.sector 3).smul_mem _ (wick_mem_sector h 3)))
  exact (GaussianNumberSectors.sector 3).add_mem (hm u v)
    ((GaussianNumberSectors.sector 3).smul_mem _ (hm w u))

theorem cube_mem_polynomialDomain (h : CoefficientSpace) : cube h ∈ polynomialCylindricalDomain :=
  polynomialCylindricalDomain.add_mem (wick h 3).property
    (polynomialCylindricalDomain.smul_mem _ (wick h 1).property)

theorem mixedCube_mem_polynomialDomain (u v : CoefficientSpace) :
    mixedCube u v ∈ polynomialCylindricalDomain :=
  polynomialCylindricalDomain.smul_mem _
    (polynomialCylindricalDomain.sub_mem
      (polynomialCylindricalDomain.add_mem (cube_mem_polynomialDomain (u+v))
        (cube_mem_polynomialDomain (u-v)))
      (polynomialCylindricalDomain.smul_mem _ (cube_mem_polynomialDomain u)))

def correctionCore (u v w : CoefficientSpace) : polynomialCylindricalDomain :=
  ⟨correction u v w, polynomialCylindricalDomain.add_mem (mixedCube_mem_polynomialDomain u v)
    (polynomialCylindricalDomain.smul_mem _ (mixedCube_mem_polynomialDomain w u))⟩

/-- Actual source IBP identifies the first-chaos adjoint coefficient with
the Bochner expectation of the full polynomial source derivative. -/
theorem adjoint_eq_mean_derivative (p : polynomialCylindricalDomain) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (p : GaussianL2) =
      ∫ ω, polynomialDerivative p ω ∂gaussianProduct := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (p : GaussianL2) (firstChaosEmbedding k) = _
  have hi : Integrable (fun ω => polynomialDerivative p ω) gaussianProduct :=
    (Lp.memLp (polynomialDerivative p)).integrable (by norm_num)
  rw [L2_inner_eq_integral]
  calc
    _ = ∫ ω, (p : GaussianL2) ω * firstChaosEmbedding k ω ∂gaussianProduct := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by simp [Real.inner_apply, mul_comm]
    _ = ∫ ω, inner ℝ (polynomialDerivative p ω) k ∂gaussianProduct :=
      (polynomialDerivative_stein p k).symm
    _ = _ := by
      have he := (innerSL ℝ k).integral_comp_comm hi
      change (∫ ω, inner ℝ k (polynomialDerivative p ω) ∂gaussianProduct) =
        inner ℝ k (∫ ω, polynomialDerivative p ω ∂gaussianProduct) at he
      simpa only [real_inner_comm] using he

theorem correction_closedDerivative_graph (u v w : CoefficientSpace) :
    (correction u v w, polynomialDerivative (correctionCore u v w)) ∈
      closedCylindricalDerivative.graph :=
  closedCylindricalDerivative_core_graph (correctionCore u v w)

theorem mean_derivative_correction (u v w : CoefficientSpace) :
    (∫ ω, polynomialDerivative (correctionCore u v w) ω ∂gaussianProduct) = coefficient u v w := by
  rw [← adjoint_eq_mean_derivative]
  exact adjoint_correction u v w

end OperatorDerivativeRewrite.Foundation.IBMCubicFirstChaos
