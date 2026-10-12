import Foundation.GaussianBrownianSobolevField

/-! Predictable representation of genuine finite Brownian quadratic cylinders.
Times may coincide and their order is arbitrary. This is not full polynomial PRP. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticCylinders
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianPredictableFull GaussianSensitivityCore GaussianQuadraticRepresentation
open GaussianTimePolynomialPairing SeparableHilbertEmbedding GaussianBrownianBracket
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def brownianProduct (s t : ℝ≥0) : polynomialCylindricalDomain :=
  polynomialProduct (firstChaosPolynomial (hilbertEmbedding TimeHilbert (timeVector s)))
    (firstChaosPolynomial (hilbertEmbedding TimeHilbert (timeVector t)))

theorem brownianProduct_coeFn (s t : ℝ≥0) :
    (brownianProduct s t : GaussianL2) =ᵐ[gaussianProduct] fun ω => process s ω * process t ω := by
  filter_upwards [polynomialProductL2_coeFn
    (firstChaosPolynomial (hilbertEmbedding TimeHilbert (timeVector s)))
    (firstChaosPolynomial (hilbertEmbedding TimeHilbert (timeVector t))),
    firstChaosPolynomial_coeFn (hilbertEmbedding TimeHilbert (timeVector s)),
    firstChaosPolynomial_coeFn (hilbertEmbedding TimeHilbert (timeVector t))] with ω hp hs ht
  change (brownianProduct s t : GaussianL2) ω = _ at hp
  rw [hp, hs, ht]
  rfl

def orderedCrossField (s t : ℝ≥0) : fullPredictable :=
  (2 : ℝ) • quadraticIntegrand s +
    pastStep s t (fun _ : Fin 1 => s) (fun _ => le_rfl) (MvPolynomial.X 0)

theorem orderedCrossField_integral (s t : ℝ≥0) (hst : s ≤ t) :
    itoIntegral (orderedCrossField s t) = (brownianProduct s t : GaussianL2) - (s : ℝ) • gaussianOne := by
  rw [orderedCrossField, map_add, map_smul, integral_quadraticIntegrand, smul_smul,
    ito_pastStep s t hst]
  norm_num only [one_div, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (terminalSquare s)
    (incrementProductL2 (fun _ : Fin 1 => s) (MvPolynomial.X 0) s t),
    terminalSquare_coeFn s,
    incrementProductL2_coeFn (fun _ : Fin 1 => s) (MvPolynomial.X 0) s t,
    Lp.coeFn_sub (brownianProduct s t : GaussianL2) ((s : ℝ) • gaussianOne),
    brownianProduct_coeFn s t, Lp.coeFn_smul (s : ℝ) gaussianOne, gaussianOne_coeFn]
    with ω ha hf hi hs hp hsm h1
  rw [ha, hs]
  simp only [Pi.add_apply, Pi.sub_apply, hf, hi, MvPolynomial.eval_X, hp, hsm,
    Pi.smul_apply, h1, smul_eq_mul, mul_one]
  ring

def crossField (s t : ℝ≥0) : fullPredictable := orderedCrossField (min s t) (max s t)

theorem crossField_integral (s t : ℝ≥0) :
    itoIntegral (crossField s t) =
      (brownianProduct s t : GaussianL2) - (min (s : ℝ) (t : ℝ)) • gaussianOne := by
  have h := orderedCrossField_integral (min s t) (max s t) (min_le_max)
  have he : (brownianProduct (min s t) (max s t) : GaussianL2) = brownianProduct s t := by
    apply Lp.ext
    filter_upwards [brownianProduct_coeFn (min s t) (max s t), brownianProduct_coeFn s t]
      with ω hm hs
    rw [hm, hs]
    rcases le_total s t with hst | hts
    · rw [min_eq_left hst, max_eq_right hst]
    · rw [min_eq_right hts, max_eq_left hts, mul_comm]
  simpa only [crossField, he, NNReal.coe_min] using h

variable {ι : Type*} [Fintype ι]

def quadraticCylinder (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) : GaussianL2 :=
  c • gaussianOne + (∑ i, a i • wienerL2 (t i)) +
    ∑ i, ∑ j, b i j • (brownianProduct (t i) (t j) : GaussianL2)

def quadraticCylinderMean (c : ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) : ℝ :=
  c + ∑ i, ∑ j, b i j * min (t i : ℝ) (t j : ℝ)

def quadraticCylinderIntegrand (a : ι → ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) : fullPredictable :=
  (∑ i, a i • deterministicInterval (t i)) + ∑ i, ∑ j, b i j • crossField (t i) (t j)

/-- An explicit predictable representation, including repeated/zero times and
singular observation covariance. No orthogonality of observations is assumed. -/
theorem quadraticCylinder_representation (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ)
    (t : ι → ℝ≥0) :
    itoIntegral (quadraticCylinderIntegrand a b t) =
      quadraticCylinder c a b t - quadraticCylinderMean c b t • gaussianOne := by
  simp only [quadraticCylinderIntegrand, map_add, map_sum, map_smul,
    integral_deterministicInterval, crossField_integral, smul_sub, smul_smul,
    Finset.sum_sub_distrib, ← Finset.sum_smul, quadraticCylinder, quadraticCylinderMean, add_smul]
  abel

theorem quadraticCylinder_mean (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) :
    (∫ ω, quadraticCylinder c a b t ω ∂gaussianProduct) = quadraticCylinderMean c b t := by
  have h := itoIntegral_centered (quadraticCylinderIntegrand a b t)
  rw [quadraticCylinder_representation c a b t] at h
  rw [← gaussianOne_inner_eq_integral, inner_sub_right, inner_smul_right,
    GaussianDeterministicGraphCore.gaussianOne_inner_self, mul_one,
    gaussianOne_inner_eq_integral] at h
  exact sub_eq_zero.mp h

theorem quadraticCylinder_mem_derivative_domain (c : ℝ) (a : ι → ℝ)
    (b : ι → ι → ℝ) (t : ι → ℝ≥0) :
    quadraticCylinder c a b t ∈ closedCylindricalDerivative.domain := by
  apply closedCylindricalDerivative.domain.add_mem
  · apply closedCylindricalDerivative.domain.add_mem
    · exact LinearPMap.mem_domain_iff.mpr ⟨0, closedDerivative_constant_graph c⟩
    · apply closedCylindricalDerivative.domain.sum_mem
      intro i _
      apply closedCylindricalDerivative.domain.smul_mem
      exact LinearPMap.mem_domain_iff.mpr ⟨_,
        GaussianDeterministicIntegral.firstChaos_closedDerivative_graph (timeVector (t i))⟩
  · apply closedCylindricalDerivative.domain.sum_mem
    intro i _
    apply closedCylindricalDerivative.domain.sum_mem
    intro j _
    exact closedCylindricalDerivative.domain.smul_mem _
      (closedCylindricalDerivative_core_mem (brownianProduct (t i) (t j)))

def quadraticCylinderDomain (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ) (t : ι → ℝ≥0) :
    closedCylindricalDerivative.domain :=
  ⟨quadraticCylinder c a b t, quadraticCylinder_mem_derivative_domain c a b t⟩

theorem predictableAdjoint_constant (c : ℝ) :
    GaussianPredictableAdjoint.predictableAdjoint (c • gaussianOne) = 0 := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ (itoIntegral.toContinuousLinearMap.adjoint (c • gaussianOne)) u = inner ℝ 0 u
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left,
    gaussianOne_inner_eq_integral]
  change c * (∫ ω, itoIntegral u ω ∂gaussianProduct) = inner ℝ 0 u
  rw [itoIntegral_centered]
  simp

theorem predictableProjection_quadraticCylinder (c : ℝ) (a : ι → ℝ)
    (b : ι → ι → ℝ) (t : ι → ℝ≥0) :
    GaussianPredictableAdjoint.predictableProjection
      (closedCylindricalDerivative (quadraticCylinderDomain c a b t)) =
        quadraticCylinderIntegrand a b t := by
  have he : quadraticCylinder c a b t = itoIntegral (quadraticCylinderIntegrand a b t) +
      quadraticCylinderMean c b t • gaussianOne :=
    sub_eq_iff_eq_add.mp (quadraticCylinder_representation c a b t).symm
  have hp := GaussianPredictableAdjoint.predictableAdjoint_eq_projected_derivative
    (quadraticCylinderDomain c a b t)
  change GaussianPredictableAdjoint.predictableAdjoint (quadraticCylinder c a b t) = _ at hp
  rw [he, map_add, GaussianPredictableAdjoint.predictableAdjoint_integral,
    predictableAdjoint_constant, add_zero] at hp
  exact hp.symm

/-- Clark--Ocone for all finite Brownian quadratic cylinders, using the actual
full closed derivative, actual expectation, and actual predictable projection. -/
theorem quadraticCylinder_clarkOcone (c : ℝ) (a : ι → ℝ) (b : ι → ι → ℝ)
    (t : ι → ℝ≥0) :
    quadraticCylinder c a b t =
      (∫ ω, quadraticCylinder c a b t ω ∂gaussianProduct) • gaussianOne +
      itoIntegral (GaussianPredictableAdjoint.predictableProjection
        (closedCylindricalDerivative (quadraticCylinderDomain c a b t))) := by
  rw [quadraticCylinder_mean, predictableProjection_quadraticCylinder,
    quadraticCylinder_representation]
  abel

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticCylinders
