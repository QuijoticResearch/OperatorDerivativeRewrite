import Foundation.InfiniteGaussianLaw
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

/-! Finite joint Gaussian laws and isonormal covariance of the actual first-chaos process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- All infinite-series limits are centered, as a consequence of their proved law. -/
theorem firstChaos_integral (h : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding h ω ∂gaussianProduct) = 0 := by
  have hi := integral_map (μ := gaussianProduct)
    (Lp.stronglyMeasurable (firstChaosEmbedding h)).aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  simpa [firstChaos_law, integral_id_gaussianReal] using hi.symm

/-- Actual product expectation equals the ℓ² inner product. -/
theorem firstChaos_product_integral (h k : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding h ω * firstChaosEmbedding k ω ∂gaussianProduct) =
      inner ℝ h k := by
  rw [← firstChaos_inner, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by simp [mul_comm])

/-- Exact isonormal covariance, with no independence hypothesis on h and k. -/
theorem firstChaos_covariance (h k : CoefficientSpace) :
    cov[firstChaosEmbedding h, firstChaosEmbedding k; gaussianProduct] = inner ℝ h k := by
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _)]
  simp only [firstChaos_integral, mul_zero, sub_zero]
  change (∫ ω, firstChaosEmbedding h ω * firstChaosEmbedding k ω ∂gaussianProduct) = _
  exact firstChaos_product_integral h k

/-- The zero vector has the degenerate Gaussian law, namely a point mass at zero. -/
theorem firstChaos_zero_law :
    gaussianProduct.map (firstChaosEmbedding (0 : CoefficientSpace)) = Measure.dirac 0 := by
  rw [firstChaos_law]
  simp

/-- Linearity of the actual representatives holds almost everywhere. -/
theorem firstChaos_add_ae (h k : CoefficientSpace) :
    firstChaosEmbedding (h + k) =ᵐ[gaussianProduct]
      fun ω => firstChaosEmbedding h ω + firstChaosEmbedding k ω := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (firstChaosEmbedding h) (firstChaosEmbedding k)] with ω hw
  exact hw

theorem firstChaos_smul_ae (a : ℝ) (h : CoefficientSpace) :
    firstChaosEmbedding (a • h) =ᵐ[gaussianProduct]
      fun ω => a * firstChaosEmbedding h ω := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul a (firstChaosEmbedding h)] with ω hw
  exact hw

variable {ι : Type*} [Fintype ι]

/-- A finite family of actual first-chaos random variables; arbitrary dependencies are allowed. -/
def firstChaosFamily (h : ι → CoefficientSpace) (ω : SampleSpace) : ι → ℝ :=
  fun i => firstChaosEmbedding (h i) ω

/-- Every finite linear combination has the actual isometric extension as its L² class. -/
theorem firstChaos_linearCombination_ae (h : ι → CoefficientSpace) (a : ι → ℝ) :
    firstChaosEmbedding (∑ i, a i • h i) =ᵐ[gaussianProduct]
      fun ω => ∑ i, a i * firstChaosEmbedding (h i) ω := by
  classical
  rw [map_sum]
  simp only [map_smul]
  have hc (i : ι) := Lp.coeFn_smul (a i) (firstChaosEmbedding (h i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => a i • firstChaosEmbedding (h i)),
    ae_all_iff.2 hc] with ω hs ha
  simp only [Finset.sum_apply] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Pi.smul_apply, smul_eq_mul] using ha i

variable [DecidableEq ι]

/-- Continuous linear projections of a finite family are genuine weighted first-chaos sums. -/
theorem firstChaosFamily_linear_ae (h : ι → CoefficientSpace) (L : (ι → ℝ) →L[ℝ] ℝ) :
    (fun ω => L (firstChaosFamily h ω)) =ᵐ[gaussianProduct]
      firstChaosEmbedding (∑ i, L (Pi.single i 1) • h i) := by
  classical
  have hl (y : ι → ℝ) : L y = ∑ i, L (Pi.single i 1) * y i := by
    nth_rw 1 [← LinearMap.sum_single_apply (fun _ : ι => ℝ) y]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (y i) = y i • (Pi.single i (1 : ℝ)) := by
      ext j
      by_cases hij : j = i <;> simp [hij]
    rw [he, map_smul, smul_eq_mul, mul_comm]
  filter_upwards [firstChaos_linearCombination_ae h (fun i => L (Pi.single i 1))]
    with ω hw
  rw [hw]
  exact hl _

/-- Exact laws of all linear projections, including zero and linearly dependent families. -/
theorem firstChaosFamily_linear_law (h : ι → CoefficientSpace) (L : (ι → ℝ) →L[ℝ] ℝ) :
    gaussianProduct.map (fun ω => L (firstChaosFamily h ω)) =
      gaussianReal 0 (NNReal.mk (‖∑ i, L (Pi.single i 1) • h i‖ ^ 2) (sq_nonneg _)) := by
  classical
  rw [Measure.map_congr (firstChaosFamily_linear_ae h L), firstChaos_law]

omit [Fintype ι] [DecidableEq ι] in
/-- Joint Gaussianity for every finite family, without orthogonality or rank assumptions. -/
theorem firstChaosFamily_hasGaussianLaw [Finite ι] (h : ι → CoefficientSpace) :
    HasGaussianLaw (firstChaosFamily h) gaussianProduct := by
  classical
  let := Fintype.ofFinite ι
  have hm : Measurable (firstChaosFamily h) :=
    Measurable.of_eval (fun i => (Lp.stronglyMeasurable (firstChaosEmbedding (h i))).measurable)
  refine ⟨hm.aemeasurable, isGaussian_of_map_eq_gaussianReal (fun L => ?_)⟩
  refine ⟨0, NNReal.mk (‖∑ i, L (Pi.single i 1) • h i‖ ^ 2) (sq_nonneg _), ?_⟩
  rw [Measure.map_map L.measurable hm]
  exact firstChaosFamily_linear_law h L

omit [Fintype ι] [DecidableEq ι] in
/-- The covariance matrix of every finite family is its Gram matrix. -/
theorem firstChaosFamily_covariance (h : ι → CoefficientSpace) (i j : ι) :
    cov[(fun ω => firstChaosFamily h ω i), (fun ω => firstChaosFamily h ω j);
      gaussianProduct] = inner ℝ (h i) (h j) :=
  firstChaos_covariance (h i) (h j)

/-- Agreement with the original coordinate classes. -/
theorem firstChaos_unit (n : ℕ) : firstChaosEmbedding (lp.single 2 n (1 : ℝ)) =
    coordinateL2 n := by
  simp [firstChaos_single]

/-- Unit coefficient families reproduce the verified finite Gaussian marginals. -/
theorem firstChaosFamily_unit_law (s : Finset ℕ) :
    gaussianProduct.map (firstChaosFamily (fun i : s => lp.single 2 i.val (1 : ℝ))) =
      FiniteGaussian.productGaussian s := by
  have he : firstChaosFamily (fun i : s => lp.single 2 i.val (1 : ℝ)) =ᵐ[gaussianProduct]
      finiteProjection s := by
    have hc (i : s) := coordinateL2_coeFn i.val
    filter_upwards [ae_all_iff.2 hc] with ω hw
    funext i
    simpa only [firstChaosFamily, firstChaos_unit, finiteProjection, coordinate,
      Finset.restrict] using hw i
  rw [Measure.map_congr he]
  exact (finiteProjection_measurePreserving s).map_eq

omit [Fintype ι] [DecidableEq ι] in
/-- The variance equals the squared coefficient norm, including the zero vector. -/
theorem firstChaos_variance (h : CoefficientSpace) :
    Var[firstChaosEmbedding h; gaussianProduct] = ‖h‖ ^ 2 := by
  rw [← covariance_self (Lp.stronglyMeasurable _).aemeasurable, firstChaos_covariance,
    real_inner_self_eq_norm_sq]

omit [Fintype ι] [DecidableEq ι] in
/-- Finite-support coefficient vectors give the actual finite coordinate sums almost everywhere. -/
theorem firstChaos_finiteSupport_ae (s : Finset ℕ) (a : ℕ → ℝ) :
    firstChaosEmbedding (∑ n ∈ s, lp.single 2 n (a n)) =ᵐ[gaussianProduct] weightedSum a s := by
  rw [firstChaos_finiteSum]
  exact weightedSumL2_coeFn a s

omit [Fintype ι] [DecidableEq ι] in
/-- Correlated finite-support families have exactly the pushforward law of the existing
finite Gaussian coordinates by their coefficient matrix; singular matrices are allowed. -/
theorem firstChaosFamily_finiteCoordinates_law [Finite ι] (s : Finset ℕ) (a : ι → s → ℝ) :
    gaussianProduct.map (firstChaosFamily
      (fun i => ∑ j : s, a i j • lp.single 2 j.val (1 : ℝ))) =
      (FiniteGaussian.productGaussian s).map
        (fun x : s → ℝ => fun i => ∑ j, a i j * x j) := by
  classical
  let := Fintype.ofFinite ι
  have hc (j : s) : firstChaosEmbedding (lp.single 2 j.val (1 : ℝ)) =ᵐ[gaussianProduct]
      coordinate j.val := by
    rw [firstChaos_unit]
    exact coordinateL2_coeFn j.val
  have he (i : ι) : firstChaosEmbedding (∑ j : s, a i j • lp.single 2 j.val (1 : ℝ))
      =ᵐ[gaussianProduct] fun ω => ∑ j : s, a i j * coordinate j.val ω := by
    filter_upwards [firstChaos_linearCombination_ae
      (fun j : s => lp.single 2 j.val (1 : ℝ)) (a i), ae_all_iff.2 hc] with ω hw hj
    rw [hw]
    exact Finset.sum_congr rfl (fun j _ => by rw [hj j])
  have hef : firstChaosFamily (fun i => ∑ j : s, a i j • lp.single 2 j.val (1 : ℝ))
      =ᵐ[gaussianProduct] (fun x : s → ℝ => fun i => ∑ j, a i j * x j) ∘ finiteProjection s := by
    filter_upwards [ae_all_iff.2 he] with ω hw
    funext i
    exact hw i
  rw [Measure.map_congr hef, ← Measure.map_map (by fun_prop)
    (finiteProjection_measurePreserving s).measurable,
    (finiteProjection_measurePreserving s).map_eq]

omit [Fintype ι] [DecidableEq ι] in
/-- The actual first-chaos representatives form a Gaussian process in Mathlib's sense. -/
theorem firstChaos_isGaussianProcess :
    IsGaussianProcess (fun h : CoefficientSpace => (firstChaosEmbedding h : SampleSpace → ℝ))
      gaussianProduct := by
  refine ⟨fun s => ?_⟩
  exact firstChaosFamily_hasGaussianLaw (fun i : s => i.val)

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
