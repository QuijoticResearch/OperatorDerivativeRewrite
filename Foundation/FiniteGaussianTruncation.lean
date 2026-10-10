import Foundation.FiniteGaussianSpectral
import Mathlib.Data.Fintype.Pi

/-! Finite total-degree Hermite approximations of the maximal divergence graph. -/
noncomputable section
open MeasureTheory Polynomial Module Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total Hermite degree, also defined for the empty coordinate set. -/
def hermiteDegree (α : ι → ℕ) : ℕ := ∑ i, α i

/-- Finite total-degree ball, rather than a rectangular coordinate cutoff. -/
def hermiteDegreeCutoff (N : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.range (N + 1))).filter (fun α => hermiteDegree α ≤ N)

/-- The cutoff includes exactly the multi-indices of degree at most N. -/
theorem mem_hermiteDegreeCutoff (α : ι → ℕ) (N : ℕ) :
    α ∈ hermiteDegreeCutoff N ↔ hermiteDegree α ≤ N := by
  simp only [hermiteDegreeCutoff, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : α i ≤ hermiteDegree α := Finset.single_le_sum (fun j _ => Nat.zero_le (α j))
      (Finset.mem_univ i)
    omega

/-- These finite balls exhaust the multi-index set in the finite-subset filter. -/
theorem hermiteDegreeCutoff_tendsto :
    Tendsto (hermiteDegreeCutoff (ι := ι)) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro s
  refine ⟨s.sup hermiteDegree, fun N hN => ?_⟩
  intro α hα
  exact (mem_hermiteDegreeCutoff α N).mpr ((Finset.le_sup hα).trans hN)

/-- Actual polynomial representing the total-degree projection of a scalar L² class. -/
def scalarHermiteTruncationPolynomial (f : ScalarGaussianL2 ι) (N : ℕ) : MvPolynomial ι ℝ :=
  ∑ α ∈ hermiteDegreeCutoff N, scalarHermiteCoefficient f α • tensorHermitePolynomial α

/-- The orthogonal total-degree projection in scalar Gaussian L². -/
def scalarHermiteTruncation (f : ScalarGaussianL2 ι) (N : ℕ) : ScalarGaussianL2 ι :=
  ∑ α ∈ hermiteDegreeCutoff N, scalarHermiteCoefficient f α • tensorHermite α

/-- The projection really belongs to the original polynomial core. -/
theorem scalarHermiteTruncationPolynomial_L2 (f : ScalarGaussianL2 ι) (N : ℕ) :
    productPolynomialL2 (scalarHermiteTruncationPolynomial f N) = scalarHermiteTruncation f N := by
  change productPolynomialEmbedding (scalarHermiteTruncationPolynomial f N) = _
  simp only [scalarHermiteTruncationPolynomial, map_sum, map_smul]
  change (∑ α ∈ hermiteDegreeCutoff N, scalarHermiteCoefficient f α •
    productPolynomialL2 (tensorHermitePolynomial α)) = _
  simp only [tensorHermitePolynomial_L2, scalarHermiteTruncation]

/-- The coefficient cutoff is exact. -/
theorem scalarHermiteTruncation_coefficient (f : ScalarGaussianL2 ι) (N : ℕ) (α : ι → ℕ) :
    scalarHermiteCoefficient (scalarHermiteTruncation f N) α =
      if hermiteDegree α ≤ N then scalarHermiteCoefficient f α else 0 := by
  classical
  simp [scalarHermiteCoefficient, scalarHermiteTruncation, inner_sum,
    real_inner_smul_right, tensorHermite_inner, mem_hermiteDegreeCutoff]

/-- Completeness supplies L² convergence with no domain hypothesis. -/
theorem scalarHermiteTruncation_tendsto (f : ScalarGaussianL2 ι) :
    Tendsto (scalarHermiteTruncation f) atTop (𝓝 f) :=
  (tensorHermiteBasis_hasSum f).comp hermiteDegreeCutoff_tendsto

/-- Continuous insertion of a scalar L² class into a Euclidean coordinate. -/
def vectorL2Insert (i : ι) : ScalarGaussianL2 ι →L[ℝ] VectorGaussianL2 ι :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ i)).compLpL 2
    (productGaussian ι)

/-- Insertion agrees with the genuine one-component polynomial field. -/
theorem vectorL2Insert_polynomial (i : ι) (p : MvPolynomial ι ℝ) :
    vectorL2Insert i (productPolynomialL2 p) = vectorPolynomialL2 (Pi.single i p) := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.basisFun ι ℝ i)).coeFn_compLpL
      (productPolynomialL2 p), productPolynomialL2_coeFn p,
      vectorPolynomialL2_coeFn (Pi.single i p)] with x hi hp hv
  change ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ i)).compLpL 2
    (productGaussian ι) (productPolynomialL2 p)) x = _
  rw [hi, hp, hv]
  ext j
  by_cases hji : j = i <;>
    simp [vectorPolynomialFunction, Pi.single_apply, EuclideanSpace.basisFun_apply, hji]

omit [DecidableEq ι] in
/-- Every actual vector L² class is reconstructed from its actual components. -/
theorem vectorL2_reassemble (u : VectorGaussianL2 ι) :
    (∑ i, vectorL2Insert i (vectorL2Component i u)) = u := by
  apply Lp.ext
  have hi : ∀ᵐ x ∂productGaussian ι, ∀ i,
      vectorL2Insert i (vectorL2Component i u) x =
        vectorL2Component i u x • EuclideanSpace.basisFun ι ℝ i :=
    ae_all_iff.mpr (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.basisFun ι ℝ i)).coeFn_compLpL _)
  have hc : ∀ᵐ x ∂productGaussian ι, ∀ i, vectorL2Component i u x = u x i :=
    ae_all_iff.mpr (fun i => vectorL2Component_coeFn i u)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => vectorL2Insert i (vectorL2Component i u)),
    hi, hc] with x hs hi hc
  rw [hs]
  simp only [hi, hc]
  exact (EuclideanSpace.basisFun ι ℝ).sum_repr (u x)

/-- Actual polynomial vector field obtained by applying the same total-degree cutoff
in every component. -/
def vectorHermiteTruncationPolynomial (u : VectorGaussianL2 ι) (N : ℕ) :
    ι → MvPolynomial ι ℝ := fun i => scalarHermiteTruncationPolynomial (vectorL2Component i u) N

/-- L² class of that genuine polynomial field. -/
def vectorHermiteTruncation (u : VectorGaussianL2 ι) (N : ℕ) : VectorGaussianL2 ι :=
  vectorPolynomialL2 (vectorHermiteTruncationPolynomial u N)

/-- Each component is the corresponding scalar projection. -/
theorem vectorHermiteTruncation_component (u : VectorGaussianL2 ι) (N : ℕ) (i : ι) :
    vectorL2Component i (vectorHermiteTruncation u N) =
      scalarHermiteTruncation (vectorL2Component i u) N := by
  rw [vectorHermiteTruncation, vectorPolynomialL2_component]
  exact scalarHermiteTruncationPolynomial_L2 _ _

/-- No component is changed inside the cutoff, and all others vanish. -/
theorem vectorHermiteTruncation_coefficient (u : VectorGaussianL2 ι)
    (N : ℕ) (i : ι) (α : ι → ℕ) :
    vectorHermiteCoefficient (vectorHermiteTruncation u N) i α =
      if hermiteDegree α ≤ N then vectorHermiteCoefficient u i α else 0 := by
  unfold vectorHermiteCoefficient
  rw [vectorHermiteTruncation_component, scalarHermiteTruncation_coefficient]

/-- Coordinate insertions turn scalar convergence into convergence in vector L². -/
theorem vectorHermiteTruncation_tendsto (u : VectorGaussianL2 ι) :
    Tendsto (vectorHermiteTruncation u) atTop (𝓝 u) := by
  have h : Tendsto (fun N => ∑ i, vectorL2Insert i
      (scalarHermiteTruncation (vectorL2Component i u) N)) atTop
      (𝓝 (∑ i, vectorL2Insert i (vectorL2Component i u))) := by
    apply tendsto_finsetSum
    intro i _
    exact (vectorL2Insert i).continuous.tendsto _ |>.comp (scalarHermiteTruncation_tendsto _)
  have he (N : ℕ) : vectorHermiteTruncation u N =
      ∑ i, vectorL2Insert i (scalarHermiteTruncation (vectorL2Component i u) N) := by
    rw [← vectorL2_reassemble (vectorHermiteTruncation u N)]
    simp only [vectorHermiteTruncation_component]
  simpa only [← he, vectorL2_reassemble] using h

/-- Lowering any positive coordinate lowers total degree by exactly one. -/
theorem hermiteDegree_lower (α : ι → ℕ) (i : ι) (hi : α i ≠ 0) :
    hermiteDegree (Function.update α i (α i - 1)) + 1 = hermiteDegree α := by
  unfold hermiteDegree
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h : (∑ j ∈ Finset.univ.erase i, α j) + α i = ∑ j, α j :=
    Finset.sum_erase_add Finset.univ α (Finset.mem_univ i)
  omega

/-- Total-degree truncation commutes with the combined raising coefficient,
with the correct one-degree shift; coordinate cancellation is preserved. -/
theorem divergenceCoefficient_truncation (u : VectorGaussianL2 ι) (N : ℕ) (α : ι → ℕ) :
    divergenceCoefficient (vectorHermiteTruncation u N) α =
      if hermiteDegree α ≤ N + 1 then divergenceCoefficient u α else 0 := by
  unfold divergenceCoefficient
  simp only [vectorHermiteTruncation_coefficient]
  by_cases hN : hermiteDegree α ≤ N + 1
  · simp only [hN, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : α i = 0
    · simp only [hi, ↓reduceIte]
    · have hd := hermiteDegree_lower α i hi
      have hb : hermiteDegree (Function.update α i (α i - 1)) ≤ N := by omega
      simp only [hi, hb, ↓reduceIte]
  · simp only [hN, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : α i = 0
    · simp only [hi, ↓reduceIte]
    · have hd := hermiteDegree_lower α i hi
      have hb : ¬ hermiteDegree (Function.update α i (α i - 1)) ≤ N := by omega
      simp only [hi, hb, ↓reduceIte, mul_zero]

/-- Genuine polynomial divergence graph approximants for every maximal adjoint pair. -/
theorem gradient_adjoint_truncation_graph (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι)
    (h : (u, g) ∈ polynomialGradient.adjoint.graph) (N : ℕ) :
    (vectorHermiteTruncation u N, scalarHermiteTruncation g (N + 1)) ∈
      polynomialDivergence.graph := by
  have he : productPolynomialL2 (divergencePolynomial (vectorHermiteTruncationPolynomial u N)) =
      scalarHermiteTruncation g (N + 1) := by
    apply scalarHermiteCoefficient_ext
    intro α
    rw [polynomialDivergence_coefficients, scalarHermiteTruncation_coefficient]
    change divergenceCoefficient (vectorHermiteTruncation u N) α = _
    rw [divergenceCoefficient_truncation, gradient_adjoint_coefficients h α]
  rw [← he]
  exact polynomialDivergence_polynomial_graph _

/-- Both L² coordinates converge: hence these are graph-norm approximations. -/
theorem gradient_adjoint_truncation_tendsto (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι) :
    Tendsto (fun N => (vectorHermiteTruncation u N, scalarHermiteTruncation g (N + 1)))
      atTop (𝓝 (u, g)) :=
  (vectorHermiteTruncation_tendsto u).prodMk_nhds
    ((scalarHermiteTruncation_tendsto g).comp (tendsto_add_atTop_nat 1))

/-- The maximal divergence adjoint lies in the actual polynomial graph closure. -/
theorem closedVectorDivergence_graph_of_coefficients (u : VectorGaussianL2 ι)
    (g : ScalarGaussianL2 ι)
    (h : ∀ α, scalarHermiteCoefficient g α = divergenceCoefficient u α) :
    (u, g) ∈ closedVectorDivergence.graph := by
  rw [← polynomialDivergence_isClosable.graph_closure_eq_closure_graph]
  apply mem_closure_of_tendsto (gradient_adjoint_truncation_tendsto u g)
  exact Eventually.of_forall
    (gradient_adjoint_truncation_graph u g (gradient_adjoint_graph_of_coefficients u g h))

omit [DecidableEq ι] in
/-- Full divergence identification follows from the explicit cancellation-preserving core. -/
theorem closedVectorDivergence_eq_gradient_adjoint :
    (closedVectorDivergence (ι := ι)) = polynomialGradient.adjoint := by
  classical
  apply le_antisymm closedVectorDivergence_le_gradient_adjoint
  apply LinearPMap.le_of_le_graph
  rintro ⟨u, g⟩ h
  exact closedVectorDivergence_graph_of_coefficients u g (gradient_adjoint_coefficients h)

/-- Exact closed divergence domain, with no stronger componentwise condition. -/
theorem closedVectorDivergence_domain_iff (u : VectorGaussianL2 ι) :
    u ∈ closedVectorDivergence.domain ↔ Summable (fun α => divergenceCoefficient u α ^ 2) := by
  rw [closedVectorDivergence_eq_gradient_adjoint]
  exact gradient_adjoint_domain_iff u

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
