import Foundation.FiniteGaussianAdjoints

/-! Exact scalar weighted Sobolev domain and coefficient realization of the closed gradient. -/
noncomputable section
open MeasureTheory Polynomial Module Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projection of a continuous coordinate insertion recovers exactly that component. -/
theorem vectorL2Component_insert (i j : ι) (f : ScalarGaussianL2 ι) :
    vectorL2Component i (vectorL2Insert j f) = if i = j then f else 0 := by
  apply Lp.ext
  filter_upwards [vectorL2Component_coeFn i (vectorL2Insert j f),
    (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ j)).coeFn_compLpL f,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := productGaussian ι)] with x hc hi hz
  change vectorL2Component i (vectorL2Insert j f) x = (if i = j then f else 0) x
  rw [hc]
  change ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun ι ℝ j)).compLpL 2
    (productGaussian ι) f) x i = _
  rw [hi]
  by_cases hij : i = j
  · simp [hij, EuclideanSpace.basisFun_apply]
  · simp [hij, EuclideanSpace.basisFun_apply]

omit [DecidableEq ι] in
/-- Square-summable component coefficient families are realized by an actual vector L² class. -/
theorem exists_vectorHermite_coefficients (c : ι → (ι → ℕ) → ℝ)
    (hc : ∀ i, Summable (fun α => c i α ^ 2)) :
    ∃ u : VectorGaussianL2 ι, ∀ i α, vectorHermiteCoefficient u i α = c i α := by
  classical
  choose f hf using fun i => exists_scalarHermite_coefficients (c i) (hc i)
  refine ⟨∑ j, vectorL2Insert j (f j), ?_⟩
  intro i α
  have he : vectorL2Component i (∑ j, vectorL2Insert j (f j)) = f i := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpₗ 2 (productGaussian ι)
      (∑ j, vectorL2Insert j (f j)) = f i
    rw [map_sum]
    change (∑ j, vectorL2Component i (vectorL2Insert j (f j))) = f i
    simp only [vectorL2Component_insert]
    simp
  unfold vectorHermiteCoefficient
  rw [he]
  exact hf i α

/-- Actual polynomial gradient approximants from prescribed output *coefficients*,
with membership proved from the true derivative rather than assumed. -/
theorem gradient_coefficients_truncation_graph (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι)
    (h : ∀ i α, vectorHermiteCoefficient g i α = gradientCoefficient f i α) (N : ℕ) :
    (scalarHermiteTruncation f (N + 1), vectorHermiteTruncation g N) ∈
      polynomialGradient.graph := by
  have hc := polynomialGradient_polynomial_graph (scalarHermiteTruncationPolynomial f (N + 1))
  rw [scalarHermiteTruncationPolynomial_L2] at hc
  have he : gradientPolynomialL2 (scalarHermiteTruncationPolynomial f (N + 1)) =
      vectorHermiteTruncation g N := by
    apply vectorHermiteCoefficient_ext
    intro i α
    rw [divergence_adjoint_coefficients
      (LinearPMap.le_graph_of_le polynomialGradient_le_divergence_adjoint hc),
      gradientCoefficient_truncation, vectorHermiteTruncation_coefficient, h i α]
  rwa [he] at hc

/-- Coefficient realization in the actual closed gradient graph, proved by graph approximation. -/
theorem closedGradient_graph_of_coefficients (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι)
    (h : ∀ i α, vectorHermiteCoefficient g i α = gradientCoefficient f i α) :
    (f, g) ∈ closedGradient.graph := by
  rw [← polynomialGradient_isClosable.graph_closure_eq_closure_graph]
  apply mem_closure_of_tendsto (divergence_adjoint_truncation_tendsto f g)
  exact Eventually.of_forall (gradient_coefficients_truncation_graph f g h)

/-- Exact full closed gradient graph; coefficients are necessary and sufficient. -/
theorem closedGradient_graph_iff (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι) :
    (f, g) ∈ closedGradient.graph ↔
      ∀ i α, vectorHermiteCoefficient g i α = gradientCoefficient f i α := by
  constructor
  · intro h
    rw [closedGradient_eq_divergence_adjoint] at h
    exact divergence_adjoint_coefficients h
  · exact closedGradient_graph_of_coefficients f g

omit [Fintype ι] in
/-- Coordinate ladder shifts are injective on all multi-indices. -/
theorem hermiteRaise_injective (i : ι) :
    Function.Injective (fun α : ι → ℕ => Function.update α i (α i + 1)) := by
  classical
  intro α β h
  ext j
  by_cases hji : j = i
  · subst j
    have hh := congrFun h i
    simpa only [Function.update_self, Nat.add_right_cancel_iff] using hh
  · have hh := congrFun h j
    simpa only [Function.update_of_ne hji] using hh

omit [Fintype ι] in
/-- A multi-index is in the raising image exactly when its selected coordinate is positive. -/
theorem mem_range_hermiteRaise (i : ι) (α : ι → ℕ) :
    α ∈ Set.range (fun β : ι → ℕ => Function.update β i (β i + 1)) ↔ α i ≠ 0 := by
  classical
  constructor
  · rintro ⟨β, rfl⟩
    simp
  · intro hi
    refine ⟨Function.update α i (α i - 1), ?_⟩
    ext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      omega
    · simp only [Function.update_of_ne hji]

/-- Reindexing the nonzero coordinate modes gives the exact coordinate weight. -/
theorem gradientCoefficient_summable_iff (f : ScalarGaussianL2 ι) (i : ι) :
    Summable (fun α => gradientCoefficient f i α ^ 2) ↔
      Summable (fun α => (α i : ℝ) * scalarHermiteCoefficient f α ^ 2) := by
  have hz : ∀ α ∉ Set.range (fun β : ι → ℕ => Function.update β i (β i + 1)),
      (α i : ℝ) * scalarHermiteCoefficient f α ^ 2 = 0 := by
    intro α hα
    have hi : α i = 0 := by
      simpa only [mem_range_hermiteRaise, not_not] using hα
    simp only [hi, Nat.cast_zero, zero_mul]
  have hs := (hermiteRaise_injective i).summable_iff hz
  change (Summable (fun α => ((Function.update α i (α i + 1)) i : ℝ) *
    scalarHermiteCoefficient f (Function.update α i (α i + 1)) ^ 2)) ↔
    Summable (fun α => (α i : ℝ) * scalarHermiteCoefficient f α ^ 2) at hs
  simpa only [Function.comp_apply, Function.update_self, gradientCoefficient,
    GaussianCore.hermite_weight_square, Nat.cast_add, Nat.cast_one] using hs

omit [DecidableEq ι] in
/-- Total-degree weighting is exactly the finite sum of coordinate weights. -/
theorem hermiteDegree_weight_summable_iff (c : (ι → ℕ) → ℝ) :
    Summable (fun α => (hermiteDegree α : ℝ) * c α ^ 2) ↔
      ∀ i, Summable (fun α => (α i : ℝ) * c α ^ 2) := by
  classical
  constructor
  · intro h i
    apply Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_) h
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i))
  · intro h
    have hs := summable_sum (s := Finset.univ) (fun i _ => h i)
    simpa only [← Finset.sum_mul, ← Nat.cast_sum, hermiteDegree] using hs

omit [DecidableEq ι] in
/-- The scalar gradient graph domain is precisely Σ |α| |cα|² < ∞. -/
theorem closedGradient_domain_iff (f : ScalarGaussianL2 ι) :
    f ∈ closedGradient.domain ↔
      Summable (fun α => (hermiteDegree α : ℝ) * scalarHermiteCoefficient f α ^ 2) := by
  classical
  rw [LinearPMap.mem_domain_iff, hermiteDegree_weight_summable_iff]
  constructor
  · rintro ⟨g, hg⟩ i
    have he := (closedGradient_graph_iff f g).mp hg
    apply (gradientCoefficient_summable_iff f i).mp
    simpa only [← he i, vectorHermiteCoefficient] using
      (scalarHermiteCoefficient_hasSum_sq (vectorL2Component i g)).summable
  · intro h
    obtain ⟨g, hg⟩ := exists_vectorHermite_coefficients (gradientCoefficient f)
      (fun i => (gradientCoefficient_summable_iff f i).mpr (h i))
    exact ⟨g, closedGradient_graph_of_coefficients f g hg⟩

omit [DecidableEq ι] in
/-- Dimension zero has the whole scalar L² gradient domain. -/
theorem closedGradient_domain_empty [IsEmpty ι] (f : ScalarGaussianL2 ι) :
    f ∈ closedGradient.domain := by
  classical
  rw [closedGradient_domain_iff]
  simp only [hermiteDegree, Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_mul]
  exact summable_zero

omit [DecidableEq ι] in
/-- In dimension zero the genuine closed gradient is zero. -/
theorem closedGradient_graph_empty [IsEmpty ι] (f : ScalarGaussianL2 ι) :
    (f, (0 : VectorGaussianL2 ι)) ∈ closedGradient.graph := by
  classical
  apply closedGradient_graph_of_coefficients
  intro i
  exact isEmptyElim i

/-- Exact full closed vector divergence graph, retaining all coordinate cancellation. -/
theorem closedVectorDivergence_graph_iff (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι) :
    (u, g) ∈ closedVectorDivergence.graph ↔
      ∀ α, scalarHermiteCoefficient g α = divergenceCoefficient u α := by
  rw [closedVectorDivergence_eq_gradient_adjoint]
  exact gradient_adjoint_graph_iff u g

/-- The closed divergence output has exactly the combined coefficient norm. -/
theorem closedVectorDivergence_norm_sq (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι)
    (h : (u, g) ∈ closedVectorDivergence.graph) :
    ‖g‖ ^ 2 = ∑' α, divergenceCoefficient u α ^ 2 := by
  rw [closedVectorDivergence_eq_gradient_adjoint] at h
  exact gradient_adjoint_norm_sq u g h

omit [DecidableEq ι] in
/-- The actual closed divergence is zero on the full vector space in dimension zero. -/
theorem closedVectorDivergence_graph_empty [IsEmpty ι] (u : VectorGaussianL2 ι) :
    (u, (0 : ScalarGaussianL2 ι)) ∈ closedVectorDivergence.graph := by
  classical
  rw [closedVectorDivergence_eq_gradient_adjoint]
  exact gradient_adjoint_graph_empty u


/-- Exact spectral graph of the full maximal gradient δ₀*. -/
theorem divergence_adjoint_graph_iff (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι) :
    (f, g) ∈ polynomialDivergence.adjoint.graph ↔
      ∀ i α, vectorHermiteCoefficient g i α = gradientCoefficient f i α := by
  rw [← closedGradient_eq_divergence_adjoint]
  exact closedGradient_graph_iff f g

/-- Squared Hilbert graph error tends to zero for the gradient total-degree approximants. -/
theorem divergence_adjoint_truncation_graphNorm_tendsto
    (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι) :
    Tendsto (fun N => ‖scalarHermiteTruncation f (N + 1) - f‖ ^ 2 +
      ‖vectorHermiteTruncation g N - g‖ ^ 2) atTop (𝓝 0) := by
  classical
  have h1 : Tendsto (fun N => ‖scalarHermiteTruncation f (N + 1) - f‖) atTop (𝓝 0) := by
    simpa using (((scalarHermiteTruncation_tendsto f).comp
      (tendsto_add_atTop_nat 1)).sub (tendsto_const_nhds (x := f))).norm
  have h2 : Tendsto (fun N => ‖vectorHermiteTruncation g N - g‖) atTop (𝓝 0) := by
    simpa using ((vectorHermiteTruncation_tendsto g).sub (tendsto_const_nhds (x := g))).norm
  simpa using (h1.pow 2).add (h2.pow 2)

/-- Squared Hilbert graph error tends to zero for the divergence total-degree approximants. -/
theorem gradient_adjoint_truncation_graphNorm_tendsto
    (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι) :
    Tendsto (fun N => ‖vectorHermiteTruncation u N - u‖ ^ 2 +
      ‖scalarHermiteTruncation g (N + 1) - g‖ ^ 2) atTop (𝓝 0) := by
  classical
  have h1 : Tendsto (fun N => ‖vectorHermiteTruncation u N - u‖) atTop (𝓝 0) := by
    simpa using ((vectorHermiteTruncation_tendsto u).sub (tendsto_const_nhds (x := u))).norm
  have h2 : Tendsto (fun N => ‖scalarHermiteTruncation g (N + 1) - g‖) atTop (𝓝 0) := by
    simpa using (((scalarHermiteTruncation_tendsto g).comp
      (tendsto_add_atTop_nat 1)).sub (tendsto_const_nhds (x := g))).norm
  simpa using (h1.pow 2).add (h2.pow 2)

/-- In zero dimensions the total-degree cutoff is the single vacuum index for every N. -/
theorem hermiteDegreeCutoff_empty [IsEmpty ι] (N : ℕ) :
    hermiteDegreeCutoff (ι := ι) N = {fun _ : ι => 0} := by
  ext α
  simp [mem_hermiteDegreeCutoff, hermiteDegree, Subsingleton.elim α (fun _ : ι => (0 : ℕ))]

/-- Every scalar total-degree projection is already the identity in dimension zero. -/
theorem scalarHermiteTruncation_empty [IsEmpty ι] (f : ScalarGaussianL2 ι) (N : ℕ) :
    scalarHermiteTruncation f N = f := by
  classical
  apply scalarHermiteCoefficient_ext
  intro α
  simp [scalarHermiteTruncation_coefficient, hermiteDegree]

/-- Every vector total-degree projection is also the identity in dimension zero. -/
theorem vectorHermiteTruncation_empty [IsEmpty ι] (u : VectorGaussianL2 ι) (N : ℕ) :
    vectorHermiteTruncation u N = u := by
  classical
  apply vectorHermiteCoefficient_ext
  intro i
  exact isEmptyElim i

omit [DecidableEq ι] in
/-- The closed divergence has the whole vector L² domain in dimension zero. -/
theorem closedVectorDivergence_domain_empty [IsEmpty ι] (u : VectorGaussianL2 ι) :
    u ∈ closedVectorDivergence.domain :=
  LinearPMap.mem_domain_iff.mpr ⟨0, closedVectorDivergence_graph_empty u⟩

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
