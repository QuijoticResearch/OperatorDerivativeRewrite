import Foundation.InfiniteGaussianOperators
import Foundation.FiniteGaussianDomains
import Foundation.AdjointBidual

/-! Finite-coordinate divergence graphs embedded in the countable Gaussian product.
These are graph approximations inside each finite sector; no infinite graph-core
identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false


/-- A finite-coordinate polynomial, as a member of the intrinsic cylindrical domain. -/
def coordinatePolynomialDomain (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    polynomialCylindricalDomain :=
  ⟨polynomialCylinderEmbedding s p, by
    rw [← isonormalCylinderL2_units]
    exact isonormalCylinderL2_mem_core _ _⟩

/-- The genuine derivative of a coordinate polynomial has its actual partial derivatives. -/
theorem coordinatePolynomialDomain_derivative_coeFn (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    polynomialDerivative (coordinatePolynomialDomain s p) =ᵐ[gaussianProduct]
      fun ω => ∑ i : s, MvPolynomial.eval (finiteProjection s ω) (MvPolynomial.pderiv i p) •
        lp.single 2 i.val (1 : ℝ) := by
  have he : polynomialDerivative (coordinatePolynomialDomain s p) =
      isonormalCylinderGradientL2 (fun i : s => lp.single 2 i.val (1 : ℝ)) p := by
    apply polynomialGradient_agrees
    exact isonormalCylinderL2_units s p
  rw [he]
  have hc (i : s) := coordinateL2_coeFn i.val
  filter_upwards [isonormalCylinderGradientL2_coeFn
    (fun i : s => lp.single 2 i.val (1 : ℝ)) p, ae_all_iff.2 hc] with ω hg hc
  rw [hg]
  unfold isonormalCylinderGradient isonormalCylinder
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg (fun x : s → ℝ => MvPolynomial.eval x (MvPolynomial.pderiv i p))
  funext j
  simpa only [firstChaos_unit, finiteProjection, Finset.restrict_def, coordinate] using hc j

/-- A bounded lift of an arbitrary finite-dimensional vector field, with the same coordinate
values and zero Hilbert components outside the chosen finite set. -/
def finiteVectorPullback (s : Finset ℕ) :
    FiniteGaussian.VectorGaussianL2 s →L[ℝ] GaussianVectorL2 :=
  ∑ i : s, (scalarTensor (lp.single 2 i.val (1 : ℝ))).comp
    ((finitePullback s).toContinuousLinearMap.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (FiniteGaussian.productGaussian s)))

theorem finiteVectorPullback_apply (s : Finset ℕ) (u : FiniteGaussian.VectorGaussianL2 s) :
    finiteVectorPullback s u = ∑ i : s,
      scalarTensor (lp.single 2 i.val (1 : ℝ))
        (finitePullback s (FiniteGaussian.vectorL2Component i u)) := by
  simp [finiteVectorPullback, FiniteGaussian.vectorL2Component, ContinuousLinearMap.compLpL]

/-- A lifted finite polynomial field is exactly an actual cylindrical finite-rank field. -/
theorem finiteVectorPullback_polynomial (s : Finset ℕ) (u : s → MvPolynomial s ℝ) :
    finiteVectorPullback s (FiniteGaussian.vectorPolynomialL2 u) =
      cylindricalField (fun i => coordinatePolynomialDomain s (u i))
        (fun i : s => lp.single 2 i.val (1 : ℝ)) := by
  rw [finiteVectorPullback_apply]
  simp only [FiniteGaussian.vectorPolynomialL2_component]
  rfl

/-- The rank divergence of a coordinate polynomial is the lifted Gaussian partial divergence. -/
theorem rankDivergence_coordinate (s : Finset ℕ) (p : MvPolynomial s ℝ) (i : s) :
    rankDivergence (coordinatePolynomialDomain s p) (lp.single 2 i.val (1 : ℝ)) =
      polynomialCylinderEmbedding s (FiniteGaussian.coordinateDivergencePolynomial i p) := by
  apply Lp.ext
  filter_upwards [rankDivergence_coeFn (coordinatePolynomialDomain s p)
      (lp.single 2 i.val (1 : ℝ)), polynomialCylinderEmbedding_coeFn s p,
    coordinatePolynomialDomain_derivative_coeFn s p, coordinateL2_coeFn i.val,
    polynomialCylinderEmbedding_coeFn s (FiniteGaussian.coordinateDivergencePolynomial i p)]
      with ω hd hp hg hi hout
  rw [hd, hout]
  change polynomialCylinderEmbedding s p ω *
    firstChaosEmbedding (lp.single 2 i.val (1 : ℝ)) ω - _ = _
  rw [hp, hg, firstChaos_unit, hi]
  simp only [sum_inner, real_inner_smul_left]
  simp only [lp.inner_single_right, Real.inner_apply, mul_one]
  have hs : (∑ j : s, MvPolynomial.eval (finiteProjection s ω) (MvPolynomial.pderiv j p) *
      (lp.single 2 j.val (1 : ℝ) : CoefficientSpace) i.val) =
      MvPolynomial.eval (finiteProjection s ω) (MvPolynomial.pderiv i p) := by
    simp [lp.single_apply, Pi.single_apply]
  rw [hs]
  simp [FiniteGaussian.coordinateDivergencePolynomial, polynomialCylinder,
    finiteProjection, coordinate, mul_comm]

/-- Every finite-dimensional polynomial divergence graph lifts to the genuine infinite core. -/
theorem finitePolynomialDivergence_lift_graph (s : Finset ℕ) (u : s → MvPolynomial s ℝ) :
    (finiteVectorPullback s (FiniteGaussian.vectorPolynomialL2 u),
      finitePullback s
        (FiniteGaussian.productPolynomialL2 (FiniteGaussian.divergencePolynomial u))) ∈
        cylindricalDivergence.graph := by
  rw [finiteVectorPullback_polynomial]
  have he : cylindricalDivergenceExpression (fun i => coordinatePolynomialDomain s (u i))
      (fun i : s => lp.single 2 i.val (1 : ℝ)) =
      finitePullback s
        (FiniteGaussian.productPolynomialL2 (FiniteGaussian.divergencePolynomial u)) := by
    unfold cylindricalDivergenceExpression
    simp only [rankDivergence_coordinate]
    change (∑ i : s, polynomialCylinderEmbedding s
      (FiniteGaussian.coordinateDivergencePolynomial i (u i))) =
      polynomialCylinderEmbedding s (∑ i : s, FiniteGaussian.coordinateDivergencePolynomial i (u i))
    rw [map_sum]
  rw [← he]
  exact cylindricalDivergence_field_graph _ _

/-- The graph closure of the genuine polynomial divergence; its closability was proved by IBP. -/
def closedPolynomialDivergence : GaussianVectorL2 →ₗ.[ℝ] GaussianL2 :=
  cylindricalDivergence.closure

theorem closedPolynomialDivergence_isClosed : closedPolynomialDivergence.IsClosed :=
  cylindricalDivergence_isClosable.closure_isClosed

/-- Closing the polynomial divergence cannot exceed the full Hilbert adjoint. -/
theorem closedPolynomialDivergence_le_hilbertDivergence :
    closedPolynomialDivergence ≤ hilbertDivergence :=
  operatorClosure_le_closed cylindricalDivergence_isClosable hilbertDivergence_isClosed
    cylindricalDivergence_le_hilbertDivergence

/-- Closing δ₀ leaves δ₀* unchanged. This does not identify δ₀* with D. -/
theorem closedPolynomialDivergence_adjoint_eq :
    closedPolynomialDivergence.adjoint = cylindricalDivergence.adjoint :=
  operatorClosure_adjoint_eq cylindricalDivergence_isClosable cylindricalDivergence_dense_domain

/-- Simultaneous total-degree truncation of every component preserves the genuine divergence
coefficients. Its scalar output has cutoff N+1; no componentwise energy condition is imposed. -/
theorem finiteDivergence_truncation_lift_graph (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s)
    (h : (u, g) ∈ FiniteGaussian.polynomialGradient.adjoint.graph) (N : ℕ) :
    (finiteVectorPullback s (FiniteGaussian.vectorHermiteTruncation u N),
      finitePullback s (FiniteGaussian.scalarHermiteTruncation g (N + 1))) ∈
        cylindricalDivergence.graph := by
  have ht := FiniteGaussian.gradient_adjoint_truncation_graph u g h N
  rw [FiniteGaussian.polynomialDivergence_graph] at ht
  obtain ⟨v, hv⟩ := ht
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  change FiniteGaussian.vectorPolynomialL2 v = FiniteGaussian.vectorHermiteTruncation u N at hv1
  change FiniteGaussian.productPolynomialL2 (FiniteGaussian.divergencePolynomial v) =
    FiniteGaussian.scalarHermiteTruncation g (N + 1) at hv2
  rw [← hv1, ← hv2]
  exact finitePolynomialDivergence_lift_graph s v

/-- Both lifted graph coordinates converge in the infinite-dimensional L² spaces. -/
theorem finiteDivergence_truncation_lift_tendsto (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s) :
    Tendsto (fun N => (finiteVectorPullback s (FiniteGaussian.vectorHermiteTruncation u N),
      finitePullback s (FiniteGaussian.scalarHermiteTruncation g (N + 1)))) atTop
        (𝓝 (finiteVectorPullback s u, finitePullback s g)) :=
  ((finiteVectorPullback s).continuous.tendsto u).comp
    (FiniteGaussian.vectorHermiteTruncation_tendsto u) |>.prodMk_nhds
      (((finitePullback s).continuous.tendsto g).comp
        ((FiniteGaussian.scalarHermiteTruncation_tendsto g).comp (tendsto_add_atTop_nat 1)))

/-- Squared graph-norm error tends to zero after lifting, without discarding cancellations. -/
theorem finiteDivergence_truncation_lift_graphNorm_tendsto (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s) :
    Tendsto (fun N =>
      ‖finiteVectorPullback s (FiniteGaussian.vectorHermiteTruncation u N) -
        finiteVectorPullback s u‖ ^ 2 +
      ‖finitePullback s (FiniteGaussian.scalarHermiteTruncation g (N + 1)) -
        finitePullback s g‖ ^ 2) atTop (𝓝 0) := by
  have ht := finiteDivergence_truncation_lift_tendsto s u g
  have h1 := (ht.fst_nhds.sub (tendsto_const_nhds (x := finiteVectorPullback s u))).norm.pow 2
  have h2 := (ht.snd_nhds.sub (tendsto_const_nhds (x := finitePullback s g))).norm.pow 2
  simpa using h1.add h2

/-- The entire maximal finite-coordinate divergence graph, including cancellation domains,
is contained in the closure of the actual infinite-dimensional polynomial divergence graph. -/
theorem finiteDivergence_lift_closed_graph (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s)
    (h : (u, g) ∈ FiniteGaussian.polynomialGradient.adjoint.graph) :
    (finiteVectorPullback s u, finitePullback s g) ∈ closedPolynomialDivergence.graph := by
  rw [show closedPolynomialDivergence = cylindricalDivergence.closure from rfl,
    ← cylindricalDivergence_isClosable.graph_closure_eq_closure_graph]
  exact mem_closure_of_tendsto (finiteDivergence_truncation_lift_tendsto s u g)
    (Eventually.of_forall (finiteDivergence_truncation_lift_graph s u g h))

/-- The full infinite adjoint has the same value on every lifted maximal finite-sector graph. -/
theorem finiteDivergence_lift_hilbert_graph (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s)
    (h : (u, g) ∈ FiniteGaussian.polynomialGradient.adjoint.graph) :
    (finiteVectorPullback s u, finitePullback s g) ∈ hilbertDivergence.graph :=
  LinearPMap.le_graph_of_le closedPolynomialDivergence_le_hilbertDivergence
    (finiteDivergence_lift_closed_graph s u g h)

/-- Coefficient realization uses the combined coefficients, not componentwise weighted norms. -/
theorem finiteDivergence_coefficients_lift_closed_graph (s : Finset ℕ)
    (u : FiniteGaussian.VectorGaussianL2 s) (g : FiniteGaussian.ScalarGaussianL2 s)
    (h : ∀ α, FiniteGaussian.scalarHermiteCoefficient g α =
      FiniteGaussian.divergenceCoefficient u α) :
    (finiteVectorPullback s u, finitePullback s g) ∈ closedPolynomialDivergence.graph :=
  finiteDivergence_lift_closed_graph s u g
    (FiniteGaussian.gradient_adjoint_graph_of_coefficients u g h)

/-- Every finite-sector field satisfying the exact combined-coefficient summability condition
has its divergence realized in the closed infinite polynomial graph. -/
theorem finiteDivergence_domain_lift (s : Finset ℕ) (u : FiniteGaussian.VectorGaussianL2 s)
    (h : Summable (fun α => FiniteGaussian.divergenceCoefficient u α ^ 2)) :
    ∃ g : FiniteGaussian.ScalarGaussianL2 s,
      (finiteVectorPullback s u, finitePullback s g) ∈ closedPolynomialDivergence.graph := by
  have hu := (FiniteGaussian.closedVectorDivergence_domain_iff u).mpr h
  refine ⟨FiniteGaussian.closedVectorDivergence ⟨u, hu⟩, ?_⟩
  apply finiteDivergence_lift_closed_graph
  rw [← FiniteGaussian.closedVectorDivergence_eq_gradient_adjoint]
  exact FiniteGaussian.closedVectorDivergence.mem_graph ⟨u, hu⟩

/-- The finite-sector vector lift is zero in dimension zero. -/
theorem finiteVectorPullback_empty (u : FiniteGaussian.VectorGaussianL2 (∅ : Finset ℕ)) :
    finiteVectorPullback ∅ u = 0 := by
  simp [finiteVectorPullback_apply]

/-- Coordinate polynomial gradients commute with the actual finite-coordinate lift. -/
theorem coordinatePolynomialDomain_derivative_lift (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    polynomialDerivative (coordinatePolynomialDomain s p) =
      finiteVectorPullback s (FiniteGaussian.gradientPolynomialL2 p) := by
  rw [FiniteGaussian.gradientPolynomialL2, finiteVectorPullback_polynomial]
  apply Lp.ext
  have hr (i : s) := scalarTensor_coeFn (lp.single 2 i.val (1 : ℝ))
    (coordinatePolynomialDomain s (MvPolynomial.pderiv i p))
  have hp (i : s) := polynomialCylinderEmbedding_coeFn s (MvPolynomial.pderiv i p)
  filter_upwards [coordinatePolynomialDomain_derivative_coeFn s p,
    Lp.coeFn_finsetSum Finset.univ (fun i : s =>
      scalarTensor (lp.single 2 i.val (1 : ℝ))
        (coordinatePolynomialDomain s (MvPolynomial.pderiv i p))),
    ae_all_iff.2 hr, ae_all_iff.2 hp] with ω hd hs hr hp
  rw [hd]
  change _ = (∑ i : s, scalarTensor (lp.single 2 i.val (1 : ℝ))
    (coordinatePolynomialDomain s (MvPolynomial.pderiv i p))) ω
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i]
  change _ = polynomialCylinderEmbedding s (MvPolynomial.pderiv i p) ω • _
  rw [hp i]
  rfl

/-- Every genuine finite polynomial gradient graph lifts to D₀. -/
theorem finitePolynomialGradient_lift_graph (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    (finitePullback s (FiniteGaussian.productPolynomialL2 p),
      finiteVectorPullback s (FiniteGaussian.gradientPolynomialL2 p)) ∈
        cylindricalDerivative.graph := by
  rw [← coordinatePolynomialDomain_derivative_lift]
  exact cylindricalDerivative.mem_graph (coordinatePolynomialDomain s p)

/-- Every maximal finite gradient graph lifts to the closed genuine derivative.
This uses the proved finite Hermite graph approximations, not an assumed graph core. -/
theorem finiteGradient_lift_closed_graph (s : Finset ℕ)
    (f : FiniteGaussian.ScalarGaussianL2 s) (g : FiniteGaussian.VectorGaussianL2 s)
    (h : (f, g) ∈ FiniteGaussian.polynomialDivergence.adjoint.graph) :
    (finitePullback s f, finiteVectorPullback s g) ∈ closedCylindricalDerivative.graph := by
  rw [closedCylindricalDerivative_graph]
  have ht : Tendsto (fun N =>
      (finitePullback s (FiniteGaussian.scalarHermiteTruncation f (N + 1)),
        finiteVectorPullback s (FiniteGaussian.vectorHermiteTruncation g N))) atTop
          (𝓝 (finitePullback s f, finiteVectorPullback s g)) :=
    (((finitePullback s).continuous.tendsto f).comp
      ((FiniteGaussian.scalarHermiteTruncation_tendsto f).comp
        (tendsto_add_atTop_nat 1))).prodMk_nhds
        (((finiteVectorPullback s).continuous.tendsto g).comp
          (FiniteGaussian.vectorHermiteTruncation_tendsto g))
  apply mem_closure_of_tendsto ht
  apply Eventually.of_forall
  intro N
  have hn := FiniteGaussian.divergence_adjoint_truncation_graph f g h N
  rw [FiniteGaussian.polynomialGradient_graph] at hn
  obtain ⟨p, hp⟩ := hn
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  change FiniteGaussian.productPolynomialL2 p =
    FiniteGaussian.scalarHermiteTruncation f (N + 1) at hp1
  change FiniteGaussian.gradientPolynomialL2 p = FiniteGaussian.vectorHermiteTruncation g N at hp2
  rw [← hp1, ← hp2]
  exact finitePolynomialGradient_lift_graph s p

/-- The full divergence recovers the genuine closed derivative by adjointness.
This operator-first identity does not assert that the polynomial divergence is a core. -/
theorem hilbertDivergence_adjoint_eq_closedDerivative :
    hilbertDivergence.adjoint = closedCylindricalDerivative :=
  closedOperator_adjoint_adjoint_eq closedCylindricalDerivative_isClosed
    closedCylindricalDerivative_dense_domain hilbertDivergence_dense_domain

/-- The adjoint of the polynomial divergence is densely defined because it contains D. -/
theorem cylindricalDivergence_adjoint_dense_domain :
    Dense (cylindricalDivergence.adjoint.domain : Set GaussianL2) :=
  closedCylindricalDerivative_dense_domain.mono
    closedCylindricalDerivative_le_cylindricalDivergence_adjoint.1

/-- δ₀** is exactly its graph closure, not automatically the full divergence δ. -/
theorem cylindricalDivergence_adjoint_adjoint_eq_closedPolynomialDivergence :
    cylindricalDivergence.adjoint.adjoint = closedPolynomialDivergence :=
  closableOperator_adjoint_adjoint_eq_closure cylindricalDivergence_isClosable
    cylindricalDivergence_dense_domain cylindricalDivergence_adjoint_dense_domain

/-- With the proved bidual identities, the two open core identifications are equivalent.
This equivalence proves neither side; no graph-density hypothesis is introduced. -/
theorem polynomialDivergence_core_iff_adjoint_identification :
    closedPolynomialDivergence = hilbertDivergence ↔
      cylindricalDivergence.adjoint = closedCylindricalDerivative := by
  constructor
  · intro h
    have he := congrArg (fun T : GaussianVectorL2 →ₗ.[ℝ] GaussianL2 => T.adjoint) h
    rwa [closedPolynomialDivergence_adjoint_eq,
      hilbertDivergence_adjoint_eq_closedDerivative] at he
  · intro h
    rw [← cylindricalDivergence_adjoint_adjoint_eq_closedPolynomialDivergence, h]

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
