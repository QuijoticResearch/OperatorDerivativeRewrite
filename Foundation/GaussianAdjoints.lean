import Foundation.GaussianDensity
import Foundation.AdjointClosure

/-! Densely defined Gaussian polynomial operators and rigorously justified adjoint inclusions. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

/-- D₀ has the dense algebraic polynomial domain. -/
theorem polynomialDerivative_dense_domain :
    Dense (polynomialDerivative.domain : Set GaussianL2) := by
  rw [polynomialDerivative_domain]; exact polynomialEmbedding_dense

/-- δ₀ has the same dense algebraic polynomial domain. -/
theorem polynomialDivergence_dense_domain :
    Dense (polynomialDivergence.domain : Set GaussianL2) := by
  rw [polynomialDivergence_domain]; exact polynomialEmbedding_dense

/-- Actual operator inclusion D₀ ⊆ δ₀*, including both domain inclusion and values. -/
theorem polynomialDerivative_le_divergence_adjoint :
    polynomialDerivative ≤ polynomialDivergence.adjoint :=
  polynomialDerivative_formalAdjoint.symm.le_adjoint polynomialDivergence_dense_domain

/-- Actual operator inclusion δ₀ ⊆ D₀*, with the orientation supplied by IBP. -/
theorem polynomialDivergence_le_derivative_adjoint :
    polynomialDivergence ≤ polynomialDerivative.adjoint :=
  polynomialDerivative_formalAdjoint.le_adjoint polynomialDerivative_dense_domain

/-- The divergence too is genuinely closable: its dense-domain adjoint partner is closed. -/
theorem polynomialDivergence_isClosable : polynomialDivergence.IsClosable :=
  (polynomialDerivative.adjoint_isClosed polynomialDerivative_dense_domain).isClosable.leIsClosable
    polynomialDivergence_le_derivative_adjoint

/-- The genuine closed derivative is the graph closure of D₀. -/
abbrev closedDerivative := polynomialDerivative.closure

/-- The genuine closed divergence is the graph closure of δ₀. -/
abbrev closedDivergence := polynomialDivergence.closure

theorem closedDerivative_isClosed : closedDerivative.IsClosed :=
  polynomialDerivative_isClosable.closure_isClosed

theorem closedDivergence_isClosed : closedDivergence.IsClosed :=
  polynomialDivergence_isClosable.closure_isClosed

theorem closedDerivative_dense_domain : Dense (closedDerivative.domain : Set GaussianL2) :=
  operatorClosure_dense_domain polynomialDerivative_dense_domain

theorem closedDivergence_dense_domain : Dense (closedDivergence.domain : Set GaussianL2) :=
  operatorClosure_dense_domain polynomialDivergence_dense_domain

/-- Strongest closed derivative inclusion proved here; equality is not inferred from density. -/
theorem closedDerivative_le_divergence_adjoint :
    closedDerivative ≤ polynomialDivergence.adjoint :=
  operatorClosure_le_closed polynomialDerivative_isClosable
    (polynomialDivergence.adjoint_isClosed polynomialDivergence_dense_domain)
    polynomialDerivative_le_divergence_adjoint

/-- Strongest closed divergence inclusion proved here; equality needs a graph-core argument. -/
theorem closedDivergence_le_derivative_adjoint :
    closedDivergence ≤ polynomialDerivative.adjoint :=
  operatorClosure_le_closed polynomialDivergence_isClosable
    (polynomialDerivative.adjoint_isClosed polynomialDerivative_dense_domain)
    polynomialDivergence_le_derivative_adjoint

/-- Integration by parts holds between the two closed domains. -/
theorem closedDerivative_formalAdjoint : closedDerivative.IsFormalAdjoint closedDivergence :=
  (formalAdjoint_closure_left polynomialDivergence_isClosable
    (formalAdjoint_closure_left polynomialDerivative_isClosable
      polynomialDerivative_formalAdjoint).symm).symm

/-- Explicit domain membership and actual classical derivative value in the closed graph. -/
theorem closedDerivative_polynomial_graph (p : ℝ[X]) :
    (polynomialL2 p, polynomialL2 p.derivative) ∈ closedDerivative.graph :=
  LinearPMap.le_graph_of_le polynomialDerivative.le_closure
    (polynomialDerivative_polynomial p)

/-- Explicit polynomial domain membership and actual divergence value in the closed graph. -/
theorem closedDivergence_polynomial_graph (p : ℝ[X]) :
    (polynomialL2 p, polynomialL2 (divergencePolynomial p)) ∈ closedDivergence.graph := by
  apply LinearPMap.le_graph_of_le polynomialDivergence.le_closure
  rw [polynomialDivergence_graph]; exact ⟨p, rfl⟩

/-- On the original core δ₀* really has value p'; no nondense-domain fallback remains. -/
theorem divergence_adjoint_polynomial_graph (p : ℝ[X]) :
    (polynomialL2 p, polynomialL2 p.derivative) ∈ polynomialDivergence.adjoint.graph :=
  LinearPMap.le_graph_of_le polynomialDerivative_le_divergence_adjoint
    (polynomialDerivative_polynomial p)

/-- On the original core D₀* really has value xq-q'. -/
theorem derivative_adjoint_polynomial_graph (p : ℝ[X]) :
    (polynomialL2 p, polynomialL2 (divergencePolynomial p)) ∈
      polynomialDerivative.adjoint.graph := by
  apply LinearPMap.le_graph_of_le polynomialDivergence_le_derivative_adjoint
  rw [polynomialDivergence_graph]; exact ⟨p, rfl⟩

/-- The algebraic polynomial domain is a graph core for its own derivative closure. -/
theorem closedDerivative_has_polynomial_core :
    closedDerivative.HasCore polynomialEmbedding.range := by
  rw [← polynomialDerivative_domain]
  exact polynomialDerivative.closureHasCore

/-- The algebraic polynomial domain is a graph core for its own divergence closure. -/
theorem closedDivergence_has_polynomial_core :
    closedDivergence.HasCore polynomialEmbedding.range := by
  rw [← polynomialDivergence_domain]
  exact polynomialDivergence.closureHasCore

/-- Closing D₀ changes its graph and domain, but not its Hilbert adjoint. -/
theorem closedDerivative_adjoint_eq : closedDerivative.adjoint = polynomialDerivative.adjoint :=
  operatorClosure_adjoint_eq polynomialDerivative_isClosable polynomialDerivative_dense_domain

/-- Closing δ₀ likewise leaves its Hilbert adjoint unchanged. -/
theorem closedDivergence_adjoint_eq : closedDivergence.adjoint = polynomialDivergence.adjoint :=
  operatorClosure_adjoint_eq polynomialDivergence_isClosable polynomialDivergence_dense_domain

/-- Explicit closed-domain derivative inclusion into the adjoint of closed divergence. -/
theorem closedDerivative_le_closedDivergence_adjoint :
    closedDerivative ≤ closedDivergence.adjoint := by
  rw [closedDivergence_adjoint_eq]
  exact closedDerivative_le_divergence_adjoint

/-- Explicit closed-domain divergence inclusion into the adjoint of closed derivative. -/
theorem closedDivergence_le_closedDerivative_adjoint :
    closedDivergence ≤ closedDerivative.adjoint := by
  rw [closedDerivative_adjoint_eq]
  exact closedDivergence_le_derivative_adjoint

/-- Polynomial membership in the closed derivative domain is established independently of values. -/
theorem closedDerivative_polynomial_mem (p : ℝ[X]) :
    polynomialL2 p ∈ closedDerivative.domain :=
  LinearPMap.mem_domain_iff.mpr ⟨polynomialL2 p.derivative, closedDerivative_polynomial_graph p⟩

/-- The closed derivative agrees with the classical polynomial derivative for any domain proof. -/
theorem closedDerivative_polynomial_apply (p : ℝ[X])
    (hp : polynomialL2 p ∈ closedDerivative.domain) :
    closedDerivative ⟨polynomialL2 p, hp⟩ = polynomialL2 p.derivative :=
  closedDerivative.mem_graph_snd_inj (closedDerivative.mem_graph ⟨polynomialL2 p, hp⟩)
    (closedDerivative_polynomial_graph p) rfl

/-- Genuine Gaussian cylinders belong to the closed derivative domain. -/
theorem closedDerivative_cylindrical_mem (h : ℝ) (p : ℝ[X]) :
    cylindricalL2 h p ∈ closedDerivative.domain :=
  closedDerivative_polynomial_mem (coordinatePolynomial h p)

/-- Closing the operator preserves its actual cylindrical Malliavin derivative formula. -/
theorem closedDerivative_cylindrical_coeFn (h : ℝ) (p : ℝ[X])
    (hp : cylindricalL2 h p ∈ closedDerivative.domain) :
    closedDerivative ⟨cylindricalL2 h p, hp⟩ =ᵐ[γ]
      fun x => p.derivative.eval (W h x) * h := by
  unfold cylindricalL2 at hp ⊢
  rw [closedDerivative_polynomial_apply (coordinatePolynomial h p) hp]
  exact cylindricalDerivativeL2_coeFn h p

end OperatorDerivativeRewrite.Foundation.GaussianCore
