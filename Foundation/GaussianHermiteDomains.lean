import Foundation.GaussianHermiteAdjoints

/-! Weighted Hermite domains and explicit graph-norm cores. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

/-- Parseval with genuine coefficients and the Gaussian L² norm. -/
theorem hermiteCoefficient_hasSum_sq (f : GaussianL2) :
    HasSum (fun n : ℕ => hermiteCoefficient f n ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (hermiteBasis.repr f)
  simpa [hermiteBasis_coefficient, hermiteCoefficient, Real.rpow_two,
    Real.norm_eq_abs, sq_abs] using h

/-- Every square-summable real sequence is realized by a Gaussian L² vector. -/
theorem exists_hermite_coefficients (c : ℕ → ℝ) (hc : Summable (fun n : ℕ => c n ^ 2)) :
    ∃ f : GaussianL2, ∀ n, hermiteCoefficient f n = c n := by
  have hm : Memℓp c 2 := memℓp_gen (by
    simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hc)
  refine ⟨hermiteBasis.repr.symm ⟨c, hm⟩, ?_⟩
  intro n
  change inner ℝ (normalizedHermite n) (hermiteBasis.repr.symm ⟨c, hm⟩) = c n
  rw [← hermiteBasis_coefficient, LinearIsometryEquiv.apply_symm_apply]

/-- Squaring a ladder weight gives precisely its integer spectral weight. -/
theorem hermite_weight_square (n : ℕ) (a : ℝ) :
    (Real.sqrt (n + 1 : ℝ) * a) ^ 2 = (n + 1 : ℝ) * a ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- Exact derivative-domain criterion: the weighted Hermite coefficients are square summable. -/
theorem closedDerivative_domain_iff (f : GaussianL2) :
    f ∈ closedDerivative.domain ↔
      Summable (fun n : ℕ => (n : ℝ) * hermiteCoefficient f n ^ 2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g, hg⟩
    have h := (closedDerivative_graph_iff f g).mp hg
    apply (summable_nat_add_iff 1).mp
    convert (hermiteCoefficient_hasSum_sq g).summable using 1
    ext n
    rw [h n, hermite_weight_square, Nat.cast_add, Nat.cast_one]
  · intro hf
    have ht := (summable_nat_add_iff 1).mpr hf
    have hd : Summable (fun n : ℕ =>
        (Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f (n + 1)) ^ 2) := by
      simpa only [hermite_weight_square, Nat.cast_add, Nat.cast_one] using ht
    obtain ⟨g, hg⟩ := exists_hermite_coefficients _ hd
    exact ⟨g, closedDerivative_graph_of_coefficients f g hg⟩

/-- Exact divergence-domain criterion, with the raising weight n+1. -/
theorem closedDivergence_domain_iff (f : GaussianL2) :
    f ∈ closedDivergence.domain ↔
      Summable (fun n : ℕ => (n + 1 : ℝ) * hermiteCoefficient f n ^ 2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g, hg⟩
    have h := ((closedDivergence_graph_iff f g).mp hg).2
    have ht := (summable_nat_add_iff 1).mpr (hermiteCoefficient_hasSum_sq g).summable
    convert ht using 1
    ext n
    rw [h n, hermite_weight_square]
  · intro hf
    let c : ℕ → ℝ := fun n : ℕ => match n with
      | 0 => 0
      | n + 1 => Real.sqrt (n + 1 : ℝ) * hermiteCoefficient f n
    have hc : Summable (fun n : ℕ => c n ^ 2) := by
      apply (summable_nat_add_iff 1).mp
      simpa only [c, hermite_weight_square] using hf
    obtain ⟨g, hg⟩ := exists_hermite_coefficients c hc
    refine ⟨g, closedDivergence_graph_of_coefficients f g (hg 0) ?_⟩
    intro n; exact hg (n + 1)

/-- Both closed operators have the same one-dimensional Gaussian Sobolev domain. -/
theorem closedDerivative_domain_eq_closedDivergence_domain :
    closedDerivative.domain = closedDivergence.domain := by
  ext f
  rw [closedDerivative_domain_iff, closedDivergence_domain_iff]
  have h0 := (hermiteCoefficient_hasSum_sq f).summable
  constructor
  · intro h
    convert h.add h0 using 1
    ext n; ring
  · intro h
    convert h.sub h0 using 1
    ext n; ring

/-- Exact derivative output norm on its closed graph. -/
theorem closedDerivative_norm_sq (f g : GaussianL2) (hg : (f, g) ∈ closedDerivative.graph) :
    ‖g‖ ^ 2 = ∑' n : ℕ, (n : ℝ) * hermiteCoefficient f n ^ 2 := by
  have h := (closedDerivative_graph_iff f g).mp hg
  have hs := (closedDerivative_domain_iff f).mp (LinearPMap.mem_domain_iff.mpr ⟨g, hg⟩)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [← (hermiteCoefficient_hasSum_sq g).tsum_eq]
  apply tsum_congr
  intro n
  rw [h n, hermite_weight_square, Nat.cast_add, Nat.cast_one]

/-- Exact divergence output norm on its closed graph. -/
theorem closedDivergence_norm_sq (f g : GaussianL2) (hg : (f, g) ∈ closedDivergence.graph) :
    ‖g‖ ^ 2 = ∑' n : ℕ, (n + 1 : ℝ) * hermiteCoefficient f n ^ 2 := by
  obtain ⟨h0, h⟩ := (closedDivergence_graph_iff f g).mp hg
  rw [← (hermiteCoefficient_hasSum_sq g).tsum_eq,
    (hermiteCoefficient_hasSum_sq g).summable.tsum_eq_zero_add]
  simp only [h0, zero_pow (by decide : 2 ≠ 0), zero_add]
  apply tsum_congr
  intro n
  rw [h n, hermite_weight_square]

/-- The Hilbert graph norm squared of D̄ is the spectral weight n+1. -/
theorem closedDerivative_graph_norm_sq (f g : GaussianL2)
    (hg : (f, g) ∈ closedDerivative.graph) :
    ‖f‖ ^ 2 + ‖g‖ ^ 2 = ∑' n : ℕ, (n + 1 : ℝ) * hermiteCoefficient f n ^ 2 := by
  have hs := (closedDerivative_domain_iff f).mp (LinearPMap.mem_domain_iff.mpr ⟨g, hg⟩)
  rw [closedDerivative_norm_sq f g hg, ← (hermiteCoefficient_hasSum_sq f).tsum_eq,
    ← (hermiteCoefficient_hasSum_sq f).summable.tsum_add hs]
  apply tsum_congr
  intro n; ring

/-- The Hilbert graph norm squared of δ̄ is the spectral weight n+2. -/
theorem closedDivergence_graph_norm_sq (f g : GaussianL2)
    (hg : (f, g) ∈ closedDivergence.graph) :
    ‖f‖ ^ 2 + ‖g‖ ^ 2 = ∑' n : ℕ, (n + 2 : ℝ) * hermiteCoefficient f n ^ 2 := by
  have hs := (closedDivergence_domain_iff f).mp (LinearPMap.mem_domain_iff.mpr ⟨g, hg⟩)
  rw [closedDivergence_norm_sq f g hg, ← (hermiteCoefficient_hasSum_sq f).tsum_eq,
    ← (hermiteCoefficient_hasSum_sq f).summable.tsum_add hs]
  apply tsum_congr
  intro n; ring

/-- The finite Hermite span is a graph core of the full derivative adjoint δ₀*. -/
theorem divergence_adjoint_has_hermite_core :
    polynomialDivergence.adjoint.HasCore (Submodule.span ℝ (Set.range normalizedHermite)) := by
  rw [← closedDerivative_eq_divergence_adjoint, normalizedHermite_span]
  exact closedDerivative_has_polynomial_core

/-- The finite Hermite span is also a graph core of the full divergence adjoint D₀*. -/
theorem derivative_adjoint_has_hermite_core :
    polynomialDerivative.adjoint.HasCore (Submodule.span ℝ (Set.range normalizedHermite)) := by
  rw [← closedDivergence_eq_derivative_adjoint, normalizedHermite_span]
  exact closedDivergence_has_polynomial_core

/-- Explicit polynomial graph approximants converge in both L² components for every δ₀* pair. -/
theorem divergence_adjoint_hermite_approximation (f g : GaussianL2)
    (hg : (f, g) ∈ polynomialDivergence.adjoint.graph) :
    (∀ N, (hermiteTruncation f (N + 1), hermiteTruncation g N) ∈ polynomialDerivative.graph) ∧
      Tendsto (fun N => (hermiteTruncation f (N + 1), hermiteTruncation g N)) atTop (𝓝 (f, g)) :=
  ⟨hermiteTruncation_derivative_graph f g (divergence_adjoint_coefficients hg),
    ((hermiteTruncation_tendsto f).comp (tendsto_add_atTop_nat 1)).prodMk_nhds
      (hermiteTruncation_tendsto g)⟩

/-- Explicit polynomial graph approximants converge in both L² components for every D₀* pair. -/
theorem derivative_adjoint_hermite_approximation (f g : GaussianL2)
    (hg : (f, g) ∈ polynomialDerivative.adjoint.graph) :
    (∀ N, (hermiteTruncation f N, hermiteTruncation g (N + 1)) ∈ polynomialDivergence.graph) ∧
      Tendsto (fun N => (hermiteTruncation f N, hermiteTruncation g (N + 1))) atTop (𝓝 (f, g)) :=
  ⟨hermiteTruncation_divergence_graph f g (derivative_adjoint_coefficient_zero hg)
      (derivative_adjoint_coefficients hg),
    (hermiteTruncation_tendsto f).prodMk_nhds
      ((hermiteTruncation_tendsto g).comp (tendsto_add_atTop_nat 1))⟩

end OperatorDerivativeRewrite.Foundation.GaussianCore
