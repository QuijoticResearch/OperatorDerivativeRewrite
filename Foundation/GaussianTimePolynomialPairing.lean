import Foundation.GaussianTimeFieldNorm

/-!
# Pairings of arbitrary polynomial predictable time steps

The intervals may overlap and need not belong to one partition.  Ordering their
left endpoints makes both coefficient derivatives vanish in the later interval
direction.  Gaussian Stein and the genuine polynomial product rule then give
the exact field/integral pairing, with no refinement or graph-density assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimePolynomialPairing

open InfiniteGaussian GaussianTimeDivergence GaussianTimeFieldNorm
set_option backward.isDefEq.respectTransparency false

/-- A first-chaos coordinate belongs to the genuine polynomial operator domain. -/
def firstChaosPolynomial (h : CoefficientSpace) : polynomialCylindricalDomain :=
  ⟨isonormalCylinderL2 (fun _ : Unit => h) (X ()), isonormalCylinderL2_mem_core _ _⟩

theorem firstChaosPolynomial_coeFn (h : CoefficientSpace) :
    (firstChaosPolynomial h : GaussianL2) =ᵐ[gaussianProduct] firstChaosEmbedding h := by
  simpa only [firstChaosPolynomial, isonormalCylinder_X] using
    isonormalCylinderL2_coeFn (fun _ : Unit => h) (X ())

/-- Its actual derivative is the constant coefficient vector. -/
theorem firstChaosPolynomial_derivative_coeFn (h : CoefficientSpace) :
    polynomialDerivative (firstChaosPolynomial h) =ᵐ[gaussianProduct] fun _ => h := by
  unfold firstChaosPolynomial
  rw [polynomialDerivative_on_cylinder]
  filter_upwards [isonormalCylinderGradientL2_coeFn (fun _ : Unit => h) (X ())]
    with ω hω
  simpa only [isonormalCylinderGradient_X] using hω

/-- The existing quotient-level Leibniz theorem gives actual representative values. -/
theorem polynomialDerivative_product_ae (f g : polynomialCylindricalDomain) :
    polynomialDerivative (polynomialProduct f g) =ᵐ[gaussianProduct]
      fun ω => (f : GaussianL2) ω • polynomialDerivative g ω +
        (g : GaussianL2) ω • polynomialDerivative f ω := by
  rw [polynomialDerivative_product]
  filter_upwards [Lp.coeFn_add (polynomialTimesDerivative f g) (polynomialTimesDerivative g f),
    polynomialTimesDerivative_coeFn f g, polynomialTimesDerivative_coeFn g f]
    with ω ha hfg hgf
  simp only [ha, Pi.add_apply, hfg, hgf]

/-- One first-order Stein calculation pairs two coefficient-times-coordinate
products when both actual coefficient derivatives vanish in the second direction. -/
theorem firstChaos_product_pairing_of_directional_zero
    (f g : polynomialCylindricalDomain) (h k : CoefficientSpace)
    (hf : (fun ω => inner ℝ (polynomialDerivative f ω) k) =ᵐ[gaussianProduct] fun _ => 0)
    (hg : (fun ω => inner ℝ (polynomialDerivative g ω) k) =ᵐ[gaussianProduct] fun _ => 0) :
    (∫ ω, ((f : GaussianL2) ω * firstChaosEmbedding h ω) *
      ((g : GaussianL2) ω * firstChaosEmbedding k ω) ∂gaussianProduct) =
      (∫ ω, (f : GaussianL2) ω * (g : GaussianL2) ω ∂gaussianProduct) * inner ℝ h k := by
  let fg := polynomialProduct f g
  let F := polynomialProduct fg (firstChaosPolynomial h)
  have hD : (fun ω => inner ℝ (polynomialDerivative F ω) k) =ᵐ[gaussianProduct]
      fun ω => (f : GaussianL2) ω * (g : GaussianL2) ω * inner ℝ h k := by
    filter_upwards [polynomialDerivative_product_ae fg (firstChaosPolynomial h),
      polynomialDerivative_product_ae f g, polynomialProductL2_coeFn f g,
      firstChaosPolynomial_derivative_coeFn h, hf, hg] with ω hF hfg hval hh hf hg
    change inner ℝ (polynomialDerivative (polynomialProduct fg (firstChaosPolynomial h)) ω) k = _
    rw [hF]
    change polynomialDerivative fg ω = _ at hfg
    change (fg : GaussianL2) ω = _ at hval
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hh, hfg, hval, inner_add_left, real_inner_smul_left, real_inner_smul_left, hf, hg]
    ring
  have hF : (fun ω => (F : GaussianL2) ω * firstChaosEmbedding k ω) =ᵐ[gaussianProduct]
      fun ω => ((f : GaussianL2) ω * firstChaosEmbedding h ω) *
        ((g : GaussianL2) ω * firstChaosEmbedding k ω) := by
    filter_upwards [polynomialProductL2_coeFn fg (firstChaosPolynomial h),
      polynomialProductL2_coeFn f g, firstChaosPolynomial_coeFn h] with ω hF hfg hh
    change (F : GaussianL2) ω = _ at hF
    change (fg : GaussianL2) ω = _ at hfg
    rw [hF, hfg, hh]
    ring
  have hint : Integrable (fun ω => ((f : GaussianL2) ω * firstChaosEmbedding h ω) *
      ((g : GaussianL2) ω * firstChaosEmbedding k ω)) gaussianProduct :=
    (polynomial_times_firstChaos_memLp f h 2 (by simp)).integrable_mul
      (polynomial_times_firstChaos_memLp g k 2 (by simp))
  have hfgInt : Integrable (fun ω => (f : GaussianL2) ω * (g : GaussianL2) ω)
      gaussianProduct := (Lp.memLp (f : GaussianL2)).integrable_mul (Lp.memLp (g : GaussianL2))
  have hs := polynomialDerivative_stein F k
  rw [integral_congr_ae hD, integral_congr_ae hF, integral_mul_const] at hs
  exact hs.symm

/-- Ordered left endpoints suffice; the intervals themselves may overlap. -/
theorem incrementProduct_inner_of_left_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) (s t : ℝ≥0)
    (q : κ → ℝ≥0) (v : MvPolynomial κ ℝ) (a b : ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (hqa : ∀ j, q j ≤ a)
    (hst : s ≤ t) (hab : a ≤ b) (hsa : s ≤ a) :
    inner ℝ (incrementProductL2 r p s t) (incrementProductL2 q v a b) =
      inner ℝ (scalarTensor (incrementDirection s t) (pastCoefficient r p))
        (scalarTensor (incrementDirection a b) (pastCoefficient q v)) := by
  have hs := firstChaos_product_pairing_of_directional_zero
    (pastCoefficient r p) (pastCoefficient q v) (incrementDirection s t) (incrementDirection a b)
    (pastCoefficient_gradient_inner_increment r p a b (fun i => (hrs i).trans hsa) hab)
    (pastCoefficient_gradient_inner_increment q v a b hqa hab)
  rw [scalarTensor_pair_inner, L2_inner_eq_integral, L2_inner_eq_integral]
  have hl : (fun ω => inner ℝ (incrementProductL2 r p s t ω)
      (incrementProductL2 q v a b ω)) =ᵐ[gaussianProduct]
      fun ω => ((pastCoefficient r p : GaussianL2) ω *
        firstChaosEmbedding (incrementDirection s t) ω) *
        ((pastCoefficient q v : GaussianL2) ω *
          firstChaosEmbedding (incrementDirection a b) ω) := by
    filter_upwards [incrementProductL2_coeFn r p s t, incrementProductL2_coeFn q v a b,
      pastCoefficient_coeFn r p, pastCoefficient_coeFn q v,
      GaussianTimeProcess.process_increment_ae s t hst,
      GaussianTimeProcess.process_increment_ae a b hab] with ω hI hJ hf hg hW hV
    change firstChaosEmbedding (incrementDirection s t) ω = _ at hW
    change firstChaosEmbedding (incrementDirection a b) ω = _ at hV
    simp [hI, hJ, hf, hg, hW, hV, mul_comm]
  rw [integral_congr_ae hl]
  simpa only [Real.inner_apply, mul_comm] using hs

/-- Actual field and integral pairings agree for any two polynomial past steps,
without a common partition or an orthogonality assumption on their intervals. -/
theorem incrementProduct_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) (s t : ℝ≥0)
    (q : κ → ℝ≥0) (v : MvPolynomial κ ℝ) (a b : ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (hqa : ∀ j, q j ≤ a)
    (hst : s ≤ t) (hab : a ≤ b) :
    inner ℝ (incrementProductL2 r p s t) (incrementProductL2 q v a b) =
      inner ℝ (scalarTensor (incrementDirection s t) (pastCoefficient r p))
        (scalarTensor (incrementDirection a b) (pastCoefficient q v)) := by
  rcases le_total s a with hsa | has
  · exact incrementProduct_inner_of_left_le r p s t q v a b hrs hqa hst hab hsa
  · rw [real_inner_comm, real_inner_comm (scalarTensor _ _)]
    exact incrementProduct_inner_of_left_le q v a b r p s t hqa hrs hab hst has

/-- Genuine polynomial past-step graph pairs, parameterized over finite natural
index types so that their algebraic span is an actual ambient submodule. -/
def elementaryTimeGraphGenerators : Set (GaussianVectorL2 × GaussianL2) :=
  {z | ∃ (n : ℕ) (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ) (s t : ℝ≥0),
    (∀ i, r i ≤ s) ∧ s ≤ t ∧
      z = (scalarTensor (incrementDirection s t) (pastCoefficient r p),
        incrementProductL2 r p s t)}

/-- The algebraic graph span of actual polynomial predictable time steps.
No density in the full predictable space is asserted by this definition. -/
def elementaryTimeGraph : Submodule ℝ (GaussianVectorL2 × GaussianL2) :=
  Submodule.span ℝ elementaryTimeGraphGenerators

/-- Every graph generator has its proved cylindrical-divergence value. -/
theorem elementaryTimeGraph_le_cylindricalDivergence_graph :
    elementaryTimeGraph ≤ cylindricalDivergence.graph := by
  apply Submodule.span_le.mpr
  rintro z ⟨n, r, p, s, t, hrs, hst, rfl⟩
  exact pastCoefficient_cylindricalDivergence_graph r p s t hrs hst

/-- The algebraic time-step graph is contained in the actual full adjoint graph. -/
theorem elementaryTimeGraph_le_hilbertDivergence_graph :
    elementaryTimeGraph ≤ hilbertDivergence.graph :=
  elementaryTimeGraph_le_cylindricalDivergence_graph.trans
    (LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence)

/-- All pairings on the algebraic graph span are preserved, even for sums of
steps whose intervals overlap and were specified using different partitions. -/
theorem elementaryTimeGraph_pairing (z w : GaussianVectorL2 × GaussianL2)
    (hz : z ∈ elementaryTimeGraph) (hw : w ∈ elementaryTimeGraph) :
    inner ℝ z.2 w.2 = inner ℝ z.1 w.1 := by
  refine Submodule.span_induction₂
    (p := fun z w _ _ => inner ℝ z.2 w.2 = inner ℝ z.1 w.1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hw
  · rintro z w ⟨n, r, p, s, t, hrs, hst, rfl⟩
      ⟨m, q, v, a, b, hqa, hab, rfl⟩
    exact incrementProduct_inner r p s t q v a b hrs hqa hst hab
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz hxz hyz
    simp only [Prod.fst_add, Prod.snd_add, inner_add_left, hxz, hyz]
  · intro x y z hx hy hz hxy hxz
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hxy, hxz]
  · intro a x y hx hy hxy
    change inner ℝ (a • x.2) y.2 = inner ℝ (a • x.1) y.1
    simp only [real_inner_smul_left, hxy]
  · intro a x y hx hy hxy
    change inner ℝ x.2 (a • y.2) = inner ℝ x.1 (a • y.1)
    simp only [inner_smul_right, hxy]

/-- The genuine divergence is isometric on the entire algebraic time-step graph. -/
theorem elementaryTimeGraph_norm (z : GaussianVectorL2 × GaussianL2)
    (hz : z ∈ elementaryTimeGraph) : ‖z.2‖ = ‖z.1‖ := by
  have he := elementaryTimeGraph_pairing z z hz hz
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg z.1, norm_nonneg z.2]

end OperatorDerivativeRewrite.Foundation.GaussianTimePolynomialPairing
