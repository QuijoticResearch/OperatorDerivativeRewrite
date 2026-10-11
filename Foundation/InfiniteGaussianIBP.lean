import Foundation.FiniteGaussianDirectionalIBP
import Foundation.InfiniteGaussianVectorCore

/-! Gaussian Stein and integration by parts for genuine polynomial cylinders. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Directional Stein for arbitrary finite isonormal polynomial representations. -/
theorem isonormalCylinder_stein {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) (v : CoefficientSpace) :
    (∫ ω, inner ℝ (isonormalCylinderGradient h p ω) v ∂gaussianProduct) =
      ∫ ω, isonormalCylinder h p ω * firstChaosEmbedding v ω ∂gaussianProduct := by
  classical
  let S := Submodule.span ℝ (Set.range h ∪ {v})
  let : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range h).union (Set.finite_singleton v))
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let a : ι → S := fun i => ⟨h i,
    Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i))⟩
  let w : S := ⟨v, Submodule.subset_span (Set.mem_union_right _ (Set.mem_singleton v))⟩
  let A := S.subtypeₗᵢ
  have hg : Continuous (FiniteGaussian.cylinderGradient a p) := by
    unfold FiniteGaussian.cylinderGradient
    exact continuous_finsetSum _ (fun i _ =>
      (FiniteGaussian.cylinder_continuous a (pderiv i p)).smul continuous_const)
  have hr : Continuous (fun x : S => FiniteGaussian.cylinder a p x * inner ℝ w x) :=
    (FiniteGaussian.cylinder_continuous a p).mul (continuous_const.inner continuous_id)
  calc
    _ = ∫ x : S, inner ℝ (FiniteGaussian.cylinderGradient a p x) w ∂stdGaussian S := by
      rw [← finiteGaussianPoint_law A,
        integral_map (finiteGaussianPoint_measurable A).aemeasurable
          (hg.inner continuous_const).aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [isonormalCylinderGradient_finiteGaussianPoint A a p] with ω hw
      change isonormalCylinderGradient h p ω =
        A (FiniteGaussian.cylinderGradient a p (finiteGaussianPoint A ω)) at hw
      change inner ℝ (isonormalCylinderGradient h p ω) (A w) = _
      rw [hw]
      exact A.inner_map_map _ w
    _ = ∫ x : S, FiniteGaussian.cylinder a p x * inner ℝ w x ∂stdGaussian S :=
      FiniteGaussian.cylinder_stein a p w
    _ = _ := by
      rw [← finiteGaussianPoint_law A,
        integral_map (finiteGaussianPoint_measurable A).aemeasurable hr.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [isonormalCylinder_finiteGaussianPoint A a p,
        finiteGaussianPoint_coordinate A w] with ω hp hv
      change isonormalCylinder h p ω =
        FiniteGaussian.cylinder a p (finiteGaussianPoint A ω) at hp
      change firstChaosEmbedding v ω = inner ℝ w (finiteGaussianPoint A ω) at hv
      rw [hp, hv]

/-- Directional Stein on the genuine scalar L² polynomial operator domain. -/
theorem polynomialDerivative_stein (f : polynomialCylindricalDomain) (h : CoefficientSpace) :
    (∫ ω, inner ℝ (polynomialDerivative f ω) h ∂gaussianProduct) =
      ∫ ω, (f : GaussianL2) ω * firstChaosEmbedding h ω ∂gaussianProduct := by
  let a := polynomialRepresentation f
  calc
    _ = ∫ ω, inner ℝ (isonormalCylinderGradient a.directions a.polynomial ω) h
        ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [isonormalCylinderGradientL2_coeFn a.directions a.polynomial] with ω hw
      exact congrArg (inner ℝ · h) hw
    _ = ∫ ω, isonormalCylinder a.directions a.polynomial ω * firstChaosEmbedding h ω
        ∂gaussianProduct := isonormalCylinder_stein _ _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [a.represents ▸ isonormalCylinderL2_coeFn a.directions a.polynomial]
        with ω hw
      rw [hw]

/-- Multiplication by W(h) is integrable on the polynomial domain, using fourth moments. -/
theorem polynomial_times_firstChaos_memLp (g : polynomialCylindricalDomain)
    (h : CoefficientSpace) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => (g : GaussianL2) ω * firstChaosEmbedding h ω) r gaussianProduct := by
  have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
  have : ENNReal.HolderTriple (2 * r) (2 * r) r := FiniteGaussian.doubled_holderTriple r
  exact (polynomialDomain_memLp g (2 * r) ht).fun_mul ((firstChaos_hasGaussianLaw h).memLp ht)

/-- All finite moments of the actual directional derivative coefficient. -/
theorem polynomial_directional_memLp (g : polynomialCylindricalDomain)
    (h : CoefficientSpace) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => inner ℝ (polynomialDerivative g ω) h) r gaussianProduct :=
  inner_memLp (polynomialDerivative_memLp g r hr)
    (memLp_const h : MemLp (fun _ : SampleSpace => h) ∞ gaussianProduct)

/-- All finite moments of the genuine rank-one divergence expression. -/
theorem rankDivergence_memLp (g : polynomialCylindricalDomain) (h : CoefficientSpace)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => (g : GaussianL2) ω * firstChaosEmbedding h ω -
      inner ℝ (polynomialDerivative g ω) h) r gaussianProduct :=
  (polynomial_times_firstChaos_memLp g h r hr).sub (polynomial_directional_memLp g h r hr)

/-- The genuine scalar L² expression δ₀(Gh)=G W(h)−⟨DG,h⟩. -/
def rankDivergence (g : polynomialCylindricalDomain) (h : CoefficientSpace) : GaussianL2 :=
  (rankDivergence_memLp g h 2 (by simp)).toLp _

theorem rankDivergence_coeFn (g : polynomialCylindricalDomain) (h : CoefficientSpace) :
    rankDivergence g h =ᵐ[gaussianProduct] fun ω =>
      (g : GaussianL2) ω * firstChaosEmbedding h ω - inner ℝ (polynomialDerivative g ω) h :=
  MemLp.coeFn_toLp _


/-- Genuine Gaussian IBP for an actual rank-one polynomial field. -/
theorem polynomialDerivative_rank_integration_by_parts
    (f g : polynomialCylindricalDomain) (h : CoefficientSpace) :
    (∫ ω, inner ℝ (polynomialDerivative f ω) (scalarTensor h g ω) ∂gaussianProduct) =
      ∫ ω, (f : GaussianL2) ω * rankDivergence g h ω ∂gaussianProduct := by
  have hi (a b : polynomialCylindricalDomain) :
      Integrable (fun ω => (a : GaussianL2) ω * inner ℝ (polynomialDerivative b ω) h)
        gaussianProduct :=
    mul_L2_integrable (Lp.memLp (a : GaussianL2)) (polynomial_directional_memLp b h 2 (by simp))
  have hc : Integrable (fun ω => (f : GaussianL2) ω *
      ((g : GaussianL2) ω * firstChaosEmbedding h ω)) gaussianProduct :=
    mul_L2_integrable (Lp.memLp (f : GaussianL2))
      (polynomial_times_firstChaos_memLp g h 2 (by simp))
  have hleft : (∫ ω, inner ℝ (polynomialDerivative (polynomialProduct f g) ω) h
      ∂gaussianProduct) = ∫ ω, (f : GaussianL2) ω * inner ℝ (polynomialDerivative g ω) h +
        (g : GaussianL2) ω * inner ℝ (polynomialDerivative f ω) h ∂gaussianProduct := by
    rw [polynomialDerivative_product]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (polynomialTimesDerivative f g) (polynomialTimesDerivative g f),
      polynomialTimesDerivative_coeFn f g, polynomialTimesDerivative_coeFn g f]
        with ω hadd hfg hgf
    rw [hadd]
    simp only [Pi.add_apply, hfg, hgf, inner_add_left, real_inner_smul_left]
  have hright : (∫ ω, (polynomialProduct f g : GaussianL2) ω * firstChaosEmbedding h ω
      ∂gaussianProduct) = ∫ ω, (f : GaussianL2) ω *
        ((g : GaussianL2) ω * firstChaosEmbedding h ω) ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [polynomialProductL2_coeFn f g] with ω hw
    simp only [polynomialProduct, hw, mul_assoc]
  have hs := polynomialDerivative_stein (polynomialProduct f g) h
  rw [hleft, hright, integral_add (hi f g) (hi g f)] at hs
  have hl : (∫ ω, inner ℝ (polynomialDerivative f ω) (scalarTensor h g ω) ∂gaussianProduct) =
      ∫ ω, (g : GaussianL2) ω * inner ℝ (polynomialDerivative f ω) h ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [scalarTensor_coeFn h g] with ω hw
    simp [hw, inner_smul_right]
  have hr : (∫ ω, (f : GaussianL2) ω * rankDivergence g h ω ∂gaussianProduct) =
      (∫ ω, (f : GaussianL2) ω * ((g : GaussianL2) ω * firstChaosEmbedding h ω) ∂gaussianProduct) -
        ∫ ω, (f : GaussianL2) ω * inner ℝ (polynomialDerivative g ω) h ∂gaussianProduct := by
    calc
      _ = ∫ ω, (f : GaussianL2) ω * ((g : GaussianL2) ω * firstChaosEmbedding h ω) -
          (f : GaussianL2) ω * inner ℝ (polynomialDerivative g ω) h ∂gaussianProduct := by
        apply integral_congr_ae
        filter_upwards [rankDivergence_coeFn g h] with ω hw
        rw [hw, mul_sub]
      _ = _ := integral_sub hc (hi f g)
  rw [hl, hr]
  linarith

/-- Hilbert-space adjoint pairing on actual rank-one polynomial fields. -/
theorem polynomialDerivative_rank_pairing (f g : polynomialCylindricalDomain)
    (h : CoefficientSpace) :
    inner ℝ (polynomialDerivative f) (scalarTensor h g) =
      inner ℝ (f : GaussianL2) (rankDivergence g h) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  simpa [Real.inner_apply, mul_comm] using polynomialDerivative_rank_integration_by_parts f g h
end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
