import Foundation.InfiniteGaussianPolynomialProducts

/-! Genuine finite-rank polynomial vector fields and their L² density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

abbrev GaussianVectorL2 := Lp CoefficientSpace 2 gaussianProduct

/-- Actual rank-one multiplication f ↦ f h, a bounded linear map on scalar L². -/
def scalarTensor (h : CoefficientSpace) : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight h).compLpL 2 gaussianProduct

theorem scalarTensor_coeFn (h : CoefficientSpace) (f : GaussianL2) :
    scalarTensor h f =ᵐ[gaussianProduct] fun ω => f ω • h :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight h).coeFn_compLpL f

/-- The finite-rank polynomial vector core is the algebraic span of actual G h fields. -/
def cylindricalVectorDomain : Submodule ℝ GaussianVectorL2 :=
  Submodule.span ℝ {u | ∃ (g : polynomialCylindricalDomain) (h : CoefficientSpace),
    scalarTensor h g = u}

theorem scalarTensor_mem_domain (g : polynomialCylindricalDomain) (h : CoefficientSpace) :
    scalarTensor h g ∈ cylindricalVectorDomain := Submodule.subset_span ⟨g, h, rfl⟩

/-- Hilbert pairing with a rank-one field is scalar pairing with its coordinate projection. -/
theorem scalarTensor_inner (h : CoefficientSpace) (f : GaussianL2) (u : GaussianVectorL2) :
    inner ℝ (scalarTensor h f) u =
      inner ℝ f ((innerSL ℝ h).compLpL 2 gaussianProduct u) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [scalarTensor_coeFn h f,
    (innerSL ℝ h).coeFn_compLpL u] with ω ht hc
  simp [ht, hc, real_inner_smul_left, mul_comm]

/-- Scalar cylinder density and ℓ² coordinate completeness force an orthogonal field to vanish. -/
theorem eq_zero_of_cylindricalVector_orthogonal (u : GaussianVectorL2)
    (hu : ∀ (g : polynomialCylindricalDomain) (h : CoefficientSpace),
      inner ℝ (scalarTensor h g) u = 0) : u = 0 := by
  have hc (h : CoefficientSpace) : (innerSL ℝ h).compLpL 2 gaussianProduct u = 0 := by
    let v := (innerSL ℝ h).compLpL 2 gaussianProduct u
    have he : (fun f : GaussianL2 => inner ℝ f v) = fun _ => (0 : ℝ) := by
      apply Continuous.ext_on polynomialCylindricalDomain_dense
        (continuous_id.inner continuous_const) continuous_const
      intro f hf
      exact (scalarTensor_inner h f u).symm.trans (hu ⟨f, hf⟩ h)
    exact inner_self_eq_zero.mp (congrFun he v)
  have ha (n : ℕ) : (fun ω => inner ℝ (lp.single 2 n (1 : ℝ)) (u ω)) =ᵐ[gaussianProduct]
      fun _ => (0 : ℝ) := by
    have he := (innerSL ℝ (lp.single 2 n (1 : ℝ))).coeFn_compLpL u
    rw [hc] at he
    exact he.symm.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct))
  apply Lp.ext
  filter_upwards [ae_all_iff.2 ha,
    Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := gaussianProduct)] with ω hω hz
  rw [hz]
  apply Subtype.ext
  funext n
  have hn := hω n
  simpa [lp.inner_single_left, Real.inner_apply] using hn

/-- Finite-rank polynomial fields are dense in the entire ℓ²-valued Gaussian L² space. -/
theorem cylindricalVectorDomain_dense : Dense (cylindricalVectorDomain : Set GaussianVectorL2) := by
  have hb : cylindricalVectorDomain.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply eq_zero_of_cylindricalVector_orthogonal u
    intro g h
    exact cylindricalVectorDomain.topologicalClosure.inner_right_of_mem_orthogonal
      (cylindricalVectorDomain.le_topologicalClosure (scalarTensor_mem_domain g h)) hu
  have ht := Submodule.orthogonal_eq_bot_iff.mp hb
  rw [dense_iff_closure_eq]
  change (cylindricalVectorDomain.topologicalClosure : Set GaussianVectorL2) = Set.univ
  rw [ht]
  rfl

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
