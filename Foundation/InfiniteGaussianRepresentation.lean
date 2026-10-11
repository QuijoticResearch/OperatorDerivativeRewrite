import Foundation.InfiniteGaussianCylinders

/-! Finite Hilbert realizations and representation independence of polynomial cylinders. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

section FiniteRealization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual finite Hilbert random vector obtained from W on an orthonormal basis. -/
def finiteGaussianPoint (A : E →ₗᵢ[ℝ] CoefficientSpace) (ω : SampleSpace) : E :=
  ∑ i, firstChaosEmbedding (A (stdOrthonormalBasis ℝ E i)) ω • stdOrthonormalBasis ℝ E i

theorem finiteGaussianPoint_measurable (A : E →ₗᵢ[ℝ] CoefficientSpace) :
    Measurable (finiteGaussianPoint A) := by
  unfold finiteGaussianPoint
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every direction in the finite space has its actual W coordinate. -/
theorem finiteGaussianPoint_coordinate (A : E →ₗᵢ[ℝ] CoefficientSpace) (v : E) :
    firstChaosEmbedding (A v) =ᵐ[gaussianProduct]
      fun ω => inner ℝ v (finiteGaussianPoint A ω) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hs : (∑ i, inner ℝ (b i) v • A (b i)) = A v := by
    simpa only [map_sum, map_smul] using congrArg A (b.sum_repr' v)
  filter_upwards [firstChaos_linearCombination_ae (fun i => A (b i))
    (fun i => inner ℝ (b i) v)] with ω hw
  rw [hs] at hw
  rw [hw]
  simp only [finiteGaussianPoint, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm v, mul_comm]

theorem finiteGaussianPoint_law (A : E →ₗᵢ[ℝ] CoefficientSpace) :
    gaussianProduct.map (finiteGaussianPoint A) = stdGaussian E := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_eq_charFun_map_inner_one (finiteGaussianPoint_measurable A).aemeasurable]
  have he : (fun ω => inner ℝ (finiteGaussianPoint A ω) t) =ᵐ[gaussianProduct]
      firstChaosEmbedding (A t) := by
    filter_upwards [finiteGaussianPoint_coordinate A t] with ω hw
    rw [real_inner_comm, ← hw]
  rw [Measure.map_congr he, firstChaos_charFun, charFun_stdGaussian]
  simp [A.norm_map, Complex.ofReal_pow]

variable {ι : Type*} [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
/-- Scalar cylinder transport to the genuine standard Gaussian finite-space model. -/
theorem isonormalCylinder_finiteGaussianPoint [Finite ι] (A : E →ₗᵢ[ℝ] CoefficientSpace)
    (h : ι → E) (p : MvPolynomial ι ℝ) :
    isonormalCylinder (fun i => A (h i)) p =ᵐ[gaussianProduct]
      fun ω => FiniteGaussian.cylinder h p (finiteGaussianPoint A ω) := by
  let := Fintype.ofFinite ι
  filter_upwards [ae_all_iff.2 (fun i => finiteGaussianPoint_coordinate A (h i))] with ω hw
  unfold isonormalCylinder FiniteGaussian.cylinder
  apply congrArg (fun x : ι → ℝ => MvPolynomial.eval x p)
  funext i
  exact hw i

omit [MeasurableSpace E] [BorelSpace E] in
/-- Gradient transport uses the isometric inclusion, not formal equality of polynomials. -/
theorem isonormalCylinderGradient_finiteGaussianPoint (A : E →ₗᵢ[ℝ] CoefficientSpace)
    (h : ι → E) (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradient (fun i => A (h i)) p =ᵐ[gaussianProduct]
      fun ω => A (FiniteGaussian.cylinderGradient h p (finiteGaussianPoint A ω)) := by
  filter_upwards [ae_all_iff.2 (fun i =>
    isonormalCylinder_finiteGaussianPoint A h (pderiv i p))] with ω hw
  simp only [isonormalCylinderGradient, FiniteGaussian.cylinderGradient, map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => by rw [hw i])

end FiniteRealization

/-- Equality of scalar L² cylinders implies equality of their genuine Hilbert-valued gradients,
for arbitrary different finite families, including dependent coordinates. -/
theorem isonormalCylinderGradientL2_representation_independent
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (h : ι → CoefficientSpace) (k : κ → CoefficientSpace)
    (p : MvPolynomial ι ℝ) (q : MvPolynomial κ ℝ)
    (he : isonormalCylinderL2 h p = isonormalCylinderL2 k q) :
    isonormalCylinderGradientL2 h p = isonormalCylinderGradientL2 k q := by
  classical
  let S := Submodule.span ℝ (Set.range h ∪ Set.range k)
  let : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range h).union (Set.finite_range k))
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let h' : ι → S := fun i => ⟨h i,
    Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i))⟩
  let k' : κ → S := fun j => ⟨k j,
    Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self j))⟩
  have ha : isonormalCylinder h p =ᵐ[gaussianProduct] isonormalCylinder k q :=
    (isonormalCylinderL2_coeFn h p).symm.trans (he ▸ isonormalCylinderL2_coeFn k q)
  have hp := isonormalCylinder_finiteGaussianPoint S.subtypeₗᵢ h' p
  have hq := isonormalCylinder_finiteGaussianPoint S.subtypeₗᵢ k' q
  have hs : FiniteGaussian.cylinder h' p =ᵐ[stdGaussian S] FiniteGaussian.cylinder k' q := by
    rw [← finiteGaussianPoint_law S.subtypeₗᵢ]
    apply (ae_map_iff (finiteGaussianPoint_measurable S.subtypeₗᵢ).aemeasurable
      (isClosed_eq (FiniteGaussian.cylinder_continuous h' p)
        (FiniteGaussian.cylinder_continuous k' q)).measurableSet).2
    exact hp.symm.trans (ha.trans hq)
  have hg := FiniteGaussian.cylinderGradient_representation_independent h' k' p q hs
  have hgp := isonormalCylinderGradient_finiteGaussianPoint S.subtypeₗᵢ h' p
  have hgq := isonormalCylinderGradient_finiteGaussianPoint S.subtypeₗᵢ k' q
  have hga : isonormalCylinderGradient h p =ᵐ[gaussianProduct]
      isonormalCylinderGradient k q := by
    filter_upwards [hgp, hgq] with ω hpω hqω
    exact hpω.trans ((congrArg (fun f => S.subtypeₗᵢ (f (finiteGaussianPoint S.subtypeₗᵢ ω)))
      hg).trans hqω.symm)
  apply Lp.ext
  exact (isonormalCylinderGradientL2_coeFn h p).trans
    (hga.trans (isonormalCylinderGradientL2_coeFn k q).symm)
end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
