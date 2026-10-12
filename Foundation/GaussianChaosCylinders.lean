import Foundation.GaussianChaosGraphConvergence
import Foundation.GaussianPastFirstChaos

/-! Orthogonal chaos projections preserve the actual polynomial algebra of an
arbitrary finite Gaussian observation family. No covariance inverse is used. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian FiniteGaussian
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
variable {ι : Type*} [Fintype ι]

def cylinderCore (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    polynomialCylindricalDomain := ⟨isonormalCylinderL2 h p, isonormalCylinderL2_mem_core h p⟩

theorem cylinder_gradient_expansion (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    polynomialDerivative (cylinderCore h p) =
      cylindricalField (fun i => cylinderCore h (pderiv i p)) h := by
  rw [show polynomialDerivative (cylinderCore h p) = isonormalCylinderGradientL2 h p from
    polynomialDerivative_on_cylinder h p]
  apply Lp.ext
  filter_upwards [isonormalCylinderGradientL2_coeFn h p,
    Lp.coeFn_finsetSum Finset.univ (fun i => scalarTensor (h i) (cylinderCore h (pderiv i p))),
    ae_all_iff.mpr (fun i => scalarTensor_coeFn (h i) (cylinderCore h (pderiv i p))),
    ae_all_iff.mpr (fun i => isonormalCylinderL2_coeFn h (pderiv i p))] with ω hg hs ht hp
  change _ = (∑ i, scalarTensor (h i) (cylinderCore h (pderiv i p))) ω
  rw [hg, hs]
  simp only [isonormalCylinderGradient, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i]
  change _ = isonormalCylinderL2 h (pderiv i p) ω • h i
  rw [hp i]

theorem orthonormal_rankDivergence (h : ι → CoefficientSpace) (hh : Orthonormal ℝ h)
    (p : MvPolynomial ι ℝ) (i : ι) :
    rankDivergence (cylinderCore h p) (h i) =
      isonormalCylinderL2 h (coordinateDivergencePolynomial i p) := by
  classical
  apply Lp.ext
  have hd := isonormalCylinderGradientL2_coeFn h p
  rw [← polynomialDerivative_on_cylinder h p] at hd
  filter_upwards [rankDivergence_coeFn (cylinderCore h p) (h i),
    isonormalCylinderL2_coeFn h p, hd,
    isonormalCylinderL2_coeFn h (coordinateDivergencePolynomial i p)] with ω hr hp hd ho
  change polynomialDerivative (cylinderCore h p) ω = _ at hd
  rw [hr, ho, hd]
  change isonormalCylinderL2 h p ω * firstChaosEmbedding (h i) ω - _ = _
  rw [hp]
  simp [isonormalCylinderGradient, sum_inner, real_inner_smul_left,
    orthonormal_iff_ite.mp hh, coordinateDivergencePolynomial, isonormalCylinder, mul_comm]

theorem orthonormal_tensor_mem_sector (h : ι → CoefficientSpace) (hh : Orthonormal ℝ h)
    (α : ι → ℕ) :
    isonormalCylinderL2 h (tensorHermitePolynomial α) ∈ sector (∑ i, α i) := by
  classical
  let p := tensorHermitePolynomial α
  apply (mem_sector _ _).mpr
  refine ⟨polynomialDerivative (cylinderCore h p),
    closedCylindricalDerivative_core_graph (cylinderCore h p), ?_⟩
  have hg := cylindricalDivergence_field_graph (fun i => cylinderCore h (pderiv i p)) h
  have he : cylindricalDivergenceExpression (fun i => cylinderCore h (pderiv i p)) h =
      ((∑ i, α i : ℕ) : ℝ) • isonormalCylinderL2 h p := by
    change (∑ i, rankDivergence (cylinderCore h (pderiv i p)) (h i)) = _
    simp only [orthonormal_rankDivergence h hh]
    change (∑ i, familyPolynomialEmbedding h (coordinateDivergencePolynomial i (pderiv i p))) = _
    rw [← map_sum]
    change familyPolynomialEmbedding h (divergencePolynomial (gradientPolynomial p)) = _
    rw [tensor_number_polynomial, map_smul]
    rfl
  rw [he, ← cylinder_gradient_expansion] at hg
  exact LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence hg

theorem projection_of_sector {n m : ℕ} (f : sector m) :
    projection n f = if n = m then f.val else 0 := by
  classical
  by_cases hnm : n = m
  · subst n
    simp only [↓reduceIte, projection_fix]
  · rw [if_neg hnm]
    have hz : (sector n).orthogonalProjectionOnto f.val = 0 := by
      apply ext_inner_right ℝ
      intro g
      rw [inner_zero_left, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
      exact sectors_orthogonal (Ne.symm hnm) f g
    change ((sector n).orthogonalProjectionOnto f.val : GaussianL2) = 0
    rw [hz]
    rfl

theorem projection_orthonormal_polynomial (n : ℕ) (h : ι → CoefficientSpace)
    (hh : Orthonormal ℝ h) (p : MvPolynomial ι ℝ) :
    ∃ q : MvPolynomial ι ℝ, projection n (isonormalCylinderL2 h p) = isonormalCylinderL2 h q := by
  classical
  let L := familyPolynomialEmbedding h
  have hs : Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := ι))) ≤
      L.range.comap ((projection n).toLinearMap.comp L) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    change projection n (isonormalCylinderL2 h (tensorHermitePolynomial α)) ∈ L.range
    rw [projection_of_sector ⟨_, orthonormal_tensor_mem_sector h hh α⟩]
    split_ifs
    · exact ⟨tensorHermitePolynomial α, rfl⟩
    · exact L.range.zero_mem
  rw [tensorHermitePolynomial_span] at hs
  obtain ⟨q, hq⟩ := hs (Submodule.mem_top (x := p))
  exact ⟨q, hq.symm⟩

/-- Projection preserves the SAME finite observation algebra, including
correlated, repeated, and zero directions. Orthonormal coordinates are used
internally and are eliminated by proved polynomial substitutions. -/
theorem projection_polynomial (n : ℕ) (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    ∃ q : MvPolynomial ι ℝ, projection n (isonormalCylinderL2 h p) = isonormalCylinderL2 h q := by
  classical
  let S := Submodule.span ℝ (Set.range h)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range h)
  let b := stdOrthonormalBasis ℝ S
  let v : Fin (Module.finrank ℝ S) → CoefficientSpace := fun j => (b j : CoefficientSpace)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  let h' : ι → S := fun i => ⟨h i, Submodule.subset_span (Set.mem_range_self i)⟩
  let a : ι → Fin (Module.finrank ℝ S) → ℝ := fun i j => inner ℝ (b j) (h' i)
  have ha : (fun i => ∑ j, a i j • v j) = h := by
    funext i
    have he := congrArg (fun x : S => (x : CoefficientSpace)) (b.sum_repr' (h' i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using he
  have hp := isonormalCylinderL2_linear_substitution v a p
  rw [ha] at hp
  obtain ⟨q, hq⟩ := projection_orthonormal_polynomial n v hv
    (bind₁ (fun i => ∑ j, C (a i j) * X j) p)
  have hb (j : Fin (Module.finrank ℝ S)) : ∃ c : ι → ℝ, ∑ i, c i • h i = v j :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (b j).property
  choose c hc using hb
  refine ⟨bind₁ (fun j => ∑ i, C (c j i) * X i) q, ?_⟩
  rw [hp, hq]
  have hout := isonormalCylinderL2_linear_substitution h c q
  rwa [show (fun j => ∑ i, c j i • h i) = v from funext hc] at hout

theorem projection_pastPolynomial_measurable (n : ℕ) {m : ℕ} (s : ℝ≥0)
    (r : Fin m → ℝ≥0) (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin m) ℝ) :
    AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration s]
      (projection n (GaussianTimeDivergence.pastCoefficient r p)) gaussianProduct := by
  obtain ⟨q, hq⟩ := projection_polynomial n
    (fun i => SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector (r i))) p
  change projection n (GaussianTimeDivergence.pastCoefficient r p) =
    (GaussianTimeDivergence.pastCoefficient r q : GaussianL2) at hq
  rw [hq]
  exact GaussianPastStepCompletion.past_polynomial_measurable s r hrs q

theorem projection_preserves_past (n : ℕ) (s : ℝ≥0) (f : GaussianL2)
    (hf : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration s] f gaussianProduct) :
    AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration s] (projection n f)
      gaussianProduct := by
  have hc : IsClosed {g : GaussianL2 | AEStronglyMeasurable[
      GaussianTimeProcess.naturalFiltration s] (projection n g) gaussianProduct} :=
    (isClosed_aestronglyMeasurable (GaussianTimeProcess.naturalFiltration.le s)).preimage
      (projection n).continuous
  apply (closure_minimal (Subset.refl _) hc)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨m, r, p, hrs, hp⟩ := GaussianTimePastDensity.exists_fin_pastPolynomial_approx s f hf ε hε
  exact ⟨GaussianTimeDivergence.pastCoefficient r p,
    projection_pastPolynomial_measurable n s r hrs p, by simpa only [dist_eq_norm] using hp⟩

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
