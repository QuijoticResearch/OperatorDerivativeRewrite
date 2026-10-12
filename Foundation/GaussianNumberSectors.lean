import Foundation.InfiniteGaussianKernel

/-! Spectral sectors of the ACTUAL Gaussian number operator D*D. Neither
completeness nor past preservation is assumed in this construction. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian

def swapScale (n : ℕ) : (GaussianL2 × GaussianVectorL2) →L[ℝ]
    (GaussianVectorL2 × GaussianL2) :=
  (ContinuousLinearMap.snd ℝ _ _).prod ((n : ℝ) • ContinuousLinearMap.fst ℝ _ _)

def sectorGraph (n : ℕ) : Submodule ℝ (GaussianL2 × GaussianVectorL2) :=
  closedCylindricalDerivative.graph ⊓ hilbertDivergence.graph.comap (swapScale n).toLinearMap

theorem mem_sectorGraph (n : ℕ) (f : GaussianL2) (g : GaussianVectorL2) :
    (f, g) ∈ sectorGraph n ↔ (f, g) ∈ closedCylindricalDerivative.graph ∧
      (g, (n : ℝ) • f) ∈ hilbertDivergence.graph := Iff.rfl

theorem sectorGraph_isClosed (n : ℕ) :
    IsClosed (sectorGraph n : Set (GaussianL2 × GaussianVectorL2)) :=
  closedCylindricalDerivative_isClosed.inter
    (hilbertDivergence_isClosed.preimage (swapScale n).continuous)

instance sectorGraph_complete (n : ℕ) : CompleteSpace (sectorGraph n) :=
  (sectorGraph_isClosed n).completeSpace_coe

theorem graph_duality {f v : GaussianL2} {g u : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph)
    (hu : (u, v) ∈ hilbertDivergence.graph) : inner ℝ g u = inner ℝ f v := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint closedCylindricalDerivative_dense_domain] at hu
  exact sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hu f g hf)

theorem sectorGraph_energy (n : ℕ) (z : sectorGraph n) :
    ‖z.val.2‖ ^ 2 = (n : ℝ) * ‖z.val.1‖ ^ 2 := by
  have h := graph_duality z.property.1 z.property.2
  change inner ℝ z.val.2 z.val.2 = inner ℝ z.val.1 ((n : ℝ) • z.val.1) at h
  simpa only [real_inner_self_eq_norm_sq, inner_smul_right] using h

theorem sectorGraph_gradient_norm (n : ℕ) (z : sectorGraph n) :
    ‖z.val.2‖ = Real.sqrt n * ‖z.val.1‖ := by
  have h := sectorGraph_energy n z
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  nlinarith [norm_nonneg z.val.2, norm_nonneg z.val.1, Real.sqrt_nonneg (n : ℝ),
    mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (norm_nonneg z.val.1)]

def sectorFst (n : ℕ) : sectorGraph n →L[ℝ] GaussianL2 :=
  (ContinuousLinearMap.fst ℝ _ _).comp (sectorGraph n).subtypeL

def sector (n : ℕ) : Submodule ℝ GaussianL2 := (sectorFst n).toLinearMap.range

theorem mem_sector (n : ℕ) (f : GaussianL2) :
    f ∈ sector n ↔ ∃ g, (f, g) ∈ closedCylindricalDerivative.graph ∧
      (g, (n : ℝ) • f) ∈ hilbertDivergence.graph := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.val.2, z.property⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨(f, g), hg⟩, rfl⟩

theorem sector_isClosed (n : ℕ) : IsClosed (sector n : Set GaussianL2) := by
  have hb : ∀ z : sectorGraph n,
      ‖z‖ ≤ (⟨1 + Real.sqrt n, by positivity⟩ : ℝ≥0) * ‖sectorFst n z‖ := by
    intro z
    change max ‖z.val.1‖ ‖z.val.2‖ ≤ (1 + Real.sqrt n) * ‖z.val.1‖
    rw [sectorGraph_gradient_norm]
    apply max_le
    · nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (norm_nonneg z.val.1)]
    · nlinarith [norm_nonneg z.val.1]
  exact ((sectorFst n).antilipschitz_of_bound hb).isClosed_range (sectorFst n).uniformContinuous

instance sector_complete (n : ℕ) : CompleteSpace (sector n) :=
  (sector_isClosed n).completeSpace_coe

theorem sector_mem_domain (n : ℕ) (f : sector n) :
    f.val ∈ closedCylindricalDerivative.domain := by
  obtain ⟨g, hg, _⟩ := (mem_sector n f).mp f.property
  exact LinearPMap.mem_domain_iff.mpr ⟨g, hg⟩

def sectorDomain (n : ℕ) : sector n →ₗ[ℝ] closedCylindricalDerivative.domain where
  toFun f := ⟨f.val, sector_mem_domain n f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sector_derivative_graph (n : ℕ) (f : sector n) :
    (f.val, closedCylindricalDerivative (sectorDomain n f)) ∈ sectorGraph n := by
  obtain ⟨g, hg, hd⟩ := (mem_sector n f).mp f.property
  have he := closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (sectorDomain n f)) hg rfl
  apply (mem_sectorGraph n _ _).mpr
  exact ⟨closedCylindricalDerivative.mem_graph (sectorDomain n f), he.symm ▸ hd⟩

def gradient (n : ℕ) : sector n →L[ℝ] GaussianVectorL2 :=
  (closedCylindricalDerivative.toFun.comp (sectorDomain n)).mkContinuous (Real.sqrt n)
    (fun f => (sectorGraph_gradient_norm n
      ⟨(f.val, closedCylindricalDerivative (sectorDomain n f)), sector_derivative_graph n f⟩).le)

theorem gradient_graph (n : ℕ) (f : sector n) :
    (f.val, gradient n f) ∈ sectorGraph n := sector_derivative_graph n f

theorem gradient_norm (n : ℕ) (f : sector n) :
    ‖gradient n f‖ = Real.sqrt n * ‖f‖ :=
  sectorGraph_gradient_norm n ⟨_, gradient_graph n f⟩

def projection (n : ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  (sector n).subtypeL.comp (sector n).orthogonalProjectionOnto

theorem projection_mem (n : ℕ) (f : GaussianL2) : projection n f ∈ sector n :=
  ((sector n).orthogonalProjectionOnto f).property

theorem projection_fix (n : ℕ) (f : sector n) : projection n f = f := by
  change ((sector n).orthogonalProjectionOnto f : GaussianL2) = f
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem projection_idempotent (n : ℕ) (f : GaussianL2) :
    projection n (projection n f) = projection n f :=
  projection_fix n ⟨_, projection_mem n f⟩

theorem projection_norm_le (n : ℕ) (f : GaussianL2) : ‖projection n f‖ ≤ ‖f‖ :=
  (sector n).norm_orthogonalProjectionOnto_apply_le f

theorem projection_derivative_graph (n : ℕ) (f : GaussianL2) :
    (projection n f, gradient n ((sector n).orthogonalProjectionOnto f)) ∈
      closedCylindricalDerivative.graph := (gradient_graph n _).1

theorem sectors_orthogonal {n m : ℕ} (hnm : n ≠ m) (f : sector n) (g : sector m) :
    inner ℝ f.val g.val = 0 := by
  have h := graph_duality (gradient_graph n f).1 (gradient_graph m g).2
  have k := graph_duality (gradient_graph m g).1 (gradient_graph n f).2
  change inner ℝ (gradient n f) (gradient m g) = inner ℝ f.val ((m : ℝ) • g.val) at h
  change inner ℝ (gradient m g) (gradient n f) = inner ℝ g.val ((n : ℝ) • f.val) at k
  rw [inner_smul_right] at h k
  rw [real_inner_comm (gradient n f) (gradient m g), real_inner_comm f.val g.val] at k
  have hnm' : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
  exact (mul_eq_zero.mp (show ((n : ℝ) - m) * inner ℝ f.val g.val = 0 by nlinarith)).resolve_left
    (sub_ne_zero.mpr hnm')

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
