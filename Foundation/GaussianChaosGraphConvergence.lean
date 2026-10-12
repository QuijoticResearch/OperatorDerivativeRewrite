import Foundation.GaussianChaosDecomposition

/-! Actual Gaussian derivative graph convergence of the same finite-chaos
truncations. Summability is derived by adjoint duality, not assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian

def projectedGradient (n : ℕ) : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  (gradient n).comp (sector n).orthogonalProjectionOnto

theorem projectedGradient_graph (n : ℕ) (f : GaussianL2) :
    (projection n f, projectedGradient n f) ∈ sectorGraph n := gradient_graph n _

theorem projectedGradient_energy (n : ℕ) (f : GaussianL2) :
    ‖projectedGradient n f‖ ^ 2 = (n : ℝ) * ‖projection n f‖ ^ 2 :=
  sectorGraph_energy n ⟨_, projectedGradient_graph n f⟩

theorem gradient_ranges_orthogonal :
    OrthogonalFamily ℝ (fun n => (gradient n).range)
      (fun n => (gradient n).range.subtypeₗᵢ) := by
  intro n m hnm u v
  obtain ⟨f, hf⟩ := u.property
  obtain ⟨g, hg⟩ := v.property
  change inner ℝ u.val v.val = 0
  rw [← hf, ← hg]
  change inner ℝ (gradient n f) (gradient m g) = 0
  have h := graph_duality (gradient_graph n f).1 (gradient_graph m g).2
  change inner ℝ (gradient n f) (gradient m g) = inner ℝ f.val ((m : ℝ) • g.val) at h
  rw [h, inner_smul_right, sectors_orthogonal hnm f g, mul_zero]

def gradientComponent (f : GaussianL2) (n : ℕ) : (gradient n).range :=
  ⟨projectedGradient n f, ⟨(sector n).orthogonalProjectionOnto f, rfl⟩⟩

theorem projectedGradient_sum_energy (f : GaussianL2) (s : Finset ℕ) :
    ‖∑ n ∈ s, projectedGradient n f‖ ^ 2 = ∑ n ∈ s, ‖projectedGradient n f‖ ^ 2 :=
  gradient_ranges_orthogonal.norm_sum (gradientComponent f) s

theorem derivative_projectedGradient_pairing {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) (n : ℕ) :
    inner ℝ g (projectedGradient n f) = ‖projectedGradient n f‖ ^ 2 := by
  have h := graph_duality hf (projectedGradient_graph n f).2
  change inner ℝ g (projectedGradient n f) = inner ℝ f ((n : ℝ) • projection n f) at h
  rw [h, inner_smul_right, projectedGradient_energy]
  congr 1
  have hp := (sector n).inner_orthogonalProjectionOnto_eq_of_mem_right
    ((sector n).orthogonalProjectionOnto f) f
  change inner ℝ (projection n f) (projection n f) = inner ℝ f (projection n f) at hp
  rw [← hp, real_inner_self_eq_norm_sq]

theorem projectedGradient_finite_bound {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) (s : Finset ℕ) :
    ∑ n ∈ s, ‖projectedGradient n f‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  have hi : inner ℝ g (∑ n ∈ s, projectedGradient n f) =
      ∑ n ∈ s, ‖projectedGradient n f‖ ^ 2 := by
    simp only [inner_sum, derivative_projectedGradient_pairing hf]
  have hn := norm_sub_sq_real g (∑ n ∈ s, projectedGradient n f)
  rw [hi, projectedGradient_sum_energy] at hn
  nlinarith [sq_nonneg ‖g - ∑ n ∈ s, projectedGradient n f‖]

theorem projectedGradient_summable {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    Summable (fun n => projectedGradient n f) := by
  have hs : Summable (fun n => ‖gradientComponent f n‖ ^ 2) :=
    summable_of_sum_le (fun n => sq_nonneg _) (projectedGradient_finite_bound hf)
  exact (gradient_ranges_orthogonal.summable_iff_norm_sq_summable (gradientComponent f)).mpr hs

theorem finite_projection_graph (f : GaussianL2) (s : Finset ℕ) :
    (∑ n ∈ s, projection n f, ∑ n ∈ s, projectedGradient n f) ∈
      closedCylindricalDerivative.graph := by
  simpa only [prod_mk_sum] using closedCylindricalDerivative.graph.sum_mem
    (fun n (_ : n ∈ s) => (projectedGradient_graph n f).1)

theorem projectedGradient_hasSum {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    HasSum (fun n => projectedGradient n f) g := by
  have hs := (projectedGradient_summable hf).hasSum
  have hg := closedCylindricalDerivative_isClosed.mem_of_tendsto
    ((projection_hasSum f).prodMk_nhds hs)
    (Eventually.of_forall (finite_projection_graph f))
  have he := closedCylindricalDerivative.mem_graph_snd_inj hg hf rfl
  rwa [he] at hs

def gradientTruncation (N : ℕ) : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  ∑ n ∈ Finset.range (N + 1), projectedGradient n

theorem truncation_graph (N : ℕ) (f : GaussianL2) :
    (truncation N f, gradientTruncation N f) ∈ closedCylindricalDerivative.graph := by
  simpa only [truncation, gradientTruncation, ContinuousLinearMap.sum_apply] using
    finite_projection_graph f (Finset.range (N + 1))

theorem simultaneous_graph_tendsto {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    Tendsto (fun N => (truncation N f, gradientTruncation N f)) atTop (𝓝 (f, g)) := by
  have hd := (projectedGradient_hasSum hf).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply (truncation_tendsto f).prodMk_nhds
  simpa only [gradientTruncation, ContinuousLinearMap.sum_apply, Function.comp_def] using hd

/-- Exact full derivative-domain characterization; no conditional domain or
graph-density assumption occurs on the summability side. -/
theorem derivative_domain_iff_weighted_chaos (f : GaussianL2) :
    f ∈ closedCylindricalDerivative.domain ↔
      Summable (fun n : ℕ => (n : ℝ) * ‖projection n f‖ ^ 2) := by
  constructor
  · intro hf
    have hs := (gradient_ranges_orthogonal.summable_iff_norm_sq_summable
      (gradientComponent f)).mp
      (projectedGradient_summable (closedCylindricalDerivative.mem_graph ⟨f, hf⟩))
    change Summable (fun n => ‖projectedGradient n f‖ ^ 2) at hs
    simpa only [projectedGradient_energy] using hs
  · intro hs
    have hn : Summable (fun n => ‖gradientComponent f n‖ ^ 2) := by
      change Summable (fun n => ‖projectedGradient n f‖ ^ 2)
      simpa only [projectedGradient_energy] using hs
    have hd := ((gradient_ranges_orthogonal.summable_iff_norm_sq_summable
      (gradientComponent f)).mpr hn).hasSum
    exact LinearPMap.mem_domain_iff.mpr ⟨_, closedCylindricalDerivative_isClosed.mem_of_tendsto
      ((projection_hasSum f).prodMk_nhds hd) (Eventually.of_forall (finite_projection_graph f))⟩

theorem derivative_energy_hasSum {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    HasSum (fun n : ℕ => (n : ℝ) * ‖projection n f‖ ^ 2) (‖g‖ ^ 2) := by
  have h := (projectedGradient_hasSum hf).norm.pow 2
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, (n : ℝ) * ‖projection n f‖ ^ 2)
    atTop (𝓝 (‖g‖ ^ 2))
  convert h using 1
  · ext s
    rw [projectedGradient_sum_energy]
    simp only [projectedGradient_energy]
  · rfl

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
