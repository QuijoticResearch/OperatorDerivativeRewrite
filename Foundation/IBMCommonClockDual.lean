import Foundation.GaussianClockSourceSpectral
import Foundation.IBMRegularizedTimeLimit

/-! A genuine dual norm for the full SOURCE/CLOCK correction: the test
image is the common smoothing with its unique preimage norm. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCommonClockDual
open InfiniteGaussian GaussianNumberSectors GaussianClockValueOperators
open GaussianClockSourceSpectral GaussianObservedSecondRegularization
open IBMRegularizedStochasticIdentity
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem scalar_smoothing_pairing (f g : GaussianL2) :
    inner ℝ (commonSmoothing f) g = inner ℝ f (commonSmoothing g) := by
  change inner ℝ (projection 0 f + GaussianInverseNumberPotential.potentialOperator f) g =
    inner ℝ f (projection 0 g + GaussianInverseNumberPotential.potentialOperator g)
  rw [inner_add_left,inner_add_right,GaussianItoChaosIntertwining.projection_pairing,
    GaussianPotentialPredictionRank.potential_inner]

theorem sourceLift_pairing (B : GaussianL2 →L[ℝ] GaussianL2)
    (hB : ∀ f g, inner ℝ (B f) g = inner ℝ f (B g)) (f g : Field) :
    inner ℝ (sourceLift B f) g = inner ℝ f (sourceLift B g) := by
  rw [L2_inner_eq_integral,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [B.coeFn_compLpL f,B.coeFn_compLpL g] with ω hf hg
  change sourceLift B f ω = B (f ω) at hf
  change sourceLift B g ω = B (g ω) at hg
  rw [hf,hg,hB]

theorem flip_pairing (f g : Field) :
    inner ℝ (ProductL2Curry.flip gaussianProduct gaussianProduct f) g =
      inner ℝ f (ProductL2Curry.flip gaussianProduct gaussianProduct g) := by
  have hh := (ProductL2Curry.flip gaussianProduct gaussianProduct).inner_map_map f
    (ProductL2Curry.flip gaussianProduct gaussianProduct g)
  rwa [flip_involutive] at hh

theorem smoothing_pairing (f g : Field) : inner ℝ (smoothing f) g = inner ℝ f (smoothing g) := by
  let F := ProductL2Curry.flip gaussianProduct gaussianProduct
  change inner ℝ (F (sourceLift commonSmoothing (F f))) g =
    inner ℝ f (F (sourceLift commonSmoothing (F g)))
  rw [flip_pairing,sourceLift_pairing commonSmoothing scalar_smoothing_pairing,flip_pairing]

/-- The regular test image is dense in the ORIGINAL full joint L2 space. -/
theorem smoothing_denseRange : DenseRange smoothing := by
  let R := smoothing.toLinearMap.range.topologicalClosure
  have hR : IsClosed (R : Set Field) := smoothing.toLinearMap.range.isClosed_topologicalClosure
  letI : CompleteSpace R := hR.completeSpace_coe
  have ho : Rᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    have hi (g : Field) : inner ℝ g (smoothing f) = 0 := by
      rw [← smoothing_pairing]
      exact (Submodule.mem_orthogonal R f).mp hf _
        (smoothing.toLinearMap.range.le_topologicalClosure ⟨g,rfl⟩)
    have hz : smoothing f = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (hi (smoothing f))
    exact smoothing_injective (hz.trans (map_zero smoothing).symm)
  have ht : R = ⊤ := Submodule.orthogonal_eq_bot_iff.mp ho
  intro f
  change f ∈ R
  rw [ht]
  trivial

def dualNorm (f : Field) : ℝ := ‖smoothing f‖

theorem dualNorm_nonneg (f : Field) : 0 ≤ dualNorm f := norm_nonneg _

theorem dualNorm_eq_zero_iff (f : Field) : dualNorm f = 0 ↔ f = 0 := by
  rw [dualNorm,norm_eq_zero]
  constructor
  · intro hf
    exact smoothing_injective (hf.trans (map_zero smoothing).symm)
  · rintro rfl
    exact map_zero _

theorem dualNorm_add_le (f g : Field) : dualNorm (f+g) ≤ dualNorm f + dualNorm g := by
  simpa only [dualNorm,map_add] using norm_add_le (smoothing f) (smoothing g)

theorem dualNorm_smul (a : ℝ) (f : Field) : dualNorm (a • f) = |a| * dualNorm f := by
  simp only [dualNorm,map_smul,norm_smul,Real.norm_eq_abs]

/-- The test is the ACTUAL smoothed field K psi, rather than psi itself. -/
theorem dual_bound (f ψ : Field) : |inner ℝ f (smoothing ψ)| ≤ dualNorm f * ‖ψ‖ := by
  rw [← smoothing_pairing]
  simpa only [Real.norm_eq_abs,dualNorm] using norm_inner_le_norm (𝕜 := ℝ) (smoothing f) ψ

/-- Attainment identifies the proposed norm with the true operator norm on
the test image equipped with its unique preimage norm. -/
theorem dual_attainment (f : Field) :
    ∃ ψ : Field, ‖ψ‖ ≤ 1 ∧ inner ℝ f (smoothing ψ) = dualNorm f := by
  by_cases hf : smoothing f = 0
  · refine ⟨0,by simp,?_⟩
    simp [dualNorm,hf]
  · have hn : 0 < ‖smoothing f‖ := norm_pos_iff.mpr hf
    refine ⟨‖smoothing f‖⁻¹ • smoothing f,?_,?_⟩
    · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
    · rw [← smoothing_pairing,real_inner_smul_right,real_inner_self_eq_norm_sq]
      change ‖smoothing f‖⁻¹ * ‖smoothing f‖ ^ 2 = ‖smoothing f‖
      field_simp

theorem dualNorm_le_iff (f : Field) {C : ℝ} (hC : 0 ≤ C) :
    dualNorm f ≤ C ↔ ∀ ψ : Field, |inner ℝ f (smoothing ψ)| ≤ C * ‖ψ‖ := by
  constructor
  · intro hf ψ
    exact (dual_bound f ψ).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg ψ))
  · intro h
    obtain ⟨ψ,hψ,he⟩ := dual_attainment f
    calc
      dualNorm f = inner ℝ f (smoothing ψ) := he.symm
      _ ≤ |inner ℝ f (smoothing ψ)| := le_abs_self _
      _ ≤ C * ‖ψ‖ := h ψ
      _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hψ hC

theorem correction_dual_uniform {g : SchwartzMap ℝ ℝ} {a : ℝ} {T : ℝ≥0} {c : Field}
    (hc : Tendsto (fun n => correction g a n T) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ ψ : Field, ‖ψ‖ ≤ 1 →
      |inner ℝ (IBMSchwartzBochnerDomain.wholeClass g a n T) (smoothing ψ) - inner ℝ c ψ| < ε := by
  obtain ⟨n0,hn⟩ := Metric.tendsto_atTop.mp hc ε hε
  refine ⟨n0,fun n hnn ψ hψ => ?_⟩
  have he : inner ℝ (IBMSchwartzBochnerDomain.wholeClass g a n T) (smoothing ψ) - inner ℝ c ψ =
      inner ℝ (correction g a n T - c) ψ := by
    rw [← smoothing_pairing,inner_sub_left]
    rfl
  rw [he]
  have hb : |inner ℝ (correction g a n T - c) ψ| ≤ ‖correction g a n T - c‖ := by
    have h0 : |inner ℝ (correction g a n T - c) ψ| ≤ ‖correction g a n T - c‖ * ‖ψ‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (correction g a n T - c) ψ
    exact h0.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hψ (norm_nonneg _))
  exact hb.trans_lt (by simpa only [dist_eq_norm] using hn n hnn)

end OperatorDerivativeRewrite.Foundation.IBMCommonClockDual
