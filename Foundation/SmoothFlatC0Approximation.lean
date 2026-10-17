import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! Uniform C0 approximation by actual smooth compact functions that are
constant near zero. This is a function approximation, not graph approximation. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.SmoothFlatC0Approximation
set_option backward.isDefEq.respectTransparency false

theorem exists_smooth_compact_approx (F : C₀(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ x, |g x-F x| ≤ ε := by
  have he : 0 < ε/4 := by positivity
  obtain ⟨g,hg,herr⟩ := (ZeroAtInftyContinuousMap.uniformContinuous F).exists_contDiff_dist_le he
  have ht : ∀ᶠ x in cocompact ℝ, ‖F x‖ < ε/4 := by
    have hh : Tendsto (fun x => ‖F x‖) (cocompact ℝ) (𝓝 0) := by
      simpa only [norm_zero] using (zero_at_infty F).norm
    exact hh.eventually (eventually_lt_nhds he)
  obtain ⟨K,hK,hout⟩ := mem_cocompact.mp ht
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  let B : ContDiffBump (0 : ℝ) := ⟨R,R+1,hR,lt_add_one R⟩
  refine ⟨fun x => B x*g x,B.contDiff.mul hg,B.hasCompactSupport.mul_right,?_⟩
  intro x
  have hB0 : 0 ≤ B x := B.nonneg
  have hB1 : B x ≤ 1 := B.le_one
  have hfirst : |B x*(g x-F x)| ≤ ε/4 := by
    rw [abs_mul,abs_of_nonneg hB0]
    have hh : |g x-F x| < ε/4 := by simpa only [Real.dist_eq] using herr x
    exact (mul_le_of_le_one_left (abs_nonneg _) hB1).trans hh.le
  have hsecond : |(B x-1)*F x| ≤ ε/4 := by
    by_cases hx : x ∈ K
    · have hb : B x = 1 := B.one_of_mem_closedBall (hKR hx)
      simp only [hb,sub_self,zero_mul,abs_zero]
      exact he.le
    · have hh : |F x| < ε/4 := by
        simpa only [Real.norm_eq_abs,mem_ofPred_eq] using hout hx
      rw [abs_mul]
      have hb : |B x-1| ≤ 1 := by rw [abs_of_nonpos (by linarith)]; linarith
      exact (mul_le_of_le_one_left (abs_nonneg _) hb).trans hh.le
  calc
    |B x*g x-F x| = |B x*(g x-F x)+(B x-1)*F x| := by congr 1; ring
    _ ≤ |B x*(g x-F x)|+|(B x-1)*F x| := abs_add_le _ _
    _ ≤ ε := by linarith

theorem exists_flat_smooth_compact_approx (F : C₀(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝 (0 : ℝ)] (fun _ => F 0) ∧ ∀ x, |g x-F x| ≤ ε := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨g,hg,hgc,herr⟩ := exists_smooth_compact_approx F he
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt (F : ℝ → ℝ) 0 from F.continuous.continuousAt) (ε/2) he
  let B : ContDiffBump (0 : ℝ) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  let f : ℝ → ℝ := fun x => B x*F 0+(1-B x)*g x
  have hfc : HasCompactSupport f := by
    exact B.hasCompactSupport.mul_right.add hgc.mul_left
  refine ⟨f,(B.contDiff.mul contDiff_const).add
    ((contDiff_const.sub B.contDiff).mul hg),hfc,?_,?_⟩
  · filter_upwards [B.eventuallyEq_one] with x hx
    simp only [f,hx,Pi.one_apply,one_mul,sub_self,zero_mul,add_zero]
  · intro x
    have hB0 : 0 ≤ B x := B.nonneg
    have hB1 : B x ≤ 1 := B.le_one
    have hfirst : |B x*(F 0-F x)| ≤ ε/2 := by
      by_cases hz : B x = 0
      · simpa only [hz,zero_mul,abs_zero] using he.le
      · have hx : x ∈ Metric.ball (0 : ℝ) δ := by
          rw [← B.support_eq]
          exact hz
        have hh : |F 0-F x| < ε/2 := by
          simpa only [Real.dist_eq,abs_sub_comm] using hclose (Metric.mem_ball.mp hx)
        rw [abs_mul,abs_of_nonneg hB0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hB1).trans hh.le
    have hsecond : |(1-B x)*(g x-F x)| ≤ ε/2 := by
      rw [abs_mul,abs_of_nonneg (by linarith)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith)).trans (herr x)
    calc
      |f x-F x| = |B x*(F 0-F x)+(1-B x)*(g x-F x)| := by
        dsimp [f]
        congr 1
        ring
      _ ≤ |B x*(F 0-F x)|+|(1-B x)*(g x-F x)| := abs_add_le _ _
      _ ≤ ε := by linarith

def flatSmooth : Set C₀(ℝ, ℝ) :=
  {F | ContDiff ℝ ∞ (F : ℝ → ℝ) ∧ HasCompactSupport (F : ℝ → ℝ) ∧
    ∃ c : ℝ, (F : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] (fun _ => c)}

theorem exists_flat_C0_approx (F : C₀(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G ∈ flatSmooth, ‖G-F‖ ≤ ε := by
  obtain ⟨g,hg,hgc,hflat,herr⟩ := exists_flat_smooth_compact_approx F hε
  let G : C₀(ℝ, ℝ) := {
    toFun := g
    continuous_toFun := hg.continuous
    zero_at_infty' := hgc.is_zero_at_infty }
  refine ⟨G,⟨hg,hgc,⟨F 0,hflat⟩⟩,?_⟩
  change ‖(G-F).toBCF‖ ≤ ε
  apply (BoundedContinuousFunction.norm_le hε.le).mpr
  intro x
  change ‖g x-F x‖ ≤ ε
  simpa only [Real.norm_eq_abs] using herr x

theorem flatSmooth_dense : Dense flatSmooth := by
  rw [Metric.dense_iff]
  intro F ε hε
  obtain ⟨G,hG,herr⟩ := exists_flat_C0_approx F (half_pos hε)
  refine ⟨G,?_,hG⟩
  rw [Metric.mem_ball,dist_eq_norm]
  exact herr.trans_lt (half_lt_self hε)

end OperatorDerivativeRewrite.Foundation.SmoothFlatC0Approximation
