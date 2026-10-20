import Foundation.EvenEntireZeroFreeRigidity
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Bounded

/-! Normalized analytic logarithms and quadratic disk estimates for the
zero-free remainder in a finite-disk factorization. These estimates do not
assert that a factorization or its growth hypotheses have been constructed. -/
noncomputable section
open Set Metric Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EvenDiskLogRemainder

theorem exists_normalized_log_on_ball (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hne : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 R) ∧ g 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball (0 : ℂ) R, Complex.exp (g z) = f z / f 0 := by
  have hsc : IsSimplyConnected (ball (0 : ℂ) R) := by
    letI : ContractibleSpace (ball (0 : ℂ) R) :=
      (convex_ball (0 : ℂ) R).contractibleSpace (nonempty_ball.mpr hR)
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨h,hc,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball
    hf.continuousOn (by
      rintro ⟨z,hz,heq⟩
      exact hne z hz heq)
  have hd (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      HasDerivAt h (deriv f z / f z) z := by
    have hl : Complex.exp ∘ h =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact he hw
    have hh := HasDerivAt.of_comp_left (hc.continuousAt (isOpen_ball.mem_nhds hz))
      (Complex.hasDerivAt_exp (h z))
      (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      (Complex.exp_ne_zero _) hl
    have hez : Complex.exp (h z) = f z := he hz
    rw [hez] at hh
    exact hh
  refine ⟨fun z => h z - h 0,?_,sub_self _,?_,?_⟩
  · exact fun z hz => ((hd z hz).sub_const _).differentiableAt.differentiableWithinAt
  · exact fun z hz => (hd z hz).sub_const _
  · intro z hz
    rw [Complex.exp_sub,show Complex.exp (h z) = f z from he hz,
      show Complex.exp (h 0) = f 0 from he (mem_ball_self hR)]

theorem quadratic_real_part_bound (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball 0 (2*R))) (h0 : g 0 = 0)
    (hd0 : deriv g 0 = 0)
    (hreal : ∀ z ∈ ball (0 : ℂ) (2*R), (g z).re ≤ M)
    (z : ℂ) (hz : ‖z‖ < R) : ‖g z‖ ≤ 2*M*(‖z‖/R)^2 := by
  have hlittle : (fun w : ℂ => g w - g 0) =o[𝓝 0] (fun w => ‖w - 0‖^(1 : ℕ)) := by
    simpa only [hd0,smul_zero,sub_zero,pow_one] using
      ((hg.differentiableAt (isOpen_ball.mem_nhds
        (mem_ball_self (by positivity)))).hasDerivAt.isLittleO.norm_right)
  have hmaps : MapsTo g (ball 0 R) (closedBall (g 0) (2*M)) := by
    intro w hw
    have hwr := mem_ball_zero_iff.mp hw
    have hw2 : w ∈ ball (0 : ℂ) (2*R) := mem_ball_zero_iff.mpr (by linarith)
    have hb := Complex.borelCaratheodory_zero hM hg hreal (by positivity) hw2 h0
    rw [mem_closedBall,dist_eq_norm,h0,sub_zero]
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < 2*R-‖w‖)).mpr
    nlinarith
  have hsub : ball (0 : ℂ) R ⊆ ball 0 (2*R) := ball_subset_ball (by linarith)
  have hb := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (hg.mono hsub) hmaps hlittle (mem_ball_zero_iff.mpr hz)
  simpa only [h0,dist_zero_right] using hb

theorem exists_normalized_log_with_bound (f : ℂ → ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball 0 (2*R)))
    (hne : ∀ z ∈ ball (0 : ℂ) (2*R), f z ≠ 0) (hd0 : deriv f 0 = 0)
    (hbound : ∀ z ∈ ball (0 : ℂ) (2*R), ‖f z‖ ≤ ‖f 0‖*Real.exp M) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 (2*R)) ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) (2*R), Complex.exp (g z) = f z / f 0) ∧
      ∀ z : ℂ, ‖z‖ < R → ‖g z‖ ≤ 2*M*(‖z‖/R)^2 := by
  obtain ⟨g,hg,h0,hd,he⟩ := exists_normalized_log_on_ball f (2*R) (by positivity) hf hne
  have hdg : deriv g 0 = 0 := by
    rw [(hd 0 (mem_ball_self (by positivity))).deriv,hd0,zero_div]
  refine ⟨g,hg,h0,hdg,he,?_⟩
  have hn : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0 (mem_ball_self (by positivity)))
  have hreal (z : ℂ) (hz : z ∈ ball (0 : ℂ) (2*R)) : (g z).re ≤ M := by
    have he' := congrArg norm (he z hz)
    rw [Complex.norm_exp,norm_div] at he'
    apply Real.exp_le_exp.mp
    rw [he']
    exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hbound z hz)
  exact fun z hz => quadratic_real_part_bound g R M hR hM hg h0 hdg hreal z hz

end OperatorDerivativeRewrite.Foundation.EvenDiskLogRemainder
