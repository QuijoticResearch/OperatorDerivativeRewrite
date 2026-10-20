import Foundation.RiemannQuarticCanonicalBounds

/-! Actual normalized zero-free canonical remainders converge locally
uniformly to one. The remaining zero-product and polynomial approximation
are not included in this theorem. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalLimit
open RiemannQuarticFlow RiemannQuarticCanonicalDerivative RiemannQuarticCanonicalBounds

theorem exists_actual_locally_uniform_remainders (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ r : ℝ → ℝ, ∃ h g : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        divisor (flow t) (sphere 0 (r R)) = 0 ∧
        ECanonicalDecomp (flow t) (h R) (r R) ∧
        DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
        (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R)) ∧
      TendstoLocallyUniformly g (fun _ => 0) atTop ∧
      TendstoLocallyUniformly (fun R z => Complex.exp (g R z)) (fun _ => 1) atTop ∧
      TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
  classical
  obtain ⟨A,hA,hreal⟩ := exists_normalized_remainder_real_part_bound t
  have hex (R : ℝ) := exists_actual_zero_derivative_log_remainder t (2*max R 1)
    (by positivity : 0 ≤ 2*max R 1)
  choose r hr hr1 hboundary h g D hg h0 hd0 hd he using hex
  have hspec (R : ℝ) (hR : 1 ≤ R) : 2*R < r R ∧ r R < 2*R+1 ∧
      divisor (flow t) (sphere 0 (r R)) = 0 ∧
      ECanonicalDecomp (flow t) (h R) (r R) ∧
      DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
      (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
      ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R) := by
    have hrl : 2*R < r R := by simpa only [max_eq_left hR] using hr R
    have hru : r R < 2*R+1 := by simpa only [max_eq_left hR] using hr1 R
    exact ⟨hrl,hru,hboundary R,D R,hg R,h0 R,hd0 R,hd R,he R,
      hreal R hR (r R) hrl hru (h R) (g R) (D R) (hboundary R) (he R)⟩
  have hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    obtain ⟨hrl,hru,hbd,hD,hgR,hg0,hgd,hder,hexp,hre⟩ := hspec R hR
    exact ⟨hgR.mono (ball_subset_ball hrl.le),hg0,hgd,hre⟩
  have hlog := EvenDiskLogLimit.locally_uniform_zero g A 6 hA (by norm_num) hdata
  have hexp := EvenDiskLogLimit.locally_uniform_exp_one g A 6 hA (by norm_num) hdata
  have hquot : TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    apply (tendstoLocallyUniformly_iff_forall_isCompact.mp hexp K hK).congr
    filter_upwards [eventually_ge_atTop (max 1 (ρ+1))] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hrl : 2*R < r R := (hspec R hR1).1
    intro z hz
    apply he R z
    apply mem_ball_zero_iff.mpr
    have hzρ : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp (hsub hz)
    linarith [(le_max_right 1 (ρ+1)).trans hR]
  exact ⟨A,hA,r,h,g,hspec,hlog,hexp,hquot⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalLimit
