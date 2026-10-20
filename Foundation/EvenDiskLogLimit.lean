import Foundation.EvenDiskLogRemainder

/-! Compact convergence of normalized disk logarithmic remainders.
All bounds are hypotheses on the actual remainders; none is inferred by
dividing an entire-function growth bound by an uncontrolled product. -/
noncomputable section
open Set Metric Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EvenDiskLogLimit
open EvenDiskLogRemainder

theorem eventually_uniform_compact_bound (g : ℝ → ℂ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+B*(R*Real.sqrt R))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ ρ →
      ‖g R z‖ ≤ (2*(A+B+1)*ρ^2)/Real.sqrt R := by
  filter_upwards [hdata,eventually_ge_atTop (max 1 (ρ+1))] with R hd hR
  obtain ⟨hg,h0,hd0,hreal⟩ := hd
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := by linarith
  have hRρ : ρ < R := by linarith [(le_max_right 1 (ρ+1)).trans hR]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRp
  have hs1 : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) hRp.le).mpr (by nlinarith)
  have hr1 : 1 ≤ R*Real.sqrt R := by nlinarith
  let M : ℝ := A+B*(R*Real.sqrt R)+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMc : M ≤ (A+B+1)*(R*Real.sqrt R) := by
    dsimp [M]
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hr1)]
  intro z hz
  have hb := quadratic_real_part_bound (g R) R M hRp hM hg h0 hd0
    (fun w hw => (hreal w hw).trans (by dsimp [M]; linarith)) z (hz.trans_lt hRρ)
  calc
    _ ≤ 2*M*(‖z‖/R)^2 := hb
    _ ≤ 2*((A+B+1)*(R*Real.sqrt R))*(ρ/R)^2 := by gcongr
    _ = (2*(A+B+1)*ρ^2)/Real.sqrt R := by
      apply (eq_div_iff (ne_of_gt hs)).mpr
      field_simp
      nlinarith [Real.sq_sqrt hRp.le]

theorem uniform_zero_on_closedBall (g : ℝ → ℂ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+B*(R*Real.sqrt R))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    TendstoUniformlyOn g (fun _ => 0) atTop (closedBall 0 ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun R : ℝ => (2*(A+B+1)*ρ^2)/Real.sqrt R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  filter_upwards [eventually_uniform_compact_bound g A B hA hB hdata ρ hρ,
    hlim.eventually (Iio_mem_nhds hε)] with R hb hsmall
  intro z hz
  simpa only [dist_zero_left] using (hb z (mem_closedBall_zero_iff.mp hz)).trans_lt hsmall

theorem locally_uniform_zero (g : ℝ → ℂ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+B*(R*Real.sqrt R)) :
    TendstoLocallyUniformly g (fun _ => 0) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  exact (uniform_zero_on_closedBall g A B hA hB hdata ρ hρ.le).mono hsub

theorem locally_uniform_exp_one (g : ℝ → ℂ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdata : ∀ᶠ R : ℝ in atTop,
      DifferentiableOn ℂ (g R) (ball 0 (2*R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+B*(R*Real.sqrt R)) :
    TendstoLocallyUniformly (fun R z => Complex.exp (g R z)) (fun _ => 1) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨ρ,hρ,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  apply TendstoUniformlyOn.mono (s := closedBall 0 ρ) ?_ hsub
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp
    (uniform_zero_on_closedBall g A B hA hB hdata ρ hρ.le))
      (min 1 (ε/2)) (by positivity)
  filter_upwards [hsmall] with R hb
  intro z hz
  have hn : ‖g R z‖ < min 1 (ε/2) := by simpa only [dist_zero_left] using hb z hz
  have he := Complex.norm_exp_sub_one_le (le_of_lt (hn.trans_le (min_le_left _ _)))
  have hh : ‖Complex.exp (g R z)-1‖ < ε := by
    linarith [hn.trans_le (min_le_right 1 (ε/2))]
  simpa only [dist_eq_norm,norm_sub_rev] using hh

end OperatorDerivativeRewrite.Foundation.EvenDiskLogLimit
