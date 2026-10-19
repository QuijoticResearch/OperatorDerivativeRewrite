import Foundation.IBMMollifierProfileAudit
import Foundation.IBMWholeLineSmoothing
import Foundation.IBMContinuousMalliavin

/-! Actual continuous-width spatial convolutions. The index filter is arbitrary:
these limits are not inferred from the previously verified discrete sequence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedMollifier
open InfiniteGaussian IBMContinuousScenery
set_option backward.isDefEq.respectTransparency false

def dilate (ρ : ℝ → ℝ) (ε x : ℝ) : ℝ := ε⁻¹ * ρ (x / ε)

theorem dilate_nonneg {ρ : ℝ → ℝ} (hρ : ∀ x, 0 ≤ ρ x) {ε : ℝ} (hε : 0 < ε)
    (x : ℝ) : 0 ≤ dilate ρ ε x := mul_nonneg (inv_nonneg.mpr hε.le) (hρ _)

theorem dilate_even {ρ : ℝ → ℝ} (hρ : ∀ x, ρ (-x) = ρ x) (ε x : ℝ) :
    dilate ρ ε (-x) = dilate ρ ε x := by simp only [dilate,neg_div,hρ]

theorem dilate_contDiff {ρ : ℝ → ℝ} {k : WithTop ℕ∞} (hρ : ContDiff ℝ k ρ)
    (ε : ℝ) : ContDiff ℝ k (dilate ρ ε) :=
  contDiff_const.mul (hρ.comp (contDiff_id.div_const ε))

theorem dilate_compact {ρ : ℝ → ℝ} (hρ : HasCompactSupport ρ) {ε : ℝ}
    (hε : ε ≠ 0) : HasCompactSupport (dilate ρ ε) := by
  have h := hρ.comp_smul (inv_ne_zero hε)
  have h' := h.smul_left (f := fun _ : ℝ => ε⁻¹)
  have he : dilate ρ ε = (fun _ : ℝ => ε⁻¹) • (fun x : ℝ => ρ (ε⁻¹ • x)) := by
    funext x
    change ε⁻¹ * ρ (x / ε) = ε⁻¹ * ρ (ε⁻¹ * x)
    rw [div_eq_mul_inv,mul_comm x]
  rw [he]
  exact h'

theorem dilate_integral (ρ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, dilate ρ ε x) = ∫ x, ρ x := by
  simp only [dilate,integral_const_mul,div_eq_mul_inv]
  rw [Measure.integral_comp_mul_right]
  simp only [inv_inv,abs_of_pos hε,smul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ hε.ne',one_mul]

theorem dilate_support {ρ : ℝ → ℝ} {R ε : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (hε : 0 < ε) {z : ℝ}
    (hz : dilate ρ ε z ≠ 0) : |z| ≤ ε * R := by
  have hr : ρ (z / ε) ≠ 0 := by intro he; exact hz (by simp [dilate,he])
  have hb := hs _ hr
  rwa [abs_div,abs_of_pos hε,div_le_iff₀ hε,mul_comm R ε] at hb

theorem shifted_support {ρ : ℝ → ℝ} {R ε : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (hε : 0 < ε) (x r : ℝ)
    (hr : r ∉ Set.Icc (x - ε * R) (x + ε * R)) : dilate ρ ε (x-r) = 0 := by
  by_contra hz
  have hb := abs_le.mp (dilate_support hs hε hz)
  exact hr ⟨by linarith,by linarith⟩

theorem shifted_mass {ρ : ℝ → ℝ} {R ε : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (hε : 0 < ε) (x : ℝ)
    (hmass : (∫ z, ρ z) = 1) :
    (∫ r in Set.Icc (x - ε * R) (x + ε * R), dilate ρ ε (x-r)) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun r hr => shifted_support hs hε x r hr)]
  rw [integral_sub_left_eq_self _ volume x,dilate_integral ρ hε,hmass]

/-- Quantitative error of the ACTUAL Bochner convolution for every positive width. -/
theorem scenery_error {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1)
    {R ε : ℝ} (hR : 0 ≤ R) (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R)
    (hε : 0 < ε) (x : ℝ) :
    ‖wholeLineScenery (dilate ρ ε) x - sourceScenery x‖^2 ≤ ε * R := by
  apply wholeLineScenery_error_sq_le (x-ε*R) (x+ε*R) x (ε*R)
    ((continuous_const.mul (hρ.comp (continuous_id.div_const ε))))
    (shifted_support hs hε x) (shifted_mass hs hε x hmass)
    (fun r _ => dilate_nonneg hpos hε _) (mul_nonneg hε.le hR)
  intro r hr
  exact abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩

/-- Any positive-width family tending to zero gives strong Gaussian L2 convergence;
the original compact mass-one profile is arbitrary. -/
theorem scenery_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (x : ℝ) :
    Tendsto (fun i => wholeLineScenery (dilate ρ (ε i)) x) l (𝓝 (sourceScenery x)) := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by
      simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hroot : Tendsto (fun i => Real.sqrt (ε i * R)) l (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp (hlim.mul_const R))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hroot
    (fun i => norm_nonneg _)
  intro i
  exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg (hε i).le hR)).mpr
    (scenery_error hρ hpos hmass hR hs (hε i) x)

/-- The actual continuum kernel has the existing full closed source derivative,
not merely a finite-dimensional or formal Gaussian derivative. -/
theorem scenery_closedDerivative_graph {ρ : ℝ → ℝ} {R ε : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (hε : 0 < ε) (x : ℝ) :
    (wholeLineScenery (dilate ρ ε) x,
      Lp.const 2 gaussianProduct
        (kernelCoefficient (x-ε*R) (x+ε*R) x (dilate ρ ε))) ∈
      closedCylindricalDerivative.graph := by
  exact wholeLineScenery_closedDerivative_graph (x-ε*R) (x+ε*R) x (dilate ρ ε)
    (shifted_support hs hε x)

end OperatorDerivativeRewrite.Foundation.IBMDilatedMollifier
