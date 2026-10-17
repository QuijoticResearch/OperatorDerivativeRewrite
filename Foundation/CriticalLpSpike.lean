import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic

/-! A fixed probability-space critical L3 bound does not imply L3 convergence or domination. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.CriticalLpSpike
set_option backward.isDefEq.respectTransparency false
private instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

def unitLaw : Measure ℝ := volume.restrict (Ioc 0 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw, Measure.restrict_apply, Real.volume_Ioc]

def height (n : ℕ) : ℝ := (n : ℝ)+1
def width (n : ℕ) : ℝ := (height n)⁻¹^3

theorem height_ge_one (n : ℕ) : 1 ≤ height n := by
  unfold height
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem height_pos (n : ℕ) : 0 < height n := lt_of_lt_of_le zero_lt_one (height_ge_one n)
theorem width_nonneg (n : ℕ) : 0 ≤ width n :=
  pow_nonneg (inv_nonneg.mpr (height_pos n).le) 3
theorem width_le_one (n : ℕ) : width n ≤ 1 :=
  pow_le_one₀ (inv_nonneg.mpr (height_pos n).le) (inv_le_one_of_one_le₀ (height_ge_one n))

theorem interval_measure (n : ℕ) : unitLaw (Ioc 0 (width n)) = ENNReal.ofReal (width n) := by
  rw [unitLaw, Measure.restrict_apply measurableSet_Ioc]
  have hs : Ioc 0 (width n) ∩ Ioc 0 (1 : ℝ) = Ioc 0 (width n) :=
    inter_eq_left.mpr fun x hx => ⟨hx.1, hx.2.trans (width_le_one n)⟩
  rw [hs, Real.volume_Ioc, sub_zero]

theorem interval_measure_real (n : ℕ) : unitLaw.real (Ioc 0 (width n)) = width n := by
  rw [measureReal_def, interval_measure, ENNReal.toReal_ofReal (width_nonneg n)]

def spike (n : ℕ) : ℝ → ℝ := (Ioc 0 (width n)).indicator fun _ => height n

theorem spike_memLp (n : ℕ) : MemLp (spike n) 3 unitLaw :=
  memLp_indicator_const 3 measurableSet_Ioc (height n) (Or.inr (measure_ne_top _ _))

def spikeL3 (n : ℕ) : Lp ℝ 3 unitLaw := (spike_memLp n).toLp (spike n)

theorem spikeL3_coeFn (n : ℕ) : spikeL3 n =ᵐ[unitLaw] spike n := MemLp.coeFn_toLp _

theorem power_integral (n q : ℕ) (hq : q ≠ 0) :
    (∫ x, |spike n x|^q ∂unitLaw) = (height n)^q*width n := by
  have he : (fun x => |spike n x|^q) =
      (Ioc 0 (width n)).indicator (fun _ : ℝ => (height n)^q) := by
    funext x
    by_cases hx : x ∈ Ioc 0 (width n)
    · simp only [spike, indicator_of_mem hx, abs_of_nonneg (height_pos n).le]
    · simp only [spike, indicator_of_notMem hx, abs_zero, zero_pow hq]
  rw [he, integral_indicator measurableSet_Ioc, setIntegral_const, interval_measure_real]
  simp only [smul_eq_mul]
  ring

theorem cubic_energy (n : ℕ) : (∫ x, |spike n x|^3 ∂unitLaw) = 1 := by
  rw [power_integral n 3 (by omega), width, ← mul_pow,
    mul_inv_cancel₀ (ne_of_gt (height_pos n)), one_pow]

theorem fourth_energy (n : ℕ) : (∫ x, |spike n x|^4 ∂unitLaw) = height n := by
  rw [power_integral n 4 (by omega), width]
  field_simp

theorem spikeL3_norm (n : ℕ) : ‖spikeL3 n‖ = 1 := by
  rw [spikeL3, Lp.norm_toLp,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (spike_memLp n)]
  have he : (∫ x, ‖spike n x‖^((3 : ℝ≥0∞).toReal) ∂unitLaw) = 1 := by
    have hr (x : ℝ) : ‖spike n x‖^((3 : ℝ≥0∞).toReal) = |spike n x|^3 := by
      rw [Real.norm_eq_abs]
      convert Real.rpow_natCast (|spike n x|) 3 using 1; norm_num
    exact (integral_congr_ae (ae_of_all _ hr)).trans (cubic_energy n)
  rw [he]
  simp

theorem width_tendsto : Tendsto width atTop (𝓝 0) := by
  have hh : Tendsto height atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hh
  change Tendsto (fun n => (height n)⁻¹^3) atTop (𝓝 0)
  simpa only [Function.comp_apply, zero_pow (by omega : 3 ≠ 0)] using hi.pow 3

theorem spike_pointwise_tendsto (x : ℝ) :
    Tendsto (fun n => spike n x) atTop (𝓝 0) := by
  by_cases hx : 0 < x
  · have he : ∀ᶠ n : ℕ in atTop, spike n x = 0 := by
      filter_upwards [width_tendsto.eventually (eventually_lt_nhds hx)] with n hn
      exact indicator_of_notMem (show x ∉ Ioc 0 (width n) from fun h => (not_le.mpr hn) h.2) _
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      (he.mono fun n hn => hn.symm)
  · have he : ∀ n, spike n x = 0 := by
      intro n
      exact indicator_of_notMem (show x ∉ Ioc 0 (width n) from fun h => hx h.1) _
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem spike_ae_tendsto :
    ∀ᵐ x ∂unitLaw, Tendsto (fun n => spike n x) atTop (𝓝 0) :=
  ae_of_all _ spike_pointwise_tendsto

theorem not_L3_tendsto_zero : ¬ Tendsto spikeL3 atTop (𝓝 0) := by
  intro ht
  have hz : Tendsto (fun n => ‖spikeL3 n‖) atTop (𝓝 (0 : ℝ)) := by simpa using ht.norm
  have ho : Tendsto (fun n => ‖spikeL3 n‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [spikeL3_norm] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have he := tendsto_nhds_unique hz ho
  norm_num at he

theorem fourth_energy_diverges :
    Tendsto (fun n => ∫ x, |spike n x|^4 ∂unitLaw) atTop atTop := by
  simp only [fourth_energy]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

theorem no_integrable_cubic_dominator :
    ¬ ∃ g : ℝ → ℝ, Integrable g unitLaw ∧
      ∀ n : ℕ, ∀ᵐ x ∂unitLaw, |spike n x|^3 ≤ g x := by
  rintro ⟨g, hg, hb⟩
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => |spike n x|^3) unitLaw := by
    have he : ((fun x => ‖spike n x‖)^3) = (fun x => |spike n x|^3) := by
      funext x
      simp only [Pi.pow_apply, Real.norm_eq_abs]
    rw [← he]
    exact (spike_memLp n).aestronglyMeasurable.norm.pow 3
  have hbound (n : ℕ) : ∀ᵐ x ∂unitLaw, ‖|spike n x|^3‖ ≤ g x := by
    filter_upwards [hb n] with x hx
    have hn : 0 ≤ |spike n x|^3 := pow_nonneg (abs_nonneg _) 3
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hx
  have hlim : ∀ᵐ x ∂unitLaw, Tendsto (fun n => |spike n x|^3) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs, norm_zero, zero_pow (by omega : 3 ≠ 0)] using
      (spike_pointwise_tendsto x).norm.pow 3
  have ht := tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim
  have hzero : Tendsto (fun n => ∫ x, |spike n x|^3 ∂unitLaw) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using ht
  have hone : Tendsto (fun n => ∫ x, |spike n x|^3 ∂unitLaw) atTop (𝓝 (1 : ℝ)) := by
    simpa only [cubic_energy] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have he := tendsto_nhds_unique hzero hone
  norm_num at he

theorem spike_eLpNorm (n : ℕ) : eLpNorm (spike n) 3 unitLaw = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  simpa only [spikeL3, Lp.norm_toLp] using spikeL3_norm n

theorem not_unifIntegrable : ¬ UnifIntegrable spike 3 unitLaw := by
  intro hui
  have ht := tendsto_Lp_finite_of_tendsto_ae (p := 3) (by norm_num) (by norm_num)
    (f := spike) (g := (0 : ℝ → ℝ))
    (fun n => (spike_memLp n).aestronglyMeasurable) (memLp_const (0 : ℝ)) hui spike_ae_tendsto
  have hzero : Tendsto (fun n => eLpNorm (spike n) 3 unitLaw) atTop (𝓝 0) := by
    simpa only [sub_zero] using ht
  have hone : Tendsto (fun n => eLpNorm (spike n) 3 unitLaw) atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [spike_eLpNorm] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1))
  have he := tendsto_nhds_unique hzero hone
  norm_num at he

theorem not_uniformIntegrable : ¬ UniformIntegrable spike 3 unitLaw :=
  fun h => not_unifIntegrable h.1

end OperatorDerivativeRewrite.Foundation.CriticalLpSpike
