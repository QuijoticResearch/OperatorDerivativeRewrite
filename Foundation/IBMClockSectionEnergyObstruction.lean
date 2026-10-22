import Foundation.IBMRandomTimeHilbert
import Foundation.GaussianSobolevQuantitative
import Foundation.GaussianLocalSobolev
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The actual scenery-valued clock section has no finite-energy Bochner
primitive on any nontrivial positive interval. This is a section obstruction;
identification with the original joint Gaussian derivative domain is separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockSectionEnergyObstruction
open InfiniteGaussian IBMContinuousScenery

def folded (r : ℝ) : GaussianL2 := sourceScenery |r|

theorem folded_increment_sq {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    ‖folded r - folded s‖ ^ 2 = |r - s| := by
  simpa only [folded, abs_of_nonneg hs, abs_of_nonneg hr] using
    sourceScenery_increment_sq s r

theorem randomSourceClass_eq (t : ℝ≥0) (ω : SampleSpace) :
    IBMRandomTimeHilbert.randomSourceClass t ω =
      folded (GaussianTimeProcess.process t ω) := rfl

theorem primitive_energy_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    ‖∫ x in Icc a b, g x‖ ^ 2 ≤
      (b - a) * ∫ x in Icc a b, ‖g x‖ ^ 2 := by
  have hc := GaussianSobolevFixedSupport.cs_setIntegral a b hab hg.norm
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Icc a b)) g
  have hi : 0 ≤ ∫ x in Icc a b, ‖g x‖ := integral_nonneg (fun _ => norm_nonneg _)
  have he : 0 ≤ ∫ x in Icc a b, ‖g x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  rw [abs_of_nonneg hi] at hc
  have hb : ‖∫ x in Icc a b, g x‖ ≤
      Real.sqrt (b - a) * Real.sqrt (∫ x in Icc a b, ‖g x‖ ^ 2) := hn.trans hc
  have hsq := pow_le_pow_left₀ (norm_nonneg (∫ x in Icc a b, g x)) hb 2
  simpa only [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt he] using hsq

/-- A Brownian spatial metric is incompatible with any locally finite L²
Bochner derivative, even when only increments from the left endpoint are required. -/
theorem no_finite_energy_primitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → E} {a b c : ℝ}
    (hab : a < b) (hc : 0 < c)
    (hF : ∀ x ∈ Icc a b, c * (x - a) ≤ ‖F x - F a‖ ^ 2)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    ¬ (∀ x ∈ Icc a b, F x - F a = ∫ y in Icc a x, g y) := by
  intro hp
  let x : ℕ → ℝ := fun n => a + (b - a) / ((n : ℝ) + 1)
  have hden (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hx (n : ℕ) : x n ∈ Icc a b := by
    dsimp [x]
    constructor
    · linarith [div_pos (sub_pos.mpr hab) (hden n)]
    · have h := (div_le_iff₀ (hden n)).2
        (show b-a ≤ (b - a) * ((n : ℝ) + 1) by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      linarith
  have hpos (n : ℕ) : 0 < x n - a := by
    dsimp [x]
    linarith [div_pos (sub_pos.mpr hab) (hden n)]
  have ht : Tendsto x atTop (𝓝 a) := by
    have h : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [add_zero] using tendsto_const_nhds.add h
  have hi : IntegrableOn (fun y => ‖g y‖ ^ 2) (Icc a b) volume :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hcont := (intervalIntegral.continuousOn_primitive_Icc hi) a ⟨le_rfl, hab.le⟩
  have ht' : Tendsto x atTop (𝓝[Icc a b] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hx⟩
  have hz : Tendsto (fun n => ∫ y in Icc a (x n), ‖g y‖ ^ 2) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hcont.tendsto.comp ht'
  obtain ⟨n, hn⟩ := (hz.eventually (eventually_lt_nhds hc)).exists
  have hg' : MemLp g 2 (volume.restrict (Icc a (x n))) :=
    hg.mono_measure (Measure.restrict_mono (Icc_subset_Icc_right (hx n).2) le_rfl)
  have hb := primitive_energy_bound (hx n).1 hg'
  rw [← hp (x n) (hx n)] at hb
  have hge : c ≤ ∫ y in Icc a (x n), ‖g y‖ ^ 2 := by
    nlinarith [hpos n, hF (x n) (hx n)]
  linarith

theorem folded_no_finite_energy_primitive {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {g : ℝ → GaussianL2} (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    ¬ (∀ x ∈ Icc a b, folded x - folded a = ∫ y in Icc a x, g y) := by
  apply no_finite_energy_primitive hab (show (0 : ℝ) < 1 by norm_num) _ hg
  intro x hx
  rw [folded_increment_sq ha (ha.trans hx.1), abs_of_nonneg (sub_nonneg.mpr hx.1)]
  simp

/-- Changing representatives or adding an arbitrary primitive constant does
not evade the obstruction for a continuous curve. -/
theorem no_finite_energy_primitive_ae {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → E} {a b c : ℝ}
    (hab : a < b) (hc : 0 < c) (hcont : ContinuousOn F (Icc a b))
    (hF : ∀ x ∈ Icc a b, c * (x - a) ≤ ‖F x - F a‖ ^ 2)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Icc a b))) (v : E) :
    ¬ (F =ᵐ[volume.restrict (Icc a b)] fun x => v + ∫ y in Icc a x, g y) := by
  intro hp
  have he := Measure.eqOn_of_ae_eq hp hcont
    (continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc
      (hg.integrable (by norm_num))))
    (show Icc a b ⊆ closure (interior (Icc a b)) by
      rw [closure_interior_Icc hab.ne])
  have ha := he ⟨le_rfl, hab.le⟩
  have ha' : F a = v := by simpa using ha
  apply no_finite_energy_primitive hab hc hF hg
  intro x hx
  rw [he hx, ha']
  simp

/-- Gaussian weighting cannot remove the local obstruction: the existing
positive-density comparison transfers a putative Gaussian L² derivative. -/
theorem folded_no_gaussian_energy_primitive {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {g : ℝ → GaussianL2} (hg : MemLp g 2 GaussianCore.γ) :
    ¬ (∀ x ∈ Icc a b, folded x - folded a = ∫ y in Icc a x, g y) := by
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison a b
  exact folded_no_finite_energy_primitive ha hab (hg.of_measure_le_smul hC hcmp)

/-- Positive clock rescaling does not repair the obstruction. In particular
the normalized observation section with scale sqrt(T), T>0, is excluded. -/
theorem scaled_folded_no_gaussian_energy_primitive {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c)
    {g : ℝ → GaussianL2} (hg : MemLp g 2 GaussianCore.γ) :
    ¬ (∀ x ∈ Icc a b, folded (c * x) - folded (c * a) = ∫ y in Icc a x, g y) := by
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison a b
  apply no_finite_energy_primitive hab hc _ (hg.of_measure_le_smul hC hcmp)
  intro x hx
  rw [folded_increment_sq (mul_nonneg hc.le ha) (mul_nonneg hc.le (ha.trans hx.1)),
    ← mul_sub, abs_mul, abs_of_pos hc, abs_of_nonneg (sub_nonneg.mpr hx.1)]

theorem scaled_folded_no_ae_primitive {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c)
    {g : ℝ → GaussianL2} (hg : MemLp g 2 GaussianCore.γ) (v : GaussianL2) :
    ¬ ((fun x => folded (c * x)) =ᵐ[volume.restrict (Icc a b)]
      fun x => v + ∫ y in Icc a x, g y) := by
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison a b
  apply no_finite_energy_primitive_ae hab hc _ _ (hg.of_measure_le_smul hC hcmp) v
  · exact (sourceScenery_continuous.comp
      ((continuous_const.mul continuous_id).abs)).continuousOn
  · intro x hx
    rw [folded_increment_sq (mul_nonneg hc.le ha) (mul_nonneg hc.le (ha.trans hx.1)),
      ← mul_sub, abs_mul, abs_of_pos hc, abs_of_nonneg (sub_nonneg.mpr hx.1)]

theorem scaled_folded_no_gaussian_ae_primitive {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hc : 0 < c)
    {g : ℝ → GaussianL2} (hg : MemLp g 2 GaussianCore.γ) (v : GaussianL2) :
    ¬ ((fun x => folded (c * x)) =ᵐ[GaussianCore.γ.restrict (Icc a b)]
      fun x => v + ∫ y in Icc a x, g y) := by
  intro hp
  have hv : (volume : Measure ℝ) ≪ GaussianCore.γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  exact scaled_folded_no_ae_primitive ha hab hc hg v ((hv.restrict (Icc a b)).ae_eq hp)


end OperatorDerivativeRewrite.Foundation.IBMClockSectionEnergyObstruction
