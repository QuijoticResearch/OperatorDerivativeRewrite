import Foundation.SignedDensityIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
noncomputable section
open MeasureTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.SignedClockComposition

def cell (a s : ℝ) : ℝ := (Ico a (a+1)).indicator (fun _ => 1) s

def halfLine : Measure ℝ := volume.restrict (Ici 0)

theorem cell_measurable (a : ℝ) : Measurable (cell a) := by
  exact measurable_const.indicator measurableSet_Ico

theorem cell_integrable (a : ℝ) : Integrable (cell a) halfLine := by
  have h : Integrable (cell a) volume := by
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact integrableOn_const (by simp [Real.volume_Ico])
  exact h.integrableOn

theorem cell_integral (a : ℝ) (ha : 0≤a) : (∫ s : ℝ, cell a s ∂halfLine)=1 := by
  unfold cell halfLine
  rw [integral_indicator measurableSet_Ico,Measure.restrict_restrict measurableSet_Ico]
  have he : Ico a (a+1) ∩ Ici 0=Ico a (a+1) := by
    ext s
    simp only [mem_inter_iff,mem_Ico,mem_Ici]
    constructor
    · tauto
    · intro hs
      exact ⟨hs,ha.trans hs.1⟩
  rw [he]
  norm_num [integral_const,Measure.real,Real.volume_Ico]

def density (t s : ℝ) : ℝ := (1+t)*cell 0 s-t*cell 1 s

theorem density_integrable (t : ℝ) : Integrable (density t) halfLine :=
  ((cell_integrable 0).const_mul (1+t)).sub ((cell_integrable 1).const_mul t)

theorem density_mass (t : ℝ) : (∫ s : ℝ, density t s ∂halfLine)=1 := by
  unfold density
  rw [integral_sub ((cell_integrable 0).const_mul _) ((cell_integrable 1).const_mul _),
    integral_const_mul,integral_const_mul,cell_integral 0 (by norm_num),cell_integral 1 (by norm_num)]
  ring

theorem bounded_observable (s : ℝ) : |cell 0 s|≤1 := by
  by_cases h : s∈Ico (0:ℝ) 1
  · simp [cell,h]
  · simp [cell,h]

theorem observable_product (t s : ℝ) : cell 0 s*density t s=(1+t)*cell 0 s := by
  by_cases h : s∈Ico (0:ℝ) 1
  · have hn : s∉Ico (1:ℝ) 2 := by
      intro hh
      exact (not_le_of_gt h.2) hh.1
    have h0 : cell 0 s=1 := by
      unfold cell
      rw [zero_add,indicator_of_mem h]
    have h1 : cell 1 s=0 := by
      unfold cell
      rw [show (1:ℝ)+1=2 from by norm_num,indicator_of_notMem hn]
    rw [density,h0,h1]
    ring
  · have h0 : cell 0 s=0 := by
      unfold cell
      rw [zero_add,indicator_of_notMem h]
    rw [h0,zero_mul,mul_zero]

theorem bounded_observable_composition (t : ℝ) :
    (∫ s : ℝ, cell 0 s*density t s ∂halfLine)=1+t := by
  simp_rw [observable_product]
  rw [integral_const_mul,cell_integral 0 (by norm_num),mul_one]

/-- The repair requires an L1 norm, not signed mass. -/
theorem composition_bound (f g : ℝ → ℝ) (hg : Integrable g halfLine)
    (hf : AEStronglyMeasurable f halfLine) (M : ℝ) (hb : ∀ s, |f s|≤M) :
    |∫ s : ℝ, f s*g s ∂halfLine|≤M*(∫ s : ℝ, |g s| ∂halfLine) := by
  have hi : Integrable (fun s => f s*g s) halfLine := by
    simpa only [mul_comm] using hg.mul_bdd hf (Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hb s))
  calc
    _ ≤ ∫ s : ℝ, |f s*g s| ∂halfLine := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun s => f s*g s)
    _ ≤ ∫ s : ℝ, M*|g s| ∂halfLine := by
      apply integral_mono_ae hi.norm (hg.norm.const_mul M)
      exact Eventually.of_forall fun s => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right (hb s) (abs_nonneg (g s))
    _ = _ := integral_const_mul _ _


theorem density_measurable (t : ℝ) : Measurable (density t) :=
  ((cell_measurable 0).const_mul (1+t)).sub ((cell_measurable 1).const_mul t)

/-- A genuine finite signed clock on nonnegative operational times. -/
def law (t : ℝ) : SignedMeasure ℝ := halfLine.withDensityᵥ (density t)

theorem law_mass (t : ℝ) : law t univ=1 := by
  rw [law,withDensityᵥ_apply (density_integrable t) MeasurableSet.univ,
    Measure.restrict_univ,density_mass]

/-- Constant signed mass1 does NOT bound the composition of one fixed bounded test. -/
theorem no_uniform_mass_bound :
    ¬∃ C : ℝ, ∀ t : ℝ, 0≤t → |∫ s : ℝ, cell 0 s*density t s ∂halfLine|≤C := by
  rintro ⟨C,h⟩
  let t := max C 0+1
  have ht : 0≤t := by dsimp [t];have := le_max_right C 0;linarith
  have hb := h t ht
  rw [bounded_observable_composition,abs_of_nonneg (by linarith : 0≤1+t)] at hb
  have hc := le_max_left C 0
  dsimp [t] at hb
  linarith


/-- The counterexample pairing is the ACTUAL signed-measure integral, not prescribed moments. -/
theorem signed_observable_composition (t : ℝ) :
    (∫ᵛ s : ℝ, (cell 0 s:ℂ) ∂<•law t)=((1+t:ℝ):ℂ) := by
  have hm : Measurable (fun s : ℝ => (cell 0 s:ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (cell_measurable 0)
  have hb (s : ℝ) : ‖(cell 0 s:ℂ)‖≤1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using bounded_observable s
  calc
    _ = ∫ s : ℝ, density t s • (cell 0 s:ℂ) ∂halfLine :=
      SignedDensityIntegral.integral_density halfLine (density t) (density_integrable t)
        (density_measurable t) _ hm 1 hb
    _ = ((∫ s : ℝ, cell 0 s*density t s ∂halfLine:ℝ):ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        change density t s • (cell 0 s:ℂ)=((cell 0 s*density t s:ℝ):ℂ)
        rw [Complex.real_smul,Complex.ofReal_mul]
        ring
    _ = _ := congrArg Complex.ofReal (bounded_observable_composition t)

end OperatorDerivativeRewrite.Foundation.SignedClockComposition
