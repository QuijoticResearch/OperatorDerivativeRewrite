import Mathlib.Probability.HasLaw
import Foundation.PoissonPolynomialExamples
import Foundation.BochnerL2Dominated
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual compensated-count norms obstruct a plain Lp lower bound for p<2. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonLpLowerObstruction
set_option backward.isDefEq.respectTransparency false
open PoissonDifferenceCore PoissonDifferenceOperators PoissonPolynomialExamples PoissonMoments

abbrev exponent : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
local instance : Fact (1 ≤ exponent) := ⟨by simpa [exponent] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 4/3 by norm_num)⟩
theorem exponent_le_two : exponent ≤ 2 := by
  simpa [exponent] using ENNReal.ofReal_le_ofReal (show (4/3 : ℝ) ≤ 2 by norm_num)
local instance (r : ℝ≥0) : IsFiniteMeasure ((r : ℝ≥0∞) • poissonLaw r) := ⟨by simp⟩

theorem centered_variance (r : ℝ≥0) (hr : 0 < r) :
    (∫ n, centeredCount r n^2 ∂poissonLaw r)=(r : ℝ) := by
  have hp : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonLaw r) := by
    simpa only [pow_one] using poisson_power_memLp_two r hr 1
  have hc := hp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := (poisson_power_memLp_two r hr 2).integrable (by norm_num)
  have he : (fun n : ℕ => centeredCount r n^2)=
      fun n : ℕ => (n : ℝ)^2-2*(r : ℝ)*(n : ℝ)+(r : ℝ)^2 := by
    funext n
    unfold centeredCount
    ring
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2-2*(r : ℝ)*(n : ℝ)) (poissonLaw r) := hs.sub (hc.const_mul (2*(r : ℝ)))
  rw [he,integral_add hi (integrable_const _),
    integral_sub hs (hc.const_mul _),integral_const_mul,integral_poisson_count_sq r hr,
    integral_poisson_count r hr,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  ring

theorem centered_L2_energy (r : ℝ≥0) (hr : 0 < r) : ‖centeredCountL2 r hr‖^2=(r : ℝ) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ n, ‖centeredCountL2 r hr n‖^2 ∂poissonLaw r)=
      ∫ n, centeredCount r n^2 ∂poissonLaw r := by
    apply integral_congr_ae
    exact ae_of_all _ (fun n => by
      change ‖centeredCountL2 r hr n‖^2=centeredCount r n^2
      rw [centeredCountL2_apply r hr,Real.norm_eq_abs,sq_abs])
  rw [he,centered_variance r hr]

theorem centered_memLp (r : ℝ≥0) (hr : 0 < r) : MemLp (centeredCount r) exponent (poissonLaw r) :=
  (centeredCount_memLp r hr).mono_exponent exponent_le_two

def output (r : ℝ≥0) (hr : 0 < r) : Lp ℝ exponent (poissonLaw r) :=
  (centered_memLp r hr).toLp (centeredCount r)

def input (r : ℝ≥0) : Lp ℝ exponent ((r : ℝ≥0∞) • poissonLaw r) :=
  (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem output_norm_le_L2 (r : ℝ≥0) (hr : 0 < r) : ‖output r hr‖ ≤ ‖centeredCountL2 r hr‖ := by
  rw [output,centeredCountL2,Lp.norm_toLp,Lp.norm_toLp]
  exact ENNReal.toReal_mono (centeredCount_memLp r hr).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := centeredCount r) exponent_le_two)

theorem output_norm_le_sqrt (r : ℝ≥0) (hr : 0 < r) : ‖output r hr‖ ≤ Real.sqrt (r : ℝ) := by
  have he := centered_L2_energy r hr
  have hn : ‖centeredCountL2 r hr‖=Real.sqrt (r : ℝ) := by
    nlinarith [norm_nonneg (centeredCountL2 r hr),Real.sqrt_nonneg (r : ℝ),Real.sq_sqrt r.coe_nonneg]
  rw [← hn]
  exact output_norm_le_L2 r hr

theorem input_norm (r : ℝ≥0) : ‖input r‖=(r : ℝ)^(3/4 : ℝ) := by
  rw [input,Lp.norm_toLp,eLpNorm_const' (1 : ℝ) (by norm_num [exponent]) (by norm_num [exponent])]
  simp only [enorm_one,one_mul,Measure.smul_apply,measure_univ,mul_one,
    ← ENNReal.toReal_rpow,ENNReal.coe_toReal]
  norm_num [exponent]

def rate (n : ℕ) : ℝ≥0 := (n : ℝ≥0)^4

theorem rate_pos {n : ℕ} (hn : 0 < n) : 0 < rate n := by unfold rate; positivity

theorem input_norm_rate (n : ℕ) : ‖input (rate n)‖=(n : ℝ)^3 := by
  rw [input_norm]
  change ((n : ℝ)^4)^(3/4 : ℝ)=(n : ℝ)^3
  rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ n) 4 (3/4 : ℝ)]
  norm_num [Real.rpow_natCast]

theorem output_norm_rate {n : ℕ} (hn : 0 < n) :
    ‖output (rate n) (rate_pos hn)‖ ≤ (n : ℝ)^2 := by
  have h := output_norm_le_sqrt (rate n) (rate_pos hn)
  have he : Real.sqrt (rate n : ℝ)=(n : ℝ)^2 := by
    change Real.sqrt ((n : ℝ)^4)=(n : ℝ)^2
    rw [show (n : ℝ)^4=((n : ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rwa [he] at h

/-- No positive lower constant works even on actual constant Poisson input fields. -/
theorem no_uniform_lower : ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ hn : 0 < n,
    c*‖input (rate n)‖ ≤ ‖output (rate n) (rate_pos hn)‖ := by
  rintro ⟨c,hc,hbound⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (1/c))
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 1) ((le_max_left _ _).trans_lt hn))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcN : 1 < c*(n : ℝ) := by
    have hh : 1/c < (n : ℝ) := (le_max_right _ _).trans_lt hn
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hh
  have hb := (hbound n hn0).trans (output_norm_rate hn0)
  rw [input_norm_rate] at hb
  have hsq : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  nlinarith [mul_pos hsq (sub_pos.mpr hcN)]

theorem norm_ratio_le {n : ℕ} (hn : 0 < n) :
    ‖output (rate n) (rate_pos hn)‖/‖input (rate n)‖ ≤ 1/(n : ℝ) := by
  rw [input_norm_rate]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (pow_pos hnR 3)).mpr
  calc
    _ ≤ (n : ℝ)^2 := output_norm_rate hn
    _ = (1/(n : ℝ))*(n : ℝ)^3 := by field_simp

theorem divergence_one_actual (r : ℝ≥0) (hr : 0 < r) :
    (PoissonMaximalOperators.maximalDivergence r hr)
      ⟨constantOneField r,constantOneField_mem_divergence_domain r hr⟩=centeredCountL2 r hr :=
  divergence_one_eq_centeredCount r hr

section Transport
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def lawOutput (X : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r) (hX : HasLaw X (poissonLaw r) μ) :
    Lp ℝ exponent μ := (hX.memLp_comp (centered_memLp r hr)).toLp (centeredCount r ∘ X)

theorem lawOutput_ae (X : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r) (hX : HasLaw X (poissonLaw r) μ) :
    lawOutput X r hr hX =ᵐ[μ] fun ω => (X ω : ℝ)-(r : ℝ) :=
  MemLp.coeFn_toLp _

theorem lawOutput_norm (X : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r) (hX : HasLaw X (poissonLaw r) μ) :
    ‖lawOutput X r hr hX‖=‖output r hr‖ := by
  have hm : AEStronglyMeasurable (centeredCount r) (Measure.map X μ) := by
    rw [hX.map_eq]
    exact (centered_memLp r hr).aestronglyMeasurable
  have he := eLpNorm_map_measure (p := exponent) hm hX.aemeasurable
  rw [hX.map_eq] at he
  rw [lawOutput,output,Lp.norm_toLp,Lp.norm_toLp]
  exact congrArg ENNReal.toReal he.symm

theorem no_lower_for_count_laws (X : ℕ → Ω → ℕ)
    (hX : ∀ n, HasLaw (X n) (poissonLaw (rate n)) μ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ hn : 0 < n,
      c*(n : ℝ)^3 ≤ ‖lawOutput (X n) (rate n) (rate_pos hn) (hX n)‖ := by
  rintro ⟨c,hc,hbound⟩
  apply no_uniform_lower
  refine ⟨c,hc,?_⟩
  intro n hn
  rw [input_norm_rate]
  have h := hbound n hn
  rwa [lawOutput_norm] at h

theorem indicator_memLp (ρ : Measure M) (A : Set M) (hA : MeasurableSet A)
    (r : ℝ≥0) (hMass : ρ A=(r : ℝ≥0∞)) :
    MemLp (A.indicator (fun _ => (1 : ℝ))) exponent ρ := by
  change eLpNorm (A.indicator (fun _ => (1 : ℝ))) exponent ρ < ∞
  rw [eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num [exponent]) (by norm_num [exponent]),hMass]
  simp only [enorm_one,one_mul]
  finiteness

theorem indicator_norm (ρ : Measure M) (A : Set M) (hA : MeasurableSet A)
    (r : ℝ≥0) (hMass : ρ A=(r : ℝ≥0∞)) :
    (eLpNorm (A.indicator (fun _ => (1 : ℝ))) exponent ρ).toReal=‖input r‖ := by
  rw [eLpNorm_indicator_const hA.nullMeasurableSet (by norm_num [exponent]) (by norm_num [exponent]),hMass,input_norm]
  simp only [enorm_one,one_mul,← ENNReal.toReal_rpow,ENNReal.coe_toReal]
  norm_num [exponent]

/-- A fixed control measure and common probability space still cannot give the claimed lower bound. -/
theorem no_indicator_lower (ρ : Measure M) (A : ℕ → Set M)
    (hA : ∀ n, MeasurableSet (A n)) (hMass : ∀ n, ρ (A n)=(rate n : ℝ≥0∞))
    (X : ℕ → Ω → ℕ) (hX : ∀ n, HasLaw (X n) (poissonLaw (rate n)) μ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ hn : 0 < n,
      c*(eLpNorm ((A n).indicator (fun _ => (1 : ℝ))) exponent ρ).toReal ≤
        ‖lawOutput (X n) (rate n) (rate_pos hn) (hX n)‖ := by
  rintro ⟨c,hc,hbound⟩
  apply no_lower_for_count_laws X hX
  refine ⟨c,hc,?_⟩
  intro n hn
  have h := hbound n hn
  rwa [indicator_norm ρ (A n) (hA n) (rate n) (hMass n),input_norm_rate] at h

end Transport
end OperatorDerivativeRewrite.Foundation.PoissonLpLowerObstruction
