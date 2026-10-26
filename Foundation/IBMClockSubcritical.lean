import Foundation.IBMClockNoiseThreshold
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-! Sharp power and Bessel-weighted ORIGINAL clock-sector criterion for the
actual reflected-clock IBM endpoint, retaining all scenery randomness. Positive
series/integral exchange and explicit per-mode lower bounds are proved.
This is not yet a fractional closed-operator domain identification. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockSubcritical
open IBMClockNoiseRegularity IBMClockNoiseThreshold

def kernel (a : ℝ) (n : ℕ) (h : ℝ) : ℝ := 2*(1-(1-h)^n)/h^(1+a)
def modeIntegral (a : ℝ) (n : ℕ) : ℝ := ∫ h in Ioo (0:ℝ) 1, kernel a n h

theorem kernel_nonneg (a : ℝ) (n : ℕ) (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    0 ≤ kernel a n h := by
  have hz := (power_defect_bounds n h h0.le h1).1
  unfold kernel
  positivity

theorem linear_power (a h : ℝ) (hh : 0 < h) :
    h/h^(1+a) = h^(-a) := by
  calc
    _ = h^(1:ℝ)/h^(1+a) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hh]; congr 1; ring

theorem kernel_integrable (a : ℝ) (ha : a < 1) (n : ℕ) :
    IntegrableOn (kernel a n) (Ioo 0 1) volume := by
  have hi : IntegrableOn (fun h : ℝ => h^(-a)) (Ioo 0 1) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -a) (by norm_num : (0:ℝ)<1)).2 (by linarith)
  apply (hi.const_mul (2*(n:ℝ))).mono'
  · have hm : Measurable (kernel a n) := by unfold kernel; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg a n h hh.1 hh.2.le)]
    have hb := (power_defect_bounds n h hh.1.le hh.2.le).2.trans (min_le_right _ _)
    have hp : 0 ≤ h^(1+a) := Real.rpow_nonneg hh.1.le _
    calc
      kernel a n h ≤ (2*((n:ℝ)*h))/h^(1+a) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hp
      _ = 2*(n:ℝ)*h^(-a) := by rw [← linear_power a h hh.1]; ring

theorem integral_power (a b : ℝ) (ha : a < 1) (hb : 0 < b) :
    (∫ h in Ioo (0:ℝ) b, h^(-a)) = b^(1-a)/(1-a) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le]
  rw [integral_rpow (Or.inl (by linarith : -1 < -a))]
  have he : -a+1 = 1-a := by ring
  rw [he,Real.zero_rpow (by linarith : 1-a ≠ 0),sub_zero]




theorem modeIntegral_lower (a : ℝ) (ha : a < 1) (n : ℕ) (hn : n ≠ 0) :
    ((1/2:ℝ)^(1-a)/(1-a))*(n:ℝ)^a ≤ modeIntegral a n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  let b : ℝ := (1/2)/(n:ℝ)
  have hb : 0 < b := div_pos (by norm_num) hn0
  have hb1 : b ≤ 1 := (div_le_iff₀ hn0).2 (by linarith)
  have hsub : Ioo (0:ℝ) b ⊆ Ioo (0:ℝ) 1 := fun h hh => ⟨hh.1,hh.2.trans_le hb1⟩
  have hi := kernel_integrable a ha n
  have hp : IntegrableOn (fun h : ℝ => (n:ℝ)*h^(-a)) (Ioo 0 b) volume :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := -a) hb).2 (by linarith)).const_mul (n:ℝ)
  have hl : (∫ h in Ioo (0:ℝ) b, (n:ℝ)*h^(-a)) ≤
      ∫ h in Ioo (0:ℝ) b, kernel a n h := by
    apply integral_mono_ae hp (hi.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hnh : (n:ℝ)*h ≤ 1/2 := by
      have hx := (le_div_iff₀ hn0).1 hh.2.le
      nlinarith
    have hbound := power_defect_lower n h hh.1.le (hh.2.le.trans hb1) hnh
    calc
      (n:ℝ)*h^(-a) = ((n:ℝ)*h)/h^(1+a) := by rw [← linear_power a h hh.1]; ring
      _ ≤ kernel a n h := by
        unfold kernel
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hh.1.le _)
        linarith
  have hu : (∫ h in Ioo (0:ℝ) b, kernel a n h) ≤ modeIntegral a n :=
    setIntegral_mono_set hi
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
          exact kernel_nonneg a n h hh.1 hh.2.le)
      (Filter.Eventually.of_forall fun h hh => hsub hh)
  have he : (n:ℝ)*b^(1-a) = (1/2:ℝ)^(1-a)*(n:ℝ)^a := by
    dsimp [b]
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1/2) hn0.le]
    calc
      _ = (1/2:ℝ)^(1-a)*((n:ℝ)^(1:ℝ)/(n:ℝ)^(1-a)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_sub hn0]; congr 2; ring
  rw [integral_const_mul,integral_power a b ha hb] at hl
  calc
    _ = (n:ℝ)*(b^(1-a)/(1-a)) := by rw [← mul_div_assoc,he]; ring
    _ ≤ _ := hl.trans hu



theorem weighted_mode_integrals_summable (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (K : ℝ) (hseries : ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      HasSum (fun (n : ℕ) => 2*(1-(1-h)^n)*C n) (K*rate h))
    (a : ℝ) (ha : a < 1/2) : Summable (fun n => modeIntegral a n*C n) := by
  have hs (h : ℝ) (hh : h ∈ Ioo (0:ℝ) 1) :
      HasSum (fun n => kernel a n h*C n) (K*weightedRate a h) := by
    have ht := (hseries h hh.1.le hh.2.le).div_const (h^(1+a))
    convert ht using 1
    · funext n; unfold kernel; ring
    · unfold weightedRate; ring
  have hm (n : ℕ) : AEStronglyMeasurable (fun h => kernel a n h*C n)
      (volume.restrict (Ioo (0:ℝ) 1)) := by
    have hm' : Measurable (fun h => kernel a n h*C n) := by unfold kernel; fun_prop
    exact hm'.aestronglyMeasurable
  have hz (n : ℕ) : ∀ᵐ h ∂volume.restrict (Ioo (0:ℝ) 1), 0 ≤ kernel a n h*C n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact mul_nonneg (kernel_nonneg a n h hh.1 hh.2.le) (hC n)
  have hb : Integrable (fun h => ∑' n, kernel a n h*C n) (volume.restrict (Ioo (0:ℝ) 1)) := by
    apply ((weighted_integrable_iff a).2 ha).const_mul K |>.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact (hs h hh).tsum_eq.symm
  have ht := hasSum_integral_of_dominated_convergence
    (fun n h => kernel a n h*C n) hm
    (fun n => (hz n).mono fun h hh => le_of_eq (Real.norm_of_nonneg hh))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
        exact (hs h hh).summable)
    hb
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
        exact hs h hh)
  have he (n : ℕ) : (∫ h in Ioo (0:ℝ) 1, kernel a n h*C n) = modeIntegral a n*C n := by
    rw [integral_mul_const]; rfl
  simpa only [he] using ht.summable



theorem power_weight_summable (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (K : ℝ) (hseries : ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      HasSum (fun (n : ℕ) => 2*(1-(1-h)^n)*C n) (K*rate h))
    (a : ℝ) (ha : a < 1/2) : Summable (fun (n : ℕ) => (n:ℝ)^a*C n) := by
  let L : ℝ := (1/2:ℝ)^(1-a)/(1-a)
  have hL : 0 < L := div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  have hs := weighted_mode_integrals_summable C hC K hseries a ha
  have hs' := (summable_nat_add_iff 1).2 (hs.div_const L)
  apply (summable_nat_add_iff 1).1
  apply Summable.of_nonneg_of_le (fun n => by have hc := hC (n+1); positivity) _ hs'
  intro n
  apply (le_div_iff₀ hL).2
  have hl := mul_le_mul_of_nonneg_right (modeIntegral_lower a (by linarith : a < 1)
    (n+1) (by omega)) (hC (n+1))
  dsimp [L]
  nlinarith

theorem bessel_weight_summable (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (K : ℝ) (hseries : ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      HasSum (fun (n : ℕ) => 2*(1-(1-h)^n)*C n) (K*rate h))
    (a : ℝ) (ha : a < 1/2) : Summable (fun (n : ℕ) => ((n:ℝ)+1)^a*C n) := by
  rcases le_total a 0 with ha0|ha0
  · have hs : Summable C := by
      simpa only [Real.rpow_zero,one_mul] using power_weight_summable C hC K hseries 0 (by norm_num)
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hC n)) _ hs
    intro n
    have hn : (1:ℝ) ≤ (n:ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
    have hw : ((n:ℝ)+1)^a ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn ha0
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (hC n)
  · have hs := (power_weight_summable C hC K hseries a ha).mul_left ((2:ℝ)^a)
    have hs' := (summable_nat_add_iff 1).2 hs
    apply (summable_nat_add_iff 1).1
    apply Summable.of_nonneg_of_le (fun n => by have hc := hC (n+1); positivity) _ hs'
    intro n
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hw : (((n+1:ℕ):ℝ)+1)^a ≤ (2:ℝ)^a*((n+1:ℕ):ℝ)^a := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (n+1:ℕ))]
      apply Real.rpow_le_rpow (by positivity) (by linarith) ha0
    have hb := mul_le_mul_of_nonneg_right hw (hC (n+1))
    simpa only [mul_assoc] using hb

open GaussianClockValueOperators IBMClockLinearDivergence

theorem actual_bessel_summable_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    Summable (fun (n : ℕ) => ((n:ℝ)+1)^a*
      ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2)
      ↔ a < 1/2 := by
  constructor
  · intro hs
    by_contra ha
    exact actual_not_summable_bessel T hT a (le_of_not_gt ha) hs
  · intro ha
    exact bessel_weight_summable _ (fun n => sq_nonneg _)
      (‖timeDirection T‖*GaussianAbsoluteMoments.standardMoment 1)
      (IBMClockNoiseSpectral.actual_clock_noise_series T hT) a ha



theorem actual_power_summable_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    Summable (fun (n : ℕ) => (n:ℝ)^a*
      ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2)
      ↔ a < 1/2 := by
  constructor
  · intro hs
    by_contra ha
    apply actual_not_summable_sqrt T hT
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    cases n with
    | zero => simp only [Nat.cast_zero,Real.sqrt_zero]; exact Real.rpow_nonneg (by norm_num) _
    | succ n =>
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (le_of_not_gt ha)
  · intro ha
    exact power_weight_summable _ (fun n => sq_nonneg _)
      (‖timeDirection T‖*GaussianAbsoluteMoments.standardMoment 1)
      (IBMClockNoiseSpectral.actual_clock_noise_series T hT) a ha

theorem actual_energy_integrability_iff_bessel (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    IntegrableOn (endpointWeightedEnergy T hT a) (Ioo 0 1) volume ↔
      Summable (fun (n : ℕ) => ((n:ℝ)+1)^a*
        ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2) :=
  (endpoint_energy_integrable_iff T hT a).trans (actual_bessel_summable_iff T hT a).symm

end OperatorDerivativeRewrite.Foundation.IBMClockSubcritical
