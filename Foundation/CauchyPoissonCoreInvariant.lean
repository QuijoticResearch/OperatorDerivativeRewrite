import Foundation.ContinuousTorusFourier
import Foundation.CauchyCenteredEnergy
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual Poisson-kernel angle probability measure and infinitesimal invariance
for the finite trigonometric Cauchy/sine-drift core. Parameter |q|<1 and drift
r=2q/(1-q^2). No closed-domain, semigroup invariance, path construction or entropy
inequality is asserted. The wrapped-Cauchy family itself is known. -/
noncomputable section
open MeasureTheory Complex Metric
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonCoreInvariant

def density (q θ : ℝ) : ℝ := poissonKernel 0 (q : ℂ) (circleMap 0 1 θ)

theorem pole_inside (q : ℝ) (hq : |q| < 1) : (q : ℂ) ∈ ball 0 1 := by
  simpa [mem_ball, dist_zero_right, Complex.norm_real] using hq

theorem poisson_moment_nat (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (q : ℂ) z • z^n) 0 1 = (q : ℂ)^n := by
  have hf : DiffContOnCl ℂ (fun z : ℂ => z^n) (ball 0 1) :=
    (differentiable_id.pow n).diffContOnCl
  exact hf.circleAverage_poissonKernel_smul (pole_inside q hq)

theorem density_mass (q : ℝ) (hq : |q| < 1) :
    (2*Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi, density q θ) = 1 := by
  have h := poisson_moment_nat q hq 0
  simp only [pow_zero, Real.circleAverage_def] at h
  have he := congrArg Complex.re h
  simpa [density, Complex.real_smul, intervalIntegral.integral_ofReal] using he

theorem density_positive (q : ℝ) (hq : |q| < 1) (θ : ℝ) : 0 < density q θ := by
  have hn : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by simp
  have hd : circleMap (0 : ℂ) 1 θ - (q : ℂ) ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [hn, Complex.norm_real] at he
    exact (ne_of_lt hq) he.symm
  unfold density poissonKernel
  simp only [sub_zero, hn, Complex.norm_real, Real.norm_eq_abs, one_pow]
  apply div_pos _ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd))
  nlinarith [abs_nonneg q]

theorem density_continuous (q : ℝ) (hq : |q| < 1) : Continuous (density q) := by
  unfold density poissonKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  simp only [sub_zero]
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  have hn : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by simp
  rw [hn, Complex.norm_real, Real.norm_eq_abs] at hh
  exact (ne_of_lt hq) hh.symm

def normalizedDensity (q θ : ℝ) : ℝ := (2*Real.pi)⁻¹ * density q θ

def law (q : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (2*Real.pi))).withDensity
    (fun θ => ENNReal.ofReal (normalizedDensity q θ))

theorem normalizedDensity_integrable (q : ℝ) (hq : |q| < 1) :
    Integrable (normalizedDensity q) (volume.restrict (Set.Ioc 0 (2*Real.pi))) :=
  ((density_continuous q hq).const_mul _).intervalIntegrable 0 (2*Real.pi) |>.1

theorem normalizedDensity_mass (q : ℝ) (hq : |q| < 1) :
    (∫ θ in Set.Ioc 0 (2*Real.pi), normalizedDensity q θ) = 1 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  simp only [normalizedDensity]
  rw [intervalIntegral.integral_const_mul]
  exact density_mass q hq

theorem law_probability (q : ℝ) (hq : |q| < 1) : IsProbabilityMeasure (law q) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (normalizedDensity_integrable q hq)
      (Filter.Eventually.of_forall (fun θ => by
        dsimp [normalizedDensity]
        positivity [density_positive q hq θ])), normalizedDensity_mass q hq]
  simp

theorem integral_law (q : ℝ) (hq : |q| < 1) (f : ℝ → ℂ) :
    (∫ θ, f θ ∂law q) =
      (2*Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2*Real.pi, density q θ • f θ := by
  rw [law, integral_withDensity_eq_integral_toReal_smul]
  · have hp : ∀ θ, 0 ≤ normalizedDensity q θ := fun θ => by
      dsimp [normalizedDensity]
      positivity [density_positive q hq θ]
    simp only [ENNReal.toReal_ofReal (hp _)]
    rw [← intervalIntegral.integral_of_le (by positivity)]
    simp only [normalizedDensity, mul_smul]
    exact intervalIntegral.integral_smul _ _
  · exact (ENNReal.measurable_ofReal.comp
      ((density_continuous q hq).const_mul _).measurable)
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem law_moment_nat (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    (∫ θ, (circleMap (0:ℂ) 1 θ)^n ∂law q) = (q:ℂ)^n := by
  rw [integral_law q hq]
  exact poisson_moment_nat q hq n

theorem law_moment_conj_nat (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    (∫ θ, starRingEnd ℂ ((circleMap (0:ℂ) 1 θ)^n) ∂law q) = (q:ℂ)^n := by
  rw [integral_conj, law_moment_nat q hq]
  simp

theorem stationary_positive_mode (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    -(n+1:ℂ)*(q:ℂ)^(n+1) +
      ((2*q/(1-q^2):ℝ):ℂ)*(n+1)/2*((q:ℂ)^n-(q:ℂ)^(n+2)) = 0 := by
  have hd : (1-q^2:ℝ) ≠ 0 := by
    have ha := abs_lt.mp hq
    nlinarith
  have hc : (1-(q:ℂ)^2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  simp only [pow_succ]
  ring

theorem law_mode_integrable (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    Integrable (fun θ => (circleMap (0:ℂ) 1 θ)^n) (law q) := by
  let := law_probability q hq
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun θ => by simp)

theorem integrated_positive_mode (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    (∫ θ, (-(n+1:ℂ)*(circleMap (0:ℂ) 1 θ)^(n+1) +
      ((2*q/(1-q^2):ℝ):ℂ)*(n+1)/2 *
        ((circleMap (0:ℂ) 1 θ)^n-(circleMap (0:ℂ) 1 θ)^(n+2))) ∂law q) = 0 := by
  have h1 : Integrable (fun θ => -(n+1:ℂ)*(circleMap (0:ℂ) 1 θ)^(n+1)) (law q) :=
    (law_mode_integrable q hq (n+1)).const_mul _
  have h2 : Integrable (fun θ => ((2*q/(1-q^2):ℝ):ℂ)*(n+1)/2 *
      ((circleMap (0:ℂ) 1 θ)^n-(circleMap (0:ℂ) 1 θ)^(n+2))) (law q) :=
    ((law_mode_integrable q hq n).sub (law_mode_integrable q hq (n+2))).const_mul _
  rw [integral_add h1 h2]
  rw [integral_const_mul, integral_const_mul,
    integral_sub (law_mode_integrable q hq n) (law_mode_integrable q hq (n+2))]
  simp only [law_moment_nat q hq]
  exact stationary_positive_mode q hq n

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteStableGamma.Core
open CauchySineDrift BrownianEnergyRepair.Torus

theorem axis_character_nat (n : ℕ) (θ : ℝ) :
    character (axisWave n) ![θ,0,0] = (circleMap (0:ℂ) 1 θ)^n := by
  simp only [character, phase, axisWave, Fin.sum_univ_three]
  simp [circleMap, ← Complex.exp_nat_mul, mul_comm, mul_assoc]

theorem axis_shift (n : ℤ) :
    axisWave n - unitWave = axisWave (n-1) ∧
    axisWave n + unitWave = axisWave (n+1) := by
  constructor <;> ext j <;> fin_cases j <;> simp [axisWave, unitWave]

theorem generator_positive_mode (r : ℝ) (n : ℕ) (θ : ℝ) :
    synthesis ![θ,0,0]
      (generator (stableSymbol 1) (AddMonoidAlgebra.single (axisWave (n+1)) 1) +
       (r:ℂ) • transport (AddMonoidAlgebra.single (axisWave (n+1)) 1)) =
    -(n+1:ℂ)*(circleMap (0:ℂ) 1 θ)^(n+1) +
      (r:ℂ)*(n+1)/2 *
       ((circleMap (0:ℂ) 1 θ)^n-(circleMap (0:ℂ) 1 θ)^(n+2)) := by
  rw [generator_single, transport_single, (axis_shift (n+1)).1, (axis_shift (n+1)).2]
  simp only [map_add, map_smul, map_sub, synthesis_single]
  simp [stableSymbol, axisWave, ← axis_character_nat, smul_eq_mul,
    abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)]
  ring

theorem actual_positive_mode_balance (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    (∫ θ, synthesis ![θ,0,0]
      (generator (stableSymbol 1) (AddMonoidAlgebra.single (axisWave (n+1)) 1) +
       ((2*q/(1-q^2):ℝ):ℂ) • transport
        (AddMonoidAlgebra.single (axisWave (n+1)) 1)) ∂law q) = 0 := by
  simp_rw [generator_positive_mode]
  exact integrated_positive_mode q hq n

open FiniteFourierReality

theorem cauchy_generator_reflection (f : Fourier) :
    reflection (generator (stableSymbol 1) f) =
      generator (stableSymbol 1) (reflection f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single k c =>
    simp [generator_single, reflection_single, stableSymbol]

theorem real_drift_reflection (r : ℝ) (f : Fourier) :
    reflection (generator (stableSymbol 1) f + r • transport f) =
      generator (stableSymbol 1) (reflection f) + r • transport (reflection f) := by
  rw [map_add, map_smul, cauchy_generator_reflection, transport_reflection]

theorem complex_real_smul (r : ℝ) (f : Fourier) : (r:ℂ) • f = r • f := by
  ext k
  simp [Complex.real_smul]

theorem actual_reflected_mode_balance (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    (∫ θ, synthesis ![θ,0,0]
      (generator (stableSymbol 1)
        (reflection (AddMonoidAlgebra.single (axisWave (n+1)) 1)) +
       ((2*q/(1-q^2):ℝ):ℂ) • transport
        (reflection (AddMonoidAlgebra.single (axisWave (n+1)) 1))) ∂law q) = 0 := by
  simp_rw [complex_real_smul, ← real_drift_reflection, synthesis_reflection]
  rw [integral_conj]
  have h := actual_positive_mode_balance q hq n
  simp_rw [complex_real_smul] at h
  rw [h]
  simp

theorem actual_integer_mode_balance (q : ℝ) (hq : |q| < 1) (n : ℤ) :
    (∫ θ, synthesis ![θ,0,0]
      (generator (stableSymbol 1) (AddMonoidAlgebra.single (axisWave n) 1) +
       ((2*q/(1-q^2):ℝ):ℂ) • transport
        (AddMonoidAlgebra.single (axisWave n) 1)) ∂law q) = 0 := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => simp [generator_single, transport_single, stableSymbol, axisWave]
    | succ n => exact actual_positive_mode_balance q hq n
  | negSucc n =>
    have he : -(axisWave ((n:ℤ)+1)) = axisWave (Int.negSucc n) := by
      ext j
      simp only [Pi.neg_apply, axisWave, Int.negSucc_eq]
      split_ifs <;> omega
    simpa only [reflection_single, map_one, he] using actual_reflected_mode_balance q hq n

theorem synthesis_law_integrable (q : ℝ) (hq : |q| < 1) (f : Fourier) :
    Integrable (fun θ => synthesis ![θ,0,0] f) (law q) := by
  let := law_probability q hq
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | single k c =>
    simp only [synthesis_single]
    apply Integrable.of_bound
      (((character_continuous k).comp (by fun_prop)).const_mul c).aestronglyMeasurable ‖c‖
    exact Filter.Eventually.of_forall (fun θ => by
      simp [character, Complex.norm_exp])

theorem transport_complex_smul (c : ℂ) (f : Fourier) :
    transport (c • f) = c • transport f := by
  simp [transport]

theorem actual_integer_coefficient_balance (q : ℝ) (hq : |q| < 1)
    (n : ℤ) (c : ℂ) :
    (∫ θ, synthesis ![θ,0,0]
      (generator (stableSymbol 1) (AddMonoidAlgebra.single (axisWave n) c) +
       ((2*q/(1-q^2):ℝ):ℂ) • transport
        (AddMonoidAlgebra.single (axisWave n) c)) ∂law q) = 0 := by
  have he : (AddMonoidAlgebra.single (axisWave n) c : Fourier) =
      c • AddMonoidAlgebra.single (axisWave n) 1 := by simp
  rw [he, map_smul, transport_complex_smul, smul_comm _ c, ← smul_add]
  simp only [map_smul]
  rw [integral_smul, actual_integer_mode_balance q hq]
  simp

theorem actual_finite_core_balance (q : ℝ) (hq : |q| < 1)
    {ι : Type*} (s : Finset ι) (n : ι → ℤ) (c : ι → ℂ) :
    (∫ θ, synthesis ![θ,0,0]
      (generator (stableSymbol 1) (∑ i ∈ s, AddMonoidAlgebra.single (axisWave (n i)) (c i)) +
       ((2*q/(1-q^2):ℝ):ℂ) • transport
        (∑ i ∈ s, AddMonoidAlgebra.single (axisWave (n i)) (c i))) ∂law q) = 0 := by
  have ht : ∀ f : ι → Fourier, transport (∑ i ∈ s, f i) = ∑ i ∈ s, transport (f i) := by
    intro f
    simp [transport, Finset.mul_sum]
  rw [map_sum, ht, Finset.smul_sum, ← Finset.sum_add_distrib]
  simp only [map_sum]
  rw [integral_finsetSum s (fun i hi => synthesis_law_integrable q hq _)]
  simp only [actual_integer_coefficient_balance q hq, Finset.sum_const_zero]

end OperatorDerivativeRewrite.Foundation.CauchyPoissonCoreInvariant
