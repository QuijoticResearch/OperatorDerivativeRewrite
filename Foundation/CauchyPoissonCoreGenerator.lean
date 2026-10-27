import Foundation.CauchyPoissonConcentration
import Foundation.ContractionTangentDissipativity
import Mathlib.Analysis.Calculus.Deriv.Star
/-! Actual supremum-norm right generator derivatives on finite circle Fourier
combinations. The orbit uses max(t,0) only to define a real-time function; every
derivative here is from positive times. No closed-domain characterization,
graph-core density or resolvent surjectivity is asserted. -/
noncomputable section
open Complex MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonCoreGenerator
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonFeller CauchyPoissonConcentration

def coordinate : C(Circle,ℂ) := ⟨fun z => (z:ℂ), by fun_prop⟩

def trajectory (q : ℝ) (hq : |q| < 1) (t : ℝ) : C(Circle,ℂ) :=
  ⟨fun z => evolution q (max t 0) z, evolution_circle_continuous q _ hq (le_max_right _ _)⟩

def quotientFactor (q : ℝ) (hq : |q| < 1) (t : ℝ) : C(Circle,ℂ) :=
  ⟨fun z => ((q:ℂ) - (1-(q:ℂ)^2)*(z:ℂ) - (q:ℂ)*(z:ℂ)^2) /
    denominator q (decay q (max t 0)) z, by
    apply Continuous.div (by fun_prop) (by unfold denominator; fun_prop)
    intro z
    exact denominator_ne_zero q _ hq (decay_range q _ hq (le_max_right _ _)).1
      (decay_range q _ hq (le_max_right _ _)).2 z (by simp)⟩

theorem quotientFactor_continuous (q : ℝ) (hq : |q| < 1) : Continuous (quotientFactor q hq) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.div (by fun_prop) (by unfold denominator decay; fun_prop)
  intro p
  exact denominator_ne_zero q _ hq (decay_range q _ hq (le_max_right _ _)).1
    (decay_range q _ hq (le_max_right _ _)).2 p.2 (by simp)

theorem trajectory_difference (q : ℝ) (hq : |q| < 1) (t : ℝ) (ht : 0 ≤ t) :
    trajectory q hq t-coordinate = (1-decay q t) • quotientFactor q hq t := by
  ext z
  change evolution q (max t 0) z - (z:ℂ) =
    (1-decay q t) • (((q:ℂ)-(1-(q:ℂ)^2)*(z:ℂ)-(q:ℂ)*(z:ℂ)^2) /
      denominator q (decay q (max t 0)) z)
  rw [max_eq_left ht]
  have hd := denominator_ne_zero q _ hq (decay_range q t hq ht).1 (decay_range q t hq ht).2 z (by simp)
  unfold evolution flow
  rw [Complex.real_smul]
  push_cast
  field_simp
  simp only [numerator,denominator]
  ring

def velocity (q : ℝ) : C(Circle,ℂ) :=
  ⟨fun z => -(z:ℂ)+(q:ℂ)/(1-(q:ℂ)^2)*(1-(z:ℂ)^2), by fun_prop⟩

theorem factor_zero (q : ℝ) (hq : |q| < 1) : rate q • quotientFactor q hq 0 = velocity q := by
  ext z
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hd : (1-(q:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1-q^2 by linarith))
  have hp : (1+(q:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+q^2 by positivity))
  simp [quotientFactor,velocity,rate,decay,denominator,Complex.real_smul]
  push_cast
  field_simp
  <;> ring

theorem trajectory_tangent (q : ℝ) (hq : |q| < 1) :
    Tendsto (fun t : ℝ => t⁻¹ • (trajectory q hq t-coordinate))
      (𝓝[Set.Ioi 0] 0) (𝓝 (velocity q)) := by
  have hd : HasDerivAt (fun t : ℝ => 1-decay q t) (rate q) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).const_mul (-rate q)).exp).const_sub 1 using 1 <;> simp [decay]
  have hs : Tendsto (fun t : ℝ => t⁻¹ * (1-decay q t)) (𝓝[Set.Ioi 0] 0) (𝓝 (rate q)) := by
    simpa [decay] using hd.tendsto_slope_zero_right
  have hf : Tendsto (quotientFactor q hq) (𝓝[Set.Ioi 0] 0) (𝓝 (quotientFactor q hq 0)) :=
    (quotientFactor_continuous q hq).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh := hs.smul hf
  rw [factor_zero q hq] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [trajectory_difference q hq t ht.le,smul_smul]

theorem trajectory_zero (q : ℝ) (hq : |q| < 1) : trajectory q hq 0 = coordinate := by
  ext z
  change evolution q (max 0 0) z = (z:ℂ)
  simpa using evolution_zero q z

theorem trajectory_hasDerivWithinAt (q : ℝ) (hq : |q| < 1) :
    HasDerivWithinAt (trajectory q hq) (velocity q) (Set.Ioi 0) 0 := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  change Tendsto (fun t : ℝ => (t-0)⁻¹ • (trajectory q hq t-trajectory q hq 0)) _ _
  simpa only [sub_zero,trajectory_zero] using trajectory_tangent q hq

def orbit (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (t : ℝ) : C(Circle,ℂ) :=
  operator q (max t 0) hq (le_max_right _ _) f

theorem kernel_power (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (z : Circle) (n : ℕ) :
    (∫ w : Circle, (w:ℂ)^n ∂kernel q t z) = (evolution q t z)^n := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simp [kernel_zero,Kernel.id_apply,evolution_zero]
  · have hi := integral_kernel_formula q t hq h (coordinate^n) z
    change (∫ w : Circle, (w:ℂ)^n ∂kernel q t z) =
      ∫ θ in Set.Icc 0 (2*Real.pi), poleWeight (evolution q t z) θ • (Circle.exp θ : ℂ)^n at hi
    rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
    simp only [poleWeight,mul_smul,circle_exp_coe]
    rw [intervalIntegral.integral_smul]
    exact (differentiable_id.pow n).diffContOnCl.circleAverage_poissonKernel_smul
      (by simpa using evolution_strict_disk q t hq h z (by simp))

theorem orbit_power (q : ℝ) (hq : |q| < 1) (n : ℕ) (t : ℝ) :
    orbit q hq (coordinate^n) t = trajectory q hq t ^ n := by
  ext z
  exact kernel_power q _ hq (le_max_right _ _) z n

theorem orbit_star (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (t : ℝ) :
    orbit q hq (star f) t = star (orbit q hq f t) := by
  ext z
  exact integral_conj

def powerVelocity (q : ℝ) (n : ℕ) : C(Circle,ℂ) :=
  n * coordinate^(n-1) * velocity q

theorem power_hasDerivWithinAt (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    HasDerivWithinAt (orbit q hq (coordinate^n)) (powerVelocity q n) (Set.Ioi 0) 0 := by
  have he : orbit q hq (coordinate^n) = fun t => trajectory q hq t ^ n := funext (orbit_power q hq n)
  rw [he]
  simpa only [trajectory_zero,powerVelocity] using (trajectory_hasDerivWithinAt q hq).fun_pow n

theorem star_power_hasDerivWithinAt (q : ℝ) (hq : |q| < 1) (n : ℕ) :
    HasDerivWithinAt (orbit q hq (star (coordinate^n))) (star (powerVelocity q n)) (Set.Ioi 0) 0 := by
  have he : orbit q hq (star (coordinate^n)) = fun t => star (orbit q hq (coordinate^n) t) :=
    funext (orbit_star q hq _)
  rw [he]
  exact (power_hasDerivWithinAt q hq n).star

def coreValue (N : ℕ) (a b : Fin N → ℂ) : C(Circle,ℂ) :=
  ∑ n : Fin N, (a n • coordinate^(n:ℕ) + b n • star (coordinate^(n:ℕ)))

def coreGenerator (q : ℝ) (N : ℕ) (a b : Fin N → ℂ) : C(Circle,ℂ) :=
  ∑ n : Fin N, (a n • powerVelocity q n + b n • star (powerVelocity q n))

theorem core_hasDerivWithinAt (q : ℝ) (hq : |q| < 1) (N : ℕ) (a b : Fin N → ℂ) :
    HasDerivWithinAt (orbit q hq (coreValue N a b)) (coreGenerator q N a b) (Set.Ioi 0) 0 := by
  have he : orbit q hq (coreValue N a b) = fun t =>
      ∑ n : Fin N, (a n • orbit q hq (coordinate^(n:ℕ)) t + b n • orbit q hq (star (coordinate^(n:ℕ))) t) := by
    funext t
    simp only [orbit,coreValue,map_sum,map_add,map_smul]
  rw [he]
  convert HasDerivWithinAt.sum (u := Finset.univ) (fun (n : Fin N) _ =>
    ((power_hasDerivWithinAt q hq n).const_smul (a n)).add
      ((star_power_hasDerivWithinAt q hq n).const_smul (b n))) using 1
  · funext t
    simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply]
  · rfl

theorem orbit_zero (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) : orbit q hq f 0 = f := by
  simp [orbit,operator_zero]

theorem core_tangent (q : ℝ) (hq : |q| < 1) (N : ℕ) (a b : Fin N → ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (orbit q hq (coreValue N a b) t-coreValue N a b))
      (𝓝[Set.Ioi 0] 0) (𝓝 (coreGenerator q N a b)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp (core_hasDerivWithinAt q hq N a b)
  change Tendsto (fun t : ℝ => (t-0)⁻¹ • (orbit q hq (coreValue N a b) t-orbit q hq (coreValue N a b) 0)) _ _ at h
  simpa only [sub_zero,orbit_zero] using h

theorem orbit_contraction (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (t : ℝ) :
    ‖orbit q hq f t‖ ≤ ‖f‖ := by
  change ‖operator q (max t 0) hq (le_max_right _ _) f‖ ≤ ‖f‖
  calc
    _ ≤ ‖operator q (max t 0) hq (le_max_right _ _)‖ * ‖f‖ :=
      (operator q (max t 0) hq (le_max_right _ _)).le_opNorm f
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right (operator_contraction q _ hq (le_max_right _ _)) (norm_nonneg _)
    _ = _ := one_mul _

theorem core_resolvent_bound (q : ℝ) (hq : |q| < 1) (N : ℕ) (a b : Fin N → ℂ)
    (r : ℝ) (hr : 0 < r) :
    r*‖coreValue N a b‖ ≤ ‖r • coreValue N a b - coreGenerator q N a b‖ :=
  ContractionTangentDissipativity.norm_resolvent_bound (orbit q hq (coreValue N a b))
    _ _ (fun t _ => orbit_contraction q hq _ t) (core_tangent q hq N a b) r hr

theorem core_presentation_independent (q : ℝ) (hq : |q| < 1)
    (N M : ℕ) (a b : Fin N → ℂ) (c d : Fin M → ℂ)
    (h : coreValue N a b = coreValue M c d) :
    coreGenerator q N a b = coreGenerator q M c d := by
  have h1 := core_tangent q hq N a b
  have h2 := core_tangent q hq M c d
  rw [h] at h1
  exact tendsto_nhds_unique h1 h2

theorem positive_mode_matches_drift (q : ℝ) (n : ℕ) (θ : ℝ) :
    powerVelocity q (n+1) (Circle.exp θ) =
      FiniteFourierSynthesis.synthesis ![θ,0,0]
        (CauchyPoissonNonSymmetry.drift (2*q/(1-q^2))
          (AddMonoidAlgebra.single (BrownianEnergyRepair.Torus.axisWave (n+1)) 1)) := by
  simp only [powerVelocity,ContinuousMap.mul_apply,ContinuousMap.pow_apply,Nat.add_sub_cancel]
  change (((n+1:ℕ):ℂ)*(Circle.exp θ : ℂ)^n)*
    (-(Circle.exp θ : ℂ)+(q:ℂ)/(1-(q:ℂ)^2)*(1-(Circle.exp θ : ℂ)^2)) = _
  rw [circle_exp_coe]
  simp only [CauchyPoissonNonSymmetry.drift,CauchyPoissonCoreInvariant.generator_positive_mode]
  push_cast
  simp only [pow_succ]
  ring

end OperatorDerivativeRewrite.Foundation.CauchyPoissonCoreGenerator
