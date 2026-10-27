import Foundation.CauchyDriftUniformObstruction
import Foundation.BrownianEnergyRepair
import Foundation.RealFiniteFourierAnalysis

/-! Actual circle drift IBP, signed-frequency free gap and centered-energy
Poincare repair for explicit finite real circle polynomials, 0 <= r < 2. -/
namespace OperatorDerivativeRewrite.Foundation.CauchyCenteredEnergy
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
open FiniteStableGamma.Core CauchySineDrift

noncomputable def sineDrift : Fourier :=
  (Complex.I/2) • (AddMonoidAlgebra.single unitWave 1 -
    AddMonoidAlgebra.single (-unitWave) 1)

theorem sineDrift_derivative : dLinear 0 sineDrift = -cosineMultiplier := by
  simp only [sineDrift, cosineMultiplier, map_sub, d_single, weight,
    Pi.neg_apply, Int.cast_neg, unitWave, Matrix.cons_val_zero, Int.cast_one,
    mul_one, mul_neg, smul_sub, smul_add, AddMonoidAlgebra.smul_single,
    smul_eq_mul]
  have h : Complex.I*(Complex.I/2) = -(1/2 : ℂ) := by
    calc _ = (Complex.I*Complex.I)/2 := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h, neg_mul, h]
  simp [AddMonoidAlgebra.single_neg]
  abel

theorem drift_product_derivative (f : Fourier) :
    dLinear 0 (sineDrift*(f*f)) = -(cosineMultiplier*(f*f)) +
      (2 : ℂ) • (f*transport f) := by
  rw [d_mul, d_mul, sineDrift_derivative]
  rw [show transport f = sineDrift*dLinear 0 f from rfl]
  simp only [two_smul]
  ring

theorem trace_drift_integration_by_parts (f : Fourier) :
    constantTrace (f*transport f) = (1/2 : ℂ)*constantTrace (cosineMultiplier*(f*f)) := by
  have h := constantTrace_derivative 0 (sineDrift*(f*f))
  rw [derivative_apply, drift_product_derivative, map_add, map_neg, map_smul,
    smul_eq_mul] at h
  linear_combination h/2

theorem trace_drift_energy (r : ℝ) (f : Fourier) :
    -constantTrace (f*(generator (stableSymbol 1) f+r • transport f)) =
      -constantTrace (f*generator (stableSymbol 1) f) -
        (r : ℂ)/2*constantTrace (cosineMultiplier*(f*f)) := by
  simp only [mul_add, mul_smul_comm, map_add, LinearMap.map_smul_of_tower,
    Complex.real_smul, trace_drift_integration_by_parts]
  ring

theorem cut_derivative_zero (f : Fourier) : cut 0 (dLinear 0 f) = 0 := by
  ext k
  simp only [cut_coeff, d_coeff]
  split_ifs with h
  · simp [weight, h]
  · rfl

theorem circle_drift_integration_by_parts (f : Fourier) (x : Space) :
    circleAverage 0 (fun y => synthesis y f*synthesis y (transport f)) x =
      (1/2 : ℂ) * circleAverage 0
        (fun y => (Real.cos (y 0) : ℂ)*(synthesis y f*synthesis y f)) x := by
  have h := congrArg (fun p : Fourier => synthesis x (cut 0 p))
    (drift_product_derivative f)
  rw [cut_derivative_zero] at h
  simp only [map_zero, map_add, map_neg, map_smul, smul_eq_mul] at h
  simp only [← cosineMultiplier_synthesis, ← synthesis_mul, circleAverage_synthesis]
  linear_combination -h/2

theorem circle_drift_energy (r : ℝ) (f : Fourier) (x : Space) :
    -circleAverage 0 (fun y => synthesis y f *
      synthesis y (generator (stableSymbol 1) f+r • transport f)) x =
    -circleAverage 0 (fun y => synthesis y f*synthesis y (generator (stableSymbol 1) f)) x -
      (r : ℂ)/2 * circleAverage 0
        (fun y => (Real.cos (y 0) : ℂ)*(synthesis y f*synthesis y f)) x := by
  have h := circle_drift_integration_by_parts f x
  simp only [← cosineMultiplier_synthesis, ← synthesis_mul, circleAverage_synthesis] at h ⊢
  simp only [mul_add, mul_smul_comm, map_add, LinearMap.map_smul_of_tower,
    Complex.real_smul]
  rw [h]
  ring

open BrownianEnergyRepair.Torus
open scoped ComplexConjugate

noncomputable def axisPolynomial {N : ℕ} (n : Fin N → ℤ) (c : Fin N → ℂ) : Fourier :=
  ∑ i, AddMonoidAlgebra.single (axisWave (n i)) (c i)

theorem axis_inner {N : ℕ} (n : Fin N → ℤ) (hn : Function.Injective n)
    (c d : Fin N → ℂ) (x : Space) :
    circleAverage 0 (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (axisPolynomial n d)) x = ∑ i, conj (c i)*d i := by
  classical
  have he : (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (axisPolynomial n d)) =
      fun y => synthesis y (gammaIter (stableSymbol 1) 0 (axisPolynomial n c) (axisPolynomial n d)) := by
    funext y
    simp [gammaIter, synthesis_mul, FiniteFourierReality.synthesis_reflection]
  rw [he, circleAverage_synthesis]
  unfold axisPolynomial
  rw [gammaIter_finite]
  simp [map_sum, cut_single, synthesis_single, axisWave, hn.eq_iff,
    sub_eq_zero, character_zero]

theorem axis_parseval {N : ℕ} (n : Fin N → ℤ) (hn : Function.Injective n)
    (c : Fin N → ℂ) (x : Space) :
    circleAverage 0 (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (axisPolynomial n c)) x = ∑ i, conj (c i)*c i := axis_inner n hn c c x

theorem axis_generator {N : ℕ} (n : Fin N → ℤ) (c : Fin N → ℂ) :
    generator (stableSymbol 1) (axisPolynomial n c) =
      axisPolynomial n (fun i => -(Complex.ofReal |(n i : ℝ)|)*c i) := by
  simp [axisPolynomial, map_sum, generator_single, stableSymbol, axisWave]

theorem axis_free_energy {N : ℕ} (n : Fin N → ℤ) (hn : Function.Injective n)
    (c : Fin N → ℂ) (x : Space) :
    -circleAverage 0 (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (generator (stableSymbol 1) (axisPolynomial n c))) x =
      ∑ i, Complex.ofReal |(n i : ℝ)| * (conj (c i)*c i) := by
  rw [axis_generator, axis_inner n hn]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem signed_coefficient_gap {N : ℕ} (n : Fin N → ℤ) (hn : ∀ i, n i ≠ 0)
    (c : Fin N → ℂ) :
    (∑ i, conj (c i)*c i).re ≤
      (∑ i, Complex.ofReal |(n i : ℝ)| * (conj (c i)*c i)).re := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  apply Finset.sum_le_sum
  intro i hi
  have h : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs (hn i)
  have hc : 0 ≤ (c i).re^2+(c i).im^2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hc]

theorem axis_free_gap {N : ℕ} (n : Fin N → ℤ) (hi : Function.Injective n)
    (hn : ∀ i, n i ≠ 0) (c : Fin N → ℂ) (x : Space) :
    (circleAverage 0 (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (axisPolynomial n c)) x).re ≤
    (-circleAverage 0 (fun y => conj (synthesis y (axisPolynomial n c)) *
      synthesis y (generator (stableSymbol 1) (axisPolynomial n c))) x).re := by
  rw [axis_parseval n hi, axis_free_energy n hi]
  exact signed_coefficient_gap n hn c

theorem circle_synthesis_re_mono (p q : Fourier) (x : Space)
    (h : ∀ y : Space, (synthesis y p).re ≤ (synthesis y q).re) :
    (circleAverage 0 (fun y => synthesis y p) x).re ≤
      (circleAverage 0 (fun y => synthesis y q) x).re := by
  have hp := coordinate_integrable p x 0
  have hq := coordinate_integrable q x 0
  have ep := Complex.reCLM.intervalIntegral_comp_comm hp
  have eq := Complex.reCLM.intervalIntegral_comp_comm hq
  simp only [Complex.reCLM_apply] at ep eq
  unfold circleAverage
  rw [RealFiniteFourierAnalysis.normalized_re, RealFiniteFourierAnalysis.normalized_re,
    ← ep, ← eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono (by positivity) ⟨hp.1.re, hp.2.re⟩ ⟨hq.1.re, hq.2.re⟩
  intro t
  exact h (Function.update x 0 t)

theorem circle_cosine_square_bound (f : Fourier) (hf : ∀ y : Space, (synthesis y f).im = 0)
    (x : Space) :
    (circleAverage 0 (fun y => (Real.cos (y 0) : ℂ)*
      (synthesis y f*synthesis y f)) x).re ≤
      (circleAverage 0 (fun y => synthesis y f*synthesis y f) x).re := by
  simp only [← cosineMultiplier_synthesis, ← synthesis_mul]
  apply circle_synthesis_re_mono
  intro y
  simp only [synthesis_mul, cosineMultiplier_synthesis, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, hf y, mul_zero, zero_mul, sub_zero]
  nlinarith [mul_nonneg (sub_nonneg.mpr (Real.cos_le_one (y 0))) (sq_nonneg (synthesis y f).re)]

theorem real_axis_drift_coercive {N : ℕ} (n : Fin N → ℤ) (hi : Function.Injective n)
    (hn : ∀ i, n i ≠ 0) (c : Fin N → ℂ)
    (hf : ∀ y : Space, (synthesis y (axisPolynomial n c)).im = 0)
    (r : ℝ) (hr : 0 ≤ r) (x : Space) :
    (1-r/2) * (circleAverage 0 (fun y => synthesis y (axisPolynomial n c) *
      synthesis y (axisPolynomial n c)) x).re ≤
      (-circleAverage 0 (fun y => synthesis y (axisPolynomial n c) *
        synthesis y (generator (stableSymbol 1) (axisPolynomial n c) +
          r • transport (axisPolynomial n c))) x).re := by
  have hc (y : Space) : conj (synthesis y (axisPolynomial n c)) =
      synthesis y (axisPolynomial n c) := by
    apply Complex.ext <;> simp [hf y]
  have hg := axis_free_gap n hi hn c x
  simp only [hc] at hg
  have hb := circle_cosine_square_bound (axisPolynomial n c) hf x
  have he := congrArg Complex.re (circle_drift_energy r (axisPolynomial n c) x)
  rw [show (r : ℂ)/2 = Complex.ofReal (r/2) by push_cast; rfl] at he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he
  have hs := mul_le_mul_of_nonneg_left hb (show 0 ≤ r/2 by positivity)
  nlinarith

theorem axis_circle_mean_zero {N : ℕ} (n : Fin N → ℤ) (hn : ∀ i, n i ≠ 0)
    (c : Fin N → ℂ) (x : Space) :
    circleAverage 0 (fun y => synthesis y (axisPolynomial n c)) x = 0 := by
  rw [circleAverage_synthesis]
  simp [axisPolynomial, map_sum, cut_single, axisWave, hn]

theorem real_axis_poincare {N : ℕ} (n : Fin N → ℤ) (hi : Function.Injective n)
    (hn : ∀ i, n i ≠ 0) (c : Fin N → ℂ)
    (hf : ∀ y : Space, (synthesis y (axisPolynomial n c)).im = 0)
    (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2) (x : Space) :
    (circleAverage 0 (fun y => synthesis y (axisPolynomial n c) *
      synthesis y (axisPolynomial n c)) x).re -
      (circleAverage 0 (fun y => synthesis y (axisPolynomial n c)) x).re^2 ≤
      (-circleAverage 0 (fun y => synthesis y (axisPolynomial n c) *
        synthesis y (generator (stableSymbol 1) (axisPolynomial n c) +
          r • transport (axisPolynomial n c))) x).re / (1-r/2) := by
  rw [axis_circle_mean_zero n hn]
  simp only [Complex.zero_re, zero_pow (by decide : 2 ≠ 0), sub_zero]
  apply (le_div_iff₀ (by linarith : 0 < 1-r/2)).mpr
  simpa only [mul_comm] using real_axis_drift_coercive n hi hn c hf r hr x

theorem circle_shift_mean (f : Fourier) (a : ℂ) (x : Space)
    (hf : circleAverage 0 (fun y => synthesis y f) x = 0) :
    circleAverage 0 (fun y => synthesis y (a • (1 : Fourier)+f)) x = a := by
  rw [circleAverage_synthesis] at hf ⊢
  simp only [map_add, map_smul, hf, smul_eq_mul, add_zero]
  simp [AddMonoidAlgebra.one_def, cut_single, synthesis_single, character_zero]

theorem circle_shift_square (f : Fourier) (a : ℂ) (x : Space)
    (hf : circleAverage 0 (fun y => synthesis y f) x = 0) :
    circleAverage 0 (fun y => synthesis y (a • (1 : Fourier)+f) *
      synthesis y (a • (1 : Fourier)+f)) x =
        a*a + circleAverage 0 (fun y => synthesis y f*synthesis y f) x := by
  rw [circleAverage_synthesis] at hf
  have hone : synthesis x (cut 0 (1 : Fourier)) = 1 := by
    simp [AddMonoidAlgebra.one_def, cut_single, synthesis_single, character_zero]
  simp only [← synthesis_mul, circleAverage_synthesis]
  simp only [add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_add, map_smul,
    hone, hf, smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]

noncomputable def circleCenter (x : Space) (f : Fourier) : Fourier :=
  f - (circleAverage 0 (fun y => synthesis y f) x) • (1 : Fourier)

theorem circleCenter_shift (f : Fourier) (a : ℂ) (x : Space)
    (hf : circleAverage 0 (fun y => synthesis y f) x = 0) :
    circleCenter x (a • (1 : Fourier)+f) = f := by
  unfold circleCenter
  rw [circle_shift_mean f a x hf]
  abel

theorem centered_axis_poincare {N : ℕ} (n : Fin N → ℤ) (hi : Function.Injective n)
    (hn : ∀ i, n i ≠ 0) (c : Fin N → ℂ)
    (hf : ∀ y : Space, (synthesis y (axisPolynomial n c)).im = 0)
    (a r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2) (x : Space) :
    let f := (a : ℂ) • (1 : Fourier)+axisPolynomial n c
    (circleAverage 0 (fun y => synthesis y f*synthesis y f) x).re -
      (circleAverage 0 (fun y => synthesis y f) x).re^2 ≤
      (-circleAverage 0 (fun y => synthesis y (circleCenter x f) *
        synthesis y (generator (stableSymbol 1) (circleCenter x f) +
          r • transport (circleCenter x f))) x).re / (1-r/2) := by
  dsimp only
  have hm := axis_circle_mean_zero n hn c x
  rw [circleCenter_shift _ _ _ hm, circle_shift_square _ _ _ hm, circle_shift_mean _ _ _ hm]
  have h := real_axis_poincare n hi hn c hf r hr hr2 x
  rw [hm] at h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re, zero_pow (by decide : 2 ≠ 0)] at h ⊢
  nlinarith

end OperatorDerivativeRewrite.Foundation.CauchyCenteredEnergy
