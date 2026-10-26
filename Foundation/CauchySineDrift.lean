import Foundation.FiniteStableGamma

/-! Exact finite Cauchy Gamma correction for real sine-drift amplitude.
No completed generator, invariant-measure or spectral-domain claim is made. -/
namespace OperatorDerivativeRewrite.Foundation.CauchySineDrift

def twiceKernel (n m : ℤ) : ℤ := |n| + |m| - |m-n|

theorem drift_lower_coefficient (n m : ℤ) :
    (m-n) * twiceKernel n m + n * twiceKernel (n+1) m -
      m * twiceKernel n (m-1) = twiceKernel n m := by
  unfold twiceKernel
  have habs (z : ℤ) : |z| = if 0 ≤ z then z else -z := by
    split_ifs with h
    · exact abs_of_nonneg h
    · exact abs_of_neg (lt_of_not_ge h)
  simp only [habs]
  split_ifs <;> first | omega | nlinarith

theorem twiceKernel_neg (n m : ℤ) : twiceKernel (-n) (-m) = twiceKernel n m := by
  simp [twiceKernel, abs_sub_comm]
  congr 1
  ring

theorem drift_upper_coefficient (n m : ℤ) :
    -(m-n) * twiceKernel n m - n * twiceKernel (n-1) m +
      m * twiceKernel n (m+1) = twiceKernel n m := by
  have h := drift_lower_coefficient (-n) (-m)
  rw [show -n+1 = -(n-1) by ring, show -m-1 = -(m+1) by ring] at h
  simp only [twiceKernel_neg] at h
  nlinarith

open OperatorDerivativeRewrite.Foundation FiniteFourierDifferentialTrace
open FiniteStableGamma.Core

theorem cauchy_kernel_twice (k l : Wave) :
    kernel (stableSymbol 1) k l = (twiceKernel (k 0) (l 0) : ℝ)/2 := by
  simp [kernel, stableSymbol, twiceKernel, Pi.sub_apply, Int.cast_sub, Int.cast_abs]

noncomputable def unitWave : Wave := ![1,0,0]

/-- The actual finite Fourier transport by minus sine in coordinate zero. -/
noncomputable def transport (f : Fourier) : Fourier :=
  ((Complex.I/2) • (AddMonoidAlgebra.single unitWave 1 -
    AddMonoidAlgebra.single (-unitWave) 1)) * dLinear 0 f

theorem transport_product (f g : Fourier) :
    transport (f*g) = f * transport g + g * transport f := by
  unfold transport
  rw [d_mul]
  ring

theorem transport_single (k : Wave) (c : ℂ) :
    transport (AddMonoidAlgebra.single k c) =
      AddMonoidAlgebra.single (k-unitWave) ((k 0 : ℂ)/2*c) -
      AddMonoidAlgebra.single (k+unitWave) ((k 0 : ℂ)/2*c) := by
  simp only [transport, d_single, weight, sub_mul,
    AddMonoidAlgebra.single_mul_single, smul_sub, AddMonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]
  have hc : (Complex.I/2) * (Complex.I*(k 0 : ℂ)*c) = -((k 0 : ℂ)/2*c) := by
    calc
      _ = (Complex.I*Complex.I) * ((k 0 : ℂ)/2*c) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hc, add_comm unitWave k, show -unitWave+k = k-unitWave by abel]
  simp
  abel





theorem transport_synthesis (f : Fourier) (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x (transport f) =
      -(Real.sin (x 0) : ℂ) * FiniteFourierSynthesis.synthesis x (dLinear 0 f) := by
  open FiniteFourierSynthesis in
    have hp : character unitWave x = Complex.exp ((x 0 : ℂ)*Complex.I) := by
      simp [character, phase, unitWave, Fin.sum_univ_three, mul_comm]
  open FiniteFourierSynthesis in
    have hm : character (-unitWave) x = Complex.exp (-(x 0 : ℂ)*Complex.I) := by
      simp [character, phase, unitWave,
        Fin.sum_univ_three, mul_comm]
  simp only [transport, FiniteFourierSynthesis.synthesis_mul, map_smul, map_sub,
    FiniteFourierSynthesis.synthesis_single, one_mul, smul_eq_mul]
  rw [hp, hm, Complex.ofReal_sin, Complex.sin]
  ring

open FiniteFourierReality

theorem transport_add (f g : Fourier) : transport (f+g) = transport f+transport g := by
  simp [transport, mul_add]

theorem transport_reflection (f : Fourier) :
    reflection (transport f) = transport (reflection f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [transport]
  | add f g hf hg => simp [transport_add, hf, hg]
  | single k c =>
    simp only [transport_single, map_sub, reflection_single]
    have h₁ : -(k-unitWave) = -k+unitWave := by abel
    have h₂ : -(k+unitWave) = -k-unitWave := by abel
    rw [h₁, h₂]
    simp only [map_mul, map_div₀, map_intCast, map_ofNat, Pi.neg_apply,
      Int.cast_neg, neg_div, neg_mul, AddMonoidAlgebra.single_neg]
    abel

theorem transport_gamma_zero (f g : Fourier) :
    transport (reflection f*g) - reflection (transport f)*g -
      reflection f*transport g = 0 := by
  rw [transport_product, transport_reflection]
  ring

/-- First Gamma form for an explicitly supplied operator on the finite core. -/
noncomputable def firstGamma (L : Fourier → Fourier) (f g : Fourier) : Fourier :=
   (1/2 : ℂ) • (L (reflection f*g) - reflection (L f)*g - reflection f*L g)

theorem firstGamma_transport_invariant (L : Fourier → Fourier) (f g : Fourier) :
     firstGamma (fun h => L h + transport h) f g = firstGamma L f g := by
   unfold firstGamma
   simp only [map_add, add_mul, mul_add]
   have ht := transport_gamma_zero f g
   congr 1
   linear_combination ht

theorem firstGamma_generator (a : Wave → ℝ) (f g : Fourier) :
     firstGamma (generator a) f g = gammaIter a 1 f g := by
   rfl

theorem drift_firstGamma (a : Wave → ℝ) (f g : Fourier) :
     firstGamma (fun h => generator a h + transport h) f g = gammaIter a 1 f g := by
   rw [firstGamma_transport_invariant, firstGamma_generator]

noncomputable def secondGamma (L : Fourier → Fourier) (f g : Fourier) : Fourier :=
   (1/2 : ℂ) • (L (firstGamma L f g) - firstGamma L (L f) g - firstGamma L f (L g))

theorem drift_secondGamma_correction (a : Wave → ℝ) (f g : Fourier) :
     secondGamma (fun h => generator a h + transport h) f g =
       gammaIter a 2 f g + (1/2 : ℂ) •
         (transport (gammaIter a 1 f g) - gammaIter a 1 (transport f) g -
           gammaIter a 1 f (transport g)) := by
   unfold secondGamma
   simp only [drift_firstGamma, gammaIter_add_left, gammaIter_add_right]
   rw [show gammaIter a 2 f g = (1/2 : ℂ) •
     (generator a (gammaIter a 1 f g) - gammaIter a 1 (generator a f) g -
       gammaIter a 1 f (generator a g)) from rfl]
   module

theorem gamma_sub_left (a : Wave → ℝ) (n : ℕ) (f h g : Fourier) :
    gammaIter a n (f-h) g = gammaIter a n f g - gammaIter a n h g := by
  have he := gammaIter_add_left a n (f-h) h g
  rw [sub_add_cancel] at he
  exact eq_sub_of_add_eq he.symm

theorem gamma_sub_right (a : Wave → ℝ) (n : ℕ) (f g h : Fourier) :
    gammaIter a n f (g-h) = gammaIter a n f g - gammaIter a n f h := by
  have he := gammaIter_add_right a n f (g-h) h
  rw [sub_add_cancel] at he
  exact eq_sub_of_add_eq he.symm

theorem kernel_lower (k l : Wave) :
    ((l 0 : ℂ)-(k 0 : ℂ)) * (kernel (stableSymbol 1) k l : ℂ) +
      (k 0 : ℂ) * (kernel (stableSymbol 1) (k+unitWave) l : ℂ) -
      (l 0 : ℂ) * (kernel (stableSymbol 1) k (l-unitWave) : ℂ) =
        (kernel (stableSymbol 1) k l : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (drift_lower_coefficient (k 0) (l 0))
  push_cast at h
  simp only [cauchy_kernel_twice, Pi.add_apply, Pi.sub_apply, unitWave,
    Matrix.cons_val_zero, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  linear_combination h / 2

theorem kernel_upper (k l : Wave) :
    -((l 0 : ℂ)-(k 0 : ℂ)) * (kernel (stableSymbol 1) k l : ℂ) -
      (k 0 : ℂ) * (kernel (stableSymbol 1) (k-unitWave) l : ℂ) +
      (l 0 : ℂ) * (kernel (stableSymbol 1) k (l+unitWave) : ℂ) =
        (kernel (stableSymbol 1) k l : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (drift_upper_coefficient (k 0) (l 0))
  push_cast at h
  simp only [cauchy_kernel_twice, Pi.add_apply, Pi.sub_apply, unitWave,
    Matrix.cons_val_zero, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  linear_combination h / 2

open scoped ComplexConjugate

theorem drift_bracket_single (k l : Wave) (c d : ℂ) :
    transport (gammaIter (stableSymbol 1) 1 (AddMonoidAlgebra.single k c)
        (AddMonoidAlgebra.single l d)) -
      gammaIter (stableSymbol 1) 1 (transport (AddMonoidAlgebra.single k c))
        (AddMonoidAlgebra.single l d) -
      gammaIter (stableSymbol 1) 1 (AddMonoidAlgebra.single k c)
        (transport (AddMonoidAlgebra.single l d)) =
      (1/2 : ℂ) • (AddMonoidAlgebra.single (l-k-unitWave)
        ((kernel (stableSymbol 1) k l : ℂ)*conj c*d) +
        AddMonoidAlgebra.single (l-k+unitWave)
        ((kernel (stableSymbol 1) k l : ℂ)*conj c*d)) := by
  classical
  simp only [transport_single, gamma_sub_left, gamma_sub_right, gammaIter_single,
    pow_one, transport_single, map_mul, map_div₀, map_intCast, map_ofNat]
  rw [show l-(k-unitWave) = l-k+unitWave by abel,
    show l-(k+unitWave) = l-k-unitWave by abel,
    show l-unitWave-k = l-k-unitWave by abel,
    show l+unitWave-k = l-k+unitWave by abel]
  ext w
  by_cases hm : l-k-unitWave = w <;> by_cases hp : l-k+unitWave = w <;>
    simp [hm, hp, Pi.sub_apply, Int.cast_sub] <;>
    first
    | linear_combination (conj c*d/2) * kernel_lower k l
    | linear_combination (conj c*d/2) * kernel_upper k l
    | linear_combination (conj c*d/2) * (kernel_lower k l + kernel_upper k l)

noncomputable def cosineMultiplier : Fourier :=
  (1/2 : ℂ) • (AddMonoidAlgebra.single unitWave 1 + AddMonoidAlgebra.single (-unitWave) 1)

theorem drift_bracket (f g : Fourier) :
    transport (gammaIter (stableSymbol 1) 1 f g) -
      gammaIter (stableSymbol 1) 1 (transport f) g -
      gammaIter (stableSymbol 1) 1 f (transport g) =
        cosineMultiplier * gammaIter (stableSymbol 1) 1 f g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [gammaIter_zero_left, transport]
  | add f h hf hh =>
    simp only [gammaIter_add_left, transport_add, mul_add]
    linear_combination hf + hh
  | single k c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp [gammaIter_zero_right, transport]
    | add g h hg hh =>
      simp only [gammaIter_add_right, transport_add, mul_add]
      linear_combination hg + hh
    | single l d =>
      rw [drift_bracket_single]
      simp only [cosineMultiplier, gammaIter_single, pow_one, smul_mul_assoc,
        add_mul, AddMonoidAlgebra.single_mul_single, one_mul]
      rw [show unitWave+(l-k) = l-k+unitWave by abel,
        show -unitWave+(l-k) = l-k-unitWave by abel]
      module

theorem cauchy_drift_scalar_shift (f g : Fourier) :
    secondGamma (fun h => generator (stableSymbol 1) h + transport h) f g =
      gammaIter (stableSymbol 1) 2 f g +
        (1/2 : ℂ) • (cosineMultiplier * gammaIter (stableSymbol 1) 1 f g) := by
  rw [drift_secondGamma_correction, drift_bracket]

theorem cosineMultiplier_synthesis (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x cosineMultiplier = (Real.cos (x 0) : ℂ) := by
  open FiniteFourierSynthesis in
    have hp : character unitWave x = Complex.exp ((x 0 : ℂ)*Complex.I) := by
      simp [character, phase, unitWave, Fin.sum_univ_three, mul_comm]
  open FiniteFourierSynthesis in
    have hm : character (-unitWave) x = Complex.exp (-(x 0 : ℂ)*Complex.I) := by
      simp [character, phase, unitWave, Fin.sum_univ_three, mul_comm]
  simp only [cosineMultiplier, map_smul, map_add,
    FiniteFourierSynthesis.synthesis_single, one_mul, smul_eq_mul]
  rw [hp, hm, Complex.ofReal_cos, Complex.cos]
  ring

theorem cauchy_drift_scalar_shift_synthesis (f g : Fourier)
    (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x
      (secondGamma (fun h => generator (stableSymbol 1) h + transport h) f g) =
    FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 2 f g) +
      ((Real.cos (x 0) : ℂ)/2) *
        FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 1 f g) := by
  rw [cauchy_drift_scalar_shift]
  simp only [map_add, map_smul, FiniteFourierSynthesis.synthesis_mul,
    cosineMultiplier_synthesis, smul_eq_mul]
  ring

theorem firstGamma_scaled_transport (r : ℝ) (L : Fourier → Fourier) (f g : Fourier) :
    firstGamma (fun h => L h + r • transport h) f g = firstGamma L f g := by
  unfold firstGamma
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  have ht := transport_gamma_zero f g
  have hr := congrArg (fun z : Fourier => r • z) ht
  simp only [smul_sub, smul_zero] at hr
  congr 1
  linear_combination hr

theorem gamma_real_smul_left (a : Wave → ℝ) (n : ℕ) (r : ℝ) (f g : Fourier) :
    gammaIter a n (r • f) g = r • gammaIter a n f g := by
  induction n generalizing f g with
  | zero => simp [gammaIter]
  | succ n ih =>
    simp only [gammaIter, ih, LinearMap.map_smul_of_tower, smul_sub]
    module

theorem gamma_real_smul_right (a : Wave → ℝ) (n : ℕ) (r : ℝ) (f g : Fourier) :
    gammaIter a n f (r • g) = r • gammaIter a n f g := by
  induction n generalizing f g with
  | zero => simp [gammaIter]
  | succ n ih =>
    simp only [gammaIter, ih, LinearMap.map_smul_of_tower, smul_sub]
    module

theorem cauchy_scaled_drift_scalar_shift (r : ℝ) (f g : Fourier) :
    secondGamma (fun h => generator (stableSymbol 1) h + r • transport h) f g =
      gammaIter (stableSymbol 1) 2 f g +
        r • ((1/2 : ℂ) • (cosineMultiplier * gammaIter (stableSymbol 1) 1 f g)) := by
  unfold secondGamma
  simp only [firstGamma_scaled_transport, firstGamma_generator,
    gammaIter_add_left, gammaIter_add_right, gamma_real_smul_left, gamma_real_smul_right]
  rw [show gammaIter (stableSymbol 1) 2 f g = (1/2 : ℂ) •
    (generator (stableSymbol 1) (gammaIter (stableSymbol 1) 1 f g) -
      gammaIter (stableSymbol 1) 1 (generator (stableSymbol 1) f) g -
      gammaIter (stableSymbol 1) 1 f (generator (stableSymbol 1) g)) from rfl]
  rw [← drift_bracket]
  module

theorem cauchy_scaled_drift_scalar_shift_synthesis (r : ℝ) (f g : Fourier)
    (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x
      (secondGamma (fun h => generator (stableSymbol 1) h + r • transport h) f g) =
    FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 2 f g) +
      ((r * Real.cos (x 0) / 2 : ℝ) : ℂ) *
        FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 1 f g) := by
  rw [cauchy_scaled_drift_scalar_shift]
  simp only [map_add, LinearMap.map_smul_of_tower, map_smul,
    FiniteFourierSynthesis.synthesis_mul, cosineMultiplier_synthesis,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

end OperatorDerivativeRewrite.Foundation.CauchySineDrift


