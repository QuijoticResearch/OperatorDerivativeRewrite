import Foundation.CauchyHigherDriftObstruction
/-! Exact single-harmonic Cauchy drift corrections on the finite Fourier core.
The positive-mode diagonal coefficient is n*min(n,r)/4 for n,r >= 0.
A shared pointwise scalar correction exists exactly for r=0 or r=1 among
nonnegative integer harmonics. No arbitrary-potential, real-only, completed
domain, new semigroup or curvature-bound classification is asserted. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.CauchyHarmonicDrift
open FiniteFourierDifferentialTrace FiniteFourierReality FiniteStableGamma.Core CauchySineDrift
open CauchyHigherDriftObstruction (wave mode wave_neg wave_sub synthesis_mode_zero)

def harmonic (r : ℤ) (f : Fourier) : Fourier :=
  ((Complex.I/2) • (mode r-mode (-r))) * dLinear 0 f

theorem harmonic_product (r : ℤ) (f g : Fourier) :
    (harmonic r) (f*g) = f * (harmonic r) g + g * (harmonic r) f := by
  unfold harmonic
  rw [d_mul]
  ring

theorem harmonic_general_single (r : ℤ) (k : Wave) (c : ℂ) :
    (harmonic r) (AddMonoidAlgebra.single k c) =
      AddMonoidAlgebra.single (k-(wave r)) ((k 0 : ℂ)/2*c) -
      AddMonoidAlgebra.single (k+(wave r)) ((k 0 : ℂ)/2*c) := by
  simp only [harmonic,mode,wave_neg, d_single, weight, sub_mul,
    AddMonoidAlgebra.single_mul_single, smul_sub, AddMonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]
  have hc : (Complex.I/2) * (Complex.I*(k 0 : ℂ)*c) = -((k 0 : ℂ)/2*c) := by
    calc
      _ = (Complex.I*Complex.I) * ((k 0 : ℂ)/2*c) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hc, add_comm (wave r) k, show -(wave r)+k = k-(wave r) by abel]
  simp
  abel

theorem harmonic_add (r : ℤ) (f g : Fourier) : (harmonic r) (f+g) = (harmonic r) f+(harmonic r) g := by
  simp [harmonic, mul_add]

theorem harmonic_reflection (r : ℤ) (f : Fourier) :
    reflection ((harmonic r) f) = (harmonic r) (reflection f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [harmonic]
  | add f g hf hg => simp [harmonic_add, hf, hg]
  | single k c =>
    simp only [harmonic_general_single, map_sub, reflection_single]
    have h₁ : -(k-(wave r)) = -k+(wave r) := by abel
    have h₂ : -(k+(wave r)) = -k-(wave r) := by abel
    rw [h₁, h₂]
    simp only [map_mul, map_div₀, map_intCast, map_ofNat, Pi.neg_apply,
      Int.cast_neg, neg_div, neg_mul, AddMonoidAlgebra.single_neg]
    abel

theorem harmonic_gamma_zero (r : ℤ) (f g : Fourier) :
    (harmonic r) (reflection f*g) - reflection ((harmonic r) f)*g -
      reflection f*(harmonic r) g = 0 := by
  rw [harmonic_product, harmonic_reflection]
  ring

theorem firstGamma_harmonic_invariant (r : ℤ) (L : Fourier → Fourier) (f g : Fourier) :
     firstGamma (fun h => L h + (harmonic r) h) f g = firstGamma L f g := by
   unfold firstGamma
   simp only [map_add, add_mul, mul_add]
   have ht := harmonic_gamma_zero r f g
   congr 1
   linear_combination ht

theorem wave_add (n m : ℤ) : wave n+wave m = wave (n+m) := by
  ext i; fin_cases i <;> simp [wave]

theorem action_axis (r n : ℤ) (c : ℂ) :
    harmonic r (AddMonoidAlgebra.single (wave n) c) =
      AddMonoidAlgebra.single (wave (n-r)) ((n:ℂ)/2*c) -
      AddMonoidAlgebra.single (wave (n+r)) ((n:ℂ)/2*c) := by
  rw [harmonic_general_single,wave_sub,wave_add]
  rfl

theorem kernel_axis (n m : ℤ) :
    (kernel (stableSymbol 1) (wave n) (wave m):ℂ) = (((|n|+|m|-|m-n|:ℤ):ℂ)/2) := by
  simp only [cauchy_kernel_twice,twiceKernel,wave,Matrix.cons_val_zero,
    Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ofNat]

theorem kernel_difference (n r : ℤ) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    kernel (stableSymbol 1) (wave (n+r)) (wave n) -
      kernel (stableSymbol 1) (wave (n-r)) (wave n) = ((min n r:ℤ):ℝ) := by
  simp only [cauchy_kernel_twice,twiceKernel,wave,Matrix.cons_val_zero]
  have he : |n+r|+|n|-|n-(n+r)| - (|n-r|+|n|-|n-(n-r)|) = 2*min n r := by
    rw [abs_of_nonneg (add_nonneg hn hr),abs_of_nonneg hn,
      show n-(n+r) = -r by omega,show n-(n-r)=r by omega,abs_neg,abs_of_nonneg hr]
    by_cases h : n ≤ r
    · rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_left h]; omega
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]; omega
  have hh : (((|n+r|+|n|-|n-(n+r)|):ℤ):ℝ) -
      (((|n-r|+|n|-|n-(n-r)|):ℤ):ℝ) = 2*((min n r:ℤ):ℝ) := by exact_mod_cast he
  linarith

def bracket (r : ℤ) (f g : Fourier) : Fourier :=
  harmonic r (gammaIter (stableSymbol 1) 1 f g) -
    gammaIter (stableSymbol 1) 1 (harmonic r f) g -
    gammaIter (stableSymbol 1) 1 f (harmonic r g)

theorem kernel_axis_symm (n m : ℤ) :
    kernel (stableSymbol 1) (wave n) (wave m) = kernel (stableSymbol 1) (wave m) (wave n) := by
  simp [cauchy_kernel_twice,twiceKernel,wave,abs_sub_comm,add_comm]

theorem diagonal_bracket (n r : ℤ) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    bracket r (mode n) (mode n) = ((n:ℂ)*(min n r:ℤ)/2) • (mode r+mode (-r)) := by
  have hk := congrArg (fun x : ℝ => (x:ℂ)) (kernel_difference n r hn hr)
  simp only [Complex.ofReal_sub,Complex.ofReal_intCast] at hk
  unfold bracket mode
  simp only [gammaIter_single,pow_one,action_axis,gamma_sub_left,gamma_sub_right,
    gammaIter_single,pow_one,wave_sub]
  rw [show n-n = 0 by omega]
  simp only [action_axis,Int.cast_zero,zero_div,zero_mul,AddMonoidAlgebra.single_zero,
    sub_self,zero_sub,map_mul,map_div₀,map_intCast,map_ofNat,map_one,mul_one]
  rw [show n-(n-r)=r by omega,show n-(n+r) = -r by omega,
    show n-r-n = -r by omega,show n+r-n = r by omega,
    kernel_axis_symm n (n-r),kernel_axis_symm n (n+r)]
  ext w
  by_cases h1 : wave r = w <;> by_cases h2 : wave (-r) = w <;>
    simp [h1,h2,AddMonoidAlgebra.coeff_single] <;>
    first | linear_combination (n:ℂ)/2*hk | linear_combination (n:ℂ)*hk | ring
theorem harmonic_synthesis (r : ℤ) (f : Fourier) (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x (harmonic r f) =
      -(Real.sin ((r:ℝ)*x 0):ℂ)*FiniteFourierSynthesis.synthesis x (dLinear 0 f) := by
  have hp : FiniteFourierSynthesis.character (wave r) x = Complex.exp (((r:ℝ)*x 0:ℝ)*Complex.I) := by
    simp [FiniteFourierSynthesis.character,FiniteFourierSynthesis.phase,wave,Fin.sum_univ_three,mul_comm]
  have hm : FiniteFourierSynthesis.character (wave (-r)) x = Complex.exp (-(((r:ℝ)*x 0:ℝ):ℂ)*Complex.I) := by
    simp [FiniteFourierSynthesis.character,FiniteFourierSynthesis.phase,wave,Fin.sum_univ_three,mul_comm]
  simp only [harmonic,mode,FiniteFourierSynthesis.synthesis_mul,map_smul,map_sub,
    FiniteFourierSynthesis.synthesis_single,one_mul,smul_eq_mul]
  rw [hp,hm,Complex.ofReal_sin,Complex.sin]
  ring

theorem second_correction (r : ℤ) (f g : Fourier) :
    secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) f g =
      gammaIter (stableSymbol 1) 2 f g + (1/2:ℂ) • bracket r f g := by
  unfold secondGamma
  simp only [firstGamma_harmonic_invariant,firstGamma_generator,gammaIter_add_left,gammaIter_add_right]
  change _ = (1/2:ℂ) •
    (generator (stableSymbol 1) (gammaIter (stableSymbol 1) 1 f g) -
     gammaIter (stableSymbol 1) 1 (generator (stableSymbol 1) f) g -
     gammaIter (stableSymbol 1) 1 f (generator (stableSymbol 1) g)) + _
  unfold bracket
  module

theorem diagonal_correction (n r : ℤ) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (mode n) (mode n) -
      gammaIter (stableSymbol 1) 2 (mode n) (mode n) =
        ((n:ℂ)*(min n r:ℤ)/4) • (mode r+mode (-r)) := by
  rw [second_correction,diagonal_bracket n r hn hr]
  module

theorem gamma_diagonal (n : ℤ) (hn : 0 ≤ n) :
    gammaIter (stableSymbol 1) 1 (mode n) (mode n) = (n:ℂ) • mode 0 := by
  simp only [mode,gammaIter_single,pow_one,wave_sub,kernel_axis,sub_self,
    abs_zero,sub_zero,abs_of_nonneg hn,map_one,mul_one,
    AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  congr 1
  · ext i; fin_cases i <;> simp [wave]
  · push_cast; ring

theorem correction_at_zero (n r : ℤ) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    FiniteFourierSynthesis.synthesis 0
      (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (mode n) (mode n) -
        gammaIter (stableSymbol 1) 2 (mode n) (mode n)) = (n:ℂ)*(min n r:ℤ)/2 := by
  rw [diagonal_correction n r hn hr]
  simp only [map_smul,map_add,synthesis_mode_zero,smul_eq_mul]
  ring

theorem no_positive_mode_scalar (r : ℤ) (hr : 1 < r) :
    ¬ ∃ a : ℂ, ∀ n : ℤ, 0 < n →
      FiniteFourierSynthesis.synthesis 0
        (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (mode n) (mode n) -
          gammaIter (stableSymbol 1) 2 (mode n) (mode n)) =
        a*FiniteFourierSynthesis.synthesis 0 (gammaIter (stableSymbol 1) 1 (mode n) (mode n)) := by
  rintro ⟨a,ha⟩
  have h1 := ha 1 (by omega)
  have h2 := ha r (by omega)
  rw [correction_at_zero 1 r (by omega) (by omega),gamma_diagonal 1 (by omega)] at h1
  rw [correction_at_zero r r (by omega) (by omega),gamma_diagonal r (by omega)] at h2
  norm_num [min_eq_left hr.le,map_smul,synthesis_mode_zero,smul_eq_mul] at h1 h2
  rw [← h1] at h2
  have hh := congrArg Complex.re h2
  norm_num [Complex.mul_re,Complex.div_re] at hh
  have hrreal : 1 < (r:ℝ) := by exact_mod_cast hr
  nlinarith

theorem no_pointwise_scalar (r : ℤ) (hr : 1 < r) :
    ¬ ∃ a : FiniteFourierSynthesis.Space → ℂ, ∀ f : Fourier, ∀ x,
      FiniteFourierSynthesis.synthesis x
        (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) f f -
          gammaIter (stableSymbol 1) 2 f f) =
        a x*FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 1 f f) := by
  rintro ⟨a,ha⟩
  exact no_positive_mode_scalar r hr ⟨a 0,fun n _ => ha (mode n) 0⟩
theorem harmonic_one (f : Fourier) : harmonic 1 f = transport f := by
  simp only [harmonic,mode,wave_neg]
  rfl

theorem scalar_iff (r : ℤ) (hr : 0 ≤ r) :
    (∃ a : FiniteFourierSynthesis.Space → ℂ, ∀ f : Fourier, ∀ x,
      FiniteFourierSynthesis.synthesis x
        (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) f f -
          gammaIter (stableSymbol 1) 2 f f) =
        a x*FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 1 f f)) ↔
      r = 0 ∨ r = 1 := by
  constructor
  · intro h
    by_contra hh
    exact no_pointwise_scalar r (by omega) h
  · rintro (rfl|rfl)
    · refine ⟨fun _ => 0,?_⟩
      intro f x
      rw [second_correction]
      simp [bracket,harmonic,gammaIter_zero_left,gammaIter_zero_right]
    · refine ⟨fun x => (Real.cos (x 0):ℂ)/2,?_⟩
      intro f x
      simp_rw [harmonic_one]
      rw [map_sub,cauchy_drift_scalar_shift_synthesis]
      ring
end OperatorDerivativeRewrite.Foundation.CauchyHarmonicDrift
