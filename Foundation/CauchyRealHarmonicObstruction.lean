import Foundation.CauchyHarmonicDrift
/-! Real-valued cosine witnesses for the single-harmonic scalar obstruction.
For r>=2, twice cosine(theta) and twice cosine(r theta) force incompatible
pointwise factors in the ACTUAL finite Fourier Gamma recursion.
The real Hermitian-core classification is r=0 or r=1 for r>=0.
No mixed-potential classification, curvature bound or completed-domain claim. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.CauchyRealHarmonicObstruction
open FiniteFourierDifferentialTrace FiniteFourierReality FiniteFourierSynthesis FiniteStableGamma.Core CauchySineDrift
open CauchyHigherDriftObstruction (wave mode wave_neg synthesis_mode_zero)
open CauchyHarmonicDrift

def pair (n : ℤ) : Fourier := mode n+mode (-n)

theorem pair_hermitian (n : ℤ) : Hermitian (pair n) := by
  rw [hermitian_iff_reflection]
  simp [pair,mode,reflection_single,← wave_neg,add_comm]

theorem synthesis_single_zero (k : Wave) (c : ℂ) :
    synthesis 0 (AddMonoidAlgebra.single k c) = c := by
  simp [synthesis_single,character,phase]

theorem gamma_pair_zero (n : ℤ) (hn : 0 ≤ n) :
    synthesis 0 (gammaIter (stableSymbol 1) 1 (pair n) (pair n)) = (2:ℂ)*n := by
  simp only [pair,mode,gammaIter_add_left,gammaIter_add_right,gammaIter_single,
    pow_one,map_add,synthesis_single_zero,map_one,mul_one,kernel_axis]
  have h1 : -n-n = -(n+n) := by omega
  simp only [neg_neg,sub_self,abs_zero,sub_zero,sub_neg_eq_add,h1,
    abs_neg,abs_of_nonneg hn,abs_of_nonneg (add_nonneg hn hn)]
  push_cast
  ring

theorem pair_correction_at_zero (n r : ℤ) :
    synthesis 0
      (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (pair n) (pair n) -
        gammaIter (stableSymbol 1) 2 (pair n) (pair n)) =
      -(1/2:ℂ)*synthesis 0 (gammaIter (stableSymbol 1) 1 (harmonic r (pair n)) (pair n)) -
       (1/2:ℂ)*synthesis 0 (gammaIter (stableSymbol 1) 1 (pair n) (harmonic r (pair n))) := by
  rw [second_correction]
  simp only [add_sub_cancel_left,map_smul,bracket,map_sub,harmonic_synthesis]
  simp
  ring

theorem pair_one_correction (r : ℤ) (hr : 2 ≤ r) :
    synthesis 0
      (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (pair 1) (pair 1) -
        gammaIter (stableSymbol 1) 2 (pair 1) (pair 1)) = 0 := by
  rw [pair_correction_at_zero]
  simp only [pair,harmonic_add,mode,action_axis,gammaIter_add_left,gammaIter_add_right,
    gamma_sub_left,gamma_sub_right,gammaIter_single,pow_one,map_add,map_sub,
    synthesis_single_zero,map_mul,map_div₀,map_intCast,map_ofNat,map_one,mul_one,kernel_axis]
  norm_num
  ring_nf
  simp only [abs_neg,abs_of_nonneg (show 0 ≤ r by omega),
    abs_of_nonneg (show 0 ≤ 1+r by omega),abs_of_nonneg (show 0 ≤ 2+r by omega),
    abs_of_nonneg (show 0 ≤ -1+r by omega),abs_of_nonneg (show 0 ≤ -2+r by omega),
    abs_of_nonpos (show 1-r ≤ 0 by omega),abs_of_nonpos (show 2-r ≤ 0 by omega),
    abs_of_nonpos (show -1-r ≤ 0 by omega),abs_of_nonpos (show -2-r ≤ 0 by omega)]
  push_cast
  ring

theorem pair_harmonic_correction (r : ℤ) (hr : 0 ≤ r) :
    synthesis 0
      (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) (pair r) (pair r) -
        gammaIter (stableSymbol 1) 2 (pair r) (pair r)) = (r:ℂ)^2 := by
  rw [pair_correction_at_zero]
  simp only [pair,harmonic_add,mode,action_axis,gammaIter_add_left,gammaIter_add_right,
    gamma_sub_left,gamma_sub_right,gammaIter_single,pow_one,map_add,map_sub,
    synthesis_single_zero,map_mul,map_div₀,map_intCast,map_ofNat,map_one,mul_one,kernel_axis]
  simp [abs_of_nonneg hr]
  push_cast
  ring_nf
  simp [abs_neg,abs_mul,abs_of_nonneg hr]
  ring
theorem pair_synthesis (n : ℤ) (x : Space) :
    synthesis x (pair n) = 2*(Real.cos ((n:ℝ)*x 0):ℂ) := by
  have hp : character (wave n) x = Complex.exp (((n:ℝ)*x 0:ℝ)*Complex.I) := by
    simp [character,phase,wave,Fin.sum_univ_three,mul_comm]
  have hm : character (wave (-n)) x = Complex.exp (-(((n:ℝ)*x 0:ℝ):ℂ)*Complex.I) := by
    simp [character,phase,wave,Fin.sum_univ_three,mul_comm]
  simp only [pair,mode,map_add,synthesis_single,one_mul]
  rw [hp,hm,Complex.ofReal_cos,Complex.cos]
  ring

theorem no_real_scalar_at_zero (r : ℤ) (hr : 2 ≤ r) :
    ¬ ∃ a : ℂ, ∀ f : Fourier, Hermitian f →
      synthesis 0
        (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) f f -
          gammaIter (stableSymbol 1) 2 f f) = a*synthesis 0 (gammaIter (stableSymbol 1) 1 f f) := by
  rintro ⟨a,ha⟩
  have h1 := ha (pair 1) (pair_hermitian 1)
  have h2 := ha (pair r) (pair_hermitian r)
  rw [pair_one_correction r hr,gamma_pair_zero 1 (by omega)] at h1
  rw [pair_harmonic_correction r (by omega),gamma_pair_zero r (by omega)] at h2
  norm_num at h1
  have ha0 : a = 0 := h1
  rw [ha0] at h2
  have hh := congrArg Complex.re h2
  norm_num [pow_two,Complex.mul_re] at hh
  have hrreal : 2 ≤ (r:ℝ) := by exact_mod_cast hr
  nlinarith

theorem real_scalar_iff (r : ℤ) (hr : 0 ≤ r) :
    (∃ a : Space → ℂ, ∀ f : Fourier, Hermitian f → ∀ x,
      synthesis x
        (secondGamma (fun h => generator (stableSymbol 1) h+harmonic r h) f f -
          gammaIter (stableSymbol 1) 2 f f) = a x*synthesis x (gammaIter (stableSymbol 1) 1 f f)) ↔
      r = 0 ∨ r = 1 := by
  constructor
  · rintro ⟨a,ha⟩
    by_contra hh
    exact no_real_scalar_at_zero r (by omega) ⟨a 0,fun f hf => ha f hf 0⟩
  · intro h
    obtain ⟨a,ha⟩ := (scalar_iff r hr).mpr h
    exact ⟨a,fun f _ x => ha f x⟩
end OperatorDerivativeRewrite.Foundation.CauchyRealHarmonicObstruction
