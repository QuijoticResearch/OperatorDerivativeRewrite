import Foundation.CauchySineDrift
/-! The first-harmonic scalar Gamma correction does not extend to all
trigonometric drifts. The actual drift -sin(2 theta) d/dtheta already has
incompatible corrections on positive Fourier modes one and two.
All statements concern the existing finite Fourier recursion; no new
semigroup, curvature bound, or completed-domain claim is made. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.CauchyHigherDriftObstruction
open FiniteFourierDifferentialTrace FiniteFourierReality FiniteStableGamma.Core CauchySineDrift

def wave (n : ℤ) : Wave := ![n,0,0]
def mode (n : ℤ) : Fourier := AddMonoidAlgebra.single (wave n) 1
def transportTwo (f : Fourier) : Fourier :=
  ((Complex.I/2) • (mode 2-mode (-2))) * dLinear 0 f

theorem wave_neg (n : ℤ) : wave (-n) = -wave n := by
  ext i; fin_cases i <;> simp [wave]

theorem transportTwo_product (f g : Fourier) :
    transportTwo (f*g) = f * transportTwo g + g * transportTwo f := by
  unfold transportTwo
  rw [d_mul]
  ring

theorem transportTwo_general_single (k : Wave) (c : ℂ) :
    transportTwo (AddMonoidAlgebra.single k c) =
      AddMonoidAlgebra.single (k-(wave 2)) ((k 0 : ℂ)/2*c) -
      AddMonoidAlgebra.single (k+(wave 2)) ((k 0 : ℂ)/2*c) := by
  simp only [transportTwo,mode,wave_neg, d_single, weight, sub_mul,
    AddMonoidAlgebra.single_mul_single, smul_sub, AddMonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]
  have hc : (Complex.I/2) * (Complex.I*(k 0 : ℂ)*c) = -((k 0 : ℂ)/2*c) := by
    calc
      _ = (Complex.I*Complex.I) * ((k 0 : ℂ)/2*c) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hc, add_comm (wave 2) k, show -(wave 2)+k = k-(wave 2) by abel]
  simp
  abel

theorem transportTwo_add (f g : Fourier) : transportTwo (f+g) = transportTwo f+transportTwo g := by
  simp [transportTwo, mul_add]

theorem transportTwo_reflection (f : Fourier) :
    reflection (transportTwo f) = transportTwo (reflection f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [transportTwo]
  | add f g hf hg => simp [transportTwo_add, hf, hg]
  | single k c =>
    simp only [transportTwo_general_single, map_sub, reflection_single]
    have h₁ : -(k-(wave 2)) = -k+(wave 2) := by abel
    have h₂ : -(k+(wave 2)) = -k-(wave 2) := by abel
    rw [h₁, h₂]
    simp only [map_mul, map_div₀, map_intCast, map_ofNat, Pi.neg_apply,
      Int.cast_neg, neg_div, neg_mul, AddMonoidAlgebra.single_neg]
    abel

theorem transportTwo_gamma_zero (f g : Fourier) :
    transportTwo (reflection f*g) - reflection (transportTwo f)*g -
      reflection f*transportTwo g = 0 := by
  rw [transportTwo_product, transportTwo_reflection]
  ring

theorem firstGamma_transportTwo_invariant (L : Fourier → Fourier) (f g : Fourier) :
     firstGamma (fun h => L h + transportTwo h) f g = firstGamma L f g := by
   unfold firstGamma
   simp only [map_add, add_mul, mul_add]
   have ht := transportTwo_gamma_zero f g
   congr 1
   linear_combination ht

theorem transportTwo_single (n : ℤ) (c : ℂ) :
    transportTwo (AddMonoidAlgebra.single (wave n) c) =
      AddMonoidAlgebra.single (wave (n-2)) ((n:ℂ)/2*c) -
      AddMonoidAlgebra.single (wave (n+2)) ((n:ℂ)/2*c) := by
  have h1 : wave 2+wave n = wave (n+2) := by ext i; fin_cases i <;> simp [wave] <;> ring
  have h2 : wave (-2)+wave n = wave (n-2) := by ext i; fin_cases i <;> simp [wave] <;> ring
  simp only [transportTwo,mode,d_single,weight,sub_mul,
    AddMonoidAlgebra.single_mul_single,smul_sub,AddMonoidAlgebra.smul_single,
    smul_eq_mul,mul_one,h1,h2]
  have hc : (Complex.I/2)*(Complex.I*(n:ℂ)*c) = -((n:ℂ)/2*c) := by
    calc
      _ = (Complex.I*Complex.I)*((n:ℂ)/2*c) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simp only [wave,Matrix.cons_val_zero,hc,AddMonoidAlgebra.single_neg]
  abel

def bracket (f g : Fourier) : Fourier :=
  transportTwo (gammaIter (stableSymbol 1) 1 f g) -
    gammaIter (stableSymbol 1) 1 (transportTwo f) g -
    gammaIter (stableSymbol 1) 1 f (transportTwo g)

theorem wave_sub (n m : ℤ) : wave n-wave m = wave (n-m) := by
  ext i; fin_cases i <;> simp [wave]

theorem bracket_one : bracket (mode 1) (mode 1) = (1/2:ℂ) • (mode 2+mode (-2)) := by
  unfold bracket mode
  simp only [gammaIter_single,pow_one,transportTwo_single,gamma_sub_left,gamma_sub_right,
    gammaIter_single,pow_one,wave_sub]
  norm_num [cauchy_kernel_twice,twiceKernel,wave,transportTwo,mode,map_mul]
  ext w
  simp [AddMonoidAlgebra.coeff_single]
  norm_num [map_ofNat,add_comm]

theorem bracket_two : bracket (mode 2) (mode 2) = (2:ℂ) • (mode 2+mode (-2)) := by
  unfold bracket mode
  simp only [gammaIter_single,pow_one,transportTwo_single,gamma_sub_left,gamma_sub_right,
    gammaIter_single,pow_one,wave_sub]
  norm_num [cauchy_kernel_twice,twiceKernel,wave,transportTwo,mode,map_mul]
  ext w
  simp [AddMonoidAlgebra.coeff_single]
  norm_num [map_ofNat,add_comm]
theorem transportTwo_synthesis (f : Fourier) (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x (transportTwo f) =
      -(Real.sin (2*x 0) : ℂ)*FiniteFourierSynthesis.synthesis x (dLinear 0 f) := by
  have hp : FiniteFourierSynthesis.character (wave 2) x = Complex.exp ((2*x 0:ℝ)*Complex.I) := by
    simp [FiniteFourierSynthesis.character,FiniteFourierSynthesis.phase,wave,Fin.sum_univ_three,mul_comm]
  have hm : FiniteFourierSynthesis.character (wave (-2)) x = Complex.exp (-((2*x 0:ℝ):ℂ)*Complex.I) := by
    simp [FiniteFourierSynthesis.character,FiniteFourierSynthesis.phase,wave,Fin.sum_univ_three,mul_comm]
  simp only [transportTwo,mode,FiniteFourierSynthesis.synthesis_mul,map_smul,map_sub,
    FiniteFourierSynthesis.synthesis_single,one_mul,smul_eq_mul]
  rw [hp,hm,Complex.ofReal_sin,Complex.sin]
  field_simp
  ring_nf

theorem gamma_one : gammaIter (stableSymbol 1) 1 (mode 1) (mode 1) = mode 0 := by
  have hz : wave 0 = 0 := by ext i; fin_cases i <;> simp [wave]
  simpa [mode,gammaIter_single,cauchy_kernel_twice,twiceKernel,wave] using congrArg (fun k : Wave => AddMonoidAlgebra.single k (1:ℂ)) hz.symm
theorem gamma_two : gammaIter (stableSymbol 1) 1 (mode 2) (mode 2) = (2:ℂ) • mode 0 := by
  have hz : wave 0 = 0 := by ext i; fin_cases i <;> simp [wave]
  norm_num [mode,gammaIter_single,cauchy_kernel_twice,twiceKernel,wave]
  exact congrArg (fun k : Wave => AddMonoidAlgebra.single k (2:ℂ)) hz.symm

theorem second_correction (f g : Fourier) :
    secondGamma (fun h => generator (stableSymbol 1) h+transportTwo h) f g =
      gammaIter (stableSymbol 1) 2 f g + (1/2:ℂ) • bracket f g := by
  unfold secondGamma
  simp only [firstGamma_transportTwo_invariant,firstGamma_generator,
    gammaIter_add_left,gammaIter_add_right]
  change _ = (1/2:ℂ) •
    (generator (stableSymbol 1) (gammaIter (stableSymbol 1) 1 f g) -
     gammaIter (stableSymbol 1) 1 (generator (stableSymbol 1) f) g -
     gammaIter (stableSymbol 1) 1 f (generator (stableSymbol 1) g)) + _
  unfold bracket
  module

theorem second_one :
    secondGamma (fun f => generator (stableSymbol 1) f+transportTwo f) (mode 1) (mode 1) -
      gammaIter (stableSymbol 1) 2 (mode 1) (mode 1) = (1/4:ℂ) • (mode 2+mode (-2)) := by
  rw [second_correction,bracket_one]
  module

theorem second_two :
    secondGamma (fun f => generator (stableSymbol 1) f+transportTwo f) (mode 2) (mode 2) -
      gammaIter (stableSymbol 1) 2 (mode 2) (mode 2) = mode 2+mode (-2) := by
  rw [second_correction,bracket_two]
  module
theorem synthesis_mode_zero (n : ℤ) : FiniteFourierSynthesis.synthesis 0 (mode n) = 1 := by
  simp [mode,FiniteFourierSynthesis.synthesis_single,FiniteFourierSynthesis.character,
    FiniteFourierSynthesis.phase]

theorem no_scalar_at_zero :
    ¬ ∃ a : ℂ, ∀ f : Fourier,
      FiniteFourierSynthesis.synthesis 0
        (secondGamma (fun h => generator (stableSymbol 1) h+transportTwo h) f f -
          gammaIter (stableSymbol 1) 2 f f) =
        a*FiniteFourierSynthesis.synthesis 0 (gammaIter (stableSymbol 1) 1 f f) := by
  rintro ⟨a,ha⟩
  have h1 := ha (mode 1)
  have h2 := ha (mode 2)
  rw [second_one,gamma_one] at h1
  rw [second_two,gamma_two] at h2
  norm_num [map_add,map_smul,synthesis_mode_zero,smul_eq_mul] at h1 h2
  have hr1 := congrArg Complex.re h1
  have hr2 := congrArg Complex.re h2
  norm_num [Complex.mul_re] at hr1 hr2
  linarith

theorem no_pointwise_scalar :
    ¬ ∃ a : FiniteFourierSynthesis.Space → ℂ, ∀ f : Fourier, ∀ x,
      FiniteFourierSynthesis.synthesis x
        (secondGamma (fun h => generator (stableSymbol 1) h+transportTwo h) f f -
          gammaIter (stableSymbol 1) 2 f f) =
        a x*FiniteFourierSynthesis.synthesis x (gammaIter (stableSymbol 1) 1 f f) := by
  rintro ⟨a,ha⟩
  exact no_scalar_at_zero ⟨a 0,fun f => ha f 0⟩
end OperatorDerivativeRewrite.Foundation.CauchyHigherDriftObstruction
