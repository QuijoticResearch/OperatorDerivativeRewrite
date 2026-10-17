import Foundation.RealPeriodicViscousCancellation

/-! An explicit real periodic ABC Beltrami profile in the verified finite
Fourier algebra. No pressure-evolution conclusion is assumed. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.ABCFourierProfile
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
  FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
  FiniteFourierReality RealFiniteFourierAnalysis RealPeriodicViscousCancellation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def frequency (i : Fin 3) : Wave := Pi.single i 1
def cosine (i : Fin 3) : Fourier :=
  AddMonoidAlgebra.single (frequency i) (1/2)+AddMonoidAlgebra.single (-frequency i) (1/2)
def sine (i : Fin 3) : Fourier :=
  AddMonoidAlgebra.single (frequency i) (-Complex.I/2)+
    AddMonoidAlgebra.single (-frequency i) (Complex.I/2)
def abc : Fin 3 → Fourier := ![sine 2+cosine 1,sine 0+cosine 2,sine 1+cosine 0]

theorem reflection_mul (f g : Fourier) : reflection (f*g)=reflection f*reflection g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [add_mul,map_add,hf,hf'] <;> ring
  | single k c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [mul_add,map_add,hg,hg'] <;> ring
    | single l d => simp [AddMonoidAlgebra.single_mul_single,reflection_single,add_comm,map_ofNat]

theorem hermitian_mul (f g : Fourier) (hf : Hermitian f) (hg : Hermitian g) :
    Hermitian (f*g) := by
  rw [hermitian_iff_reflection]
  rw [reflection_mul,(hermitian_iff_reflection f).mp hf,(hermitian_iff_reflection g).mp hg]

theorem cosine_hermitian (i : Fin 3) : Hermitian (cosine i) := by
  rw [hermitian_iff_reflection]
  norm_num [cosine,reflection_single,add_comm,map_ofNat]

theorem sine_hermitian (i : Fin 3) : Hermitian (sine i) := by
  rw [hermitian_iff_reflection]
  norm_num [sine,reflection_single,add_comm,map_ofNat]

theorem abc_hermitian (i : Fin 3) : Hermitian (abc i) := by
  fin_cases i <;> exact hermitian_add _ _ (sine_hermitian _) (cosine_hermitian _)

theorem derivative_cosine (i j : Fin 3) :
    derivative j (cosine i)=if j=i then -sine i else 0 := by
  by_cases h : j=i
  · subst j
    ext k
    simp [cosine,sine,derivative_apply,d_single,weight,frequency,Pi.single_apply,
      Finsupp.single_apply,Complex.mul_re,Complex.mul_im] <;>
      split_ifs <;> ring_nf <;> norm_num [Complex.I_sq]
  · simp [cosine,derivative_apply,d_single,weight,frequency,Pi.single_apply,h,Ne.symm h]

theorem derivative_sine (i j : Fin 3) :
    derivative j (sine i)=if j=i then cosine i else 0 := by
  by_cases h : j=i
  · subst j
    ext k
    simp [cosine,sine,derivative_apply,d_single,weight,frequency,Pi.single_apply,
      Finsupp.single_apply,Complex.mul_re,Complex.mul_im] <;>
      split_ifs <;> ring_nf <;> norm_num [Complex.I_sq]
  · simp [sine,derivative_apply,d_single,weight,frequency,Pi.single_apply,h,Ne.symm h]

theorem abc_curl : curl derivative abc=abc := by
  ext i
  fin_cases i <;> norm_num [curl,axis,jacobian,abc,map_add,derivative_sine,derivative_cosine] <;> abel

theorem abc_divergence : divergence derivative abc=0 := by
  have h := divergence_curl derivative derivative_commute abc
  rw [abc_curl] at h
  exact h

theorem divergence_coefficient (u : Fin 3 → Fourier) (k : Wave) :
    (divergence derivative u).coeff k=Complex.I*(∑ i, (k i : ℂ)*(u i).coeff k) := by
  simp only [divergence,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    derivative_apply,d_coeff,weight,mul_assoc]
  rw [Finset.mul_sum]

theorem abc_transverse (k : Wave) : ∑ i, (k i : ℂ)*(abc i).coeff k=0 := by
  have h := congrArg (fun f : Fourier => f.coeff k) abc_divergence
  rw [divergence_coefficient] at h
  simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left Complex.I_ne_zero

theorem lap_cosine (i : Fin 3) : lap derivative (cosine i)=-cosine i := by
  fin_cases i <;> norm_num [lap,derivative_cosine,derivative_sine,map_neg,Fin.sum_univ_succ]

theorem lap_sine (i : Fin 3) : lap derivative (sine i)=-sine i := by
  fin_cases i <;> norm_num [lap,derivative_cosine,derivative_sine,map_neg,Fin.sum_univ_succ]

theorem abc_laplacian (i : Fin 3) : lap derivative (abc i)=-abc i := by
  fin_cases i <;> simp [abc,lap_add,lap_cosine,lap_sine,add_comm]

theorem phase_frequency (i : Fin 3) (x : Space) : phase (frequency i) x=x i := by
  simp [phase,frequency,Pi.single_apply,ite_mul,Finset.sum_ite_eq',eq_comm]

theorem character_frequency_re (i : Fin 3) (x : Space) :
    (character (frequency i) x).re=Real.cos (x i) := by
  simp [character,phase_frequency,Complex.exp_re,Complex.mul_re,Complex.mul_im]

theorem character_frequency_im (i : Fin 3) (x : Space) :
    (character (frequency i) x).im=Real.sin (x i) := by
  simp [character,phase_frequency,Complex.exp_im,Complex.mul_re,Complex.mul_im]

theorem realize_cosine (i : Fin 3) (x : Space) : realSynthesis (cosine i) x=Real.cos (x i) := by
  simp [realSynthesis,cosine,map_add,synthesis_single,character_neg,
    Complex.mul_re,Complex.mul_im,character_frequency_re,character_frequency_im] <;> ring

theorem realize_sine (i : Fin 3) (x : Space) : realSynthesis (sine i) x=Real.sin (x i) := by
  simp [realSynthesis,sine,map_add,synthesis_single,character_neg,
    Complex.mul_re,Complex.mul_im,character_frequency_re,character_frequency_im] <;> ring

theorem abc_realization (x : Space) : realizeReal abc x=
    ![Real.sin (x 2)+Real.cos (x 1),Real.sin (x 0)+Real.cos (x 2),Real.sin (x 1)+Real.cos (x 0)] := by
  ext i
  fin_cases i <;> simp [realizeReal,abc,realSynthesis,map_add,← realize_sine,← realize_cosine]

end OperatorDerivativeRewrite.Foundation.ABCFourierProfile
