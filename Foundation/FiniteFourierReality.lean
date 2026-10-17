import Foundation.FiniteFourierPeriodicCancellation
import Mathlib.Analysis.Complex.Basic

/-! Hermitian coefficient symmetry, actual real-valued synthesis, and its
preservation by coordinate differentiation and real linear combinations. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.FiniteFourierReality
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def reflectionCoeffs : (Wave →₀ ℂ) →ₗ[ℝ] (Wave →₀ ℂ) :=
  Finsupp.lsum ℝ (fun k : Wave =>
    (Finsupp.lsingle (-k) : ℂ →ₗ[ℝ] (Wave →₀ ℂ)).comp Complex.conjAe.toLinearMap)

def reflection : Fourier →ₗ[ℝ] Fourier :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    (reflectionCoeffs.comp (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap)

theorem reflection_single (k : Wave) (c : ℂ) :
    reflection (AddMonoidAlgebra.single k c)=AddMonoidAlgebra.single (-k) (conj c) := by
  simp [reflection,reflectionCoeffs,Finsupp.lsum_single]

theorem reflection_coeff (f : Fourier) (k : Wave) :
    (reflection f).coeff k=conj (f.coeff (-k)) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf,hg]
  | single l c =>
    rw [reflection_single]
    by_cases h : l=-k
    · subst l
      simp
    · have h' : -l ≠ k := by
        intro he
        apply h
        simpa using congrArg Neg.neg he
      simp [Finsupp.single_apply,h,h',Ne.symm h,Ne.symm h']

def Hermitian (f : Fourier) : Prop := ∀ k : Wave, f.coeff (-k)=conj (f.coeff k)

theorem hermitian_iff_reflection (f : Fourier) : Hermitian f ↔ reflection f=f := by
  constructor
  · intro h
    ext k
    rw [reflection_coeff,h k]
    simp
  · intro h k
    have he := congrArg (fun g : Fourier => g.coeff (-k)) h
    simpa only [reflection_coeff,neg_neg] using he.symm

theorem phase_neg (k : Wave) (x : Space) : phase (-k) x=-phase k x := by
  simp [phase,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem character_neg (k : Wave) (x : Space) : character (-k) x=conj (character k x) := by
  simp only [character,phase_neg,Complex.ofReal_neg]
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem synthesis_reflection (f : Fourier) (x : Space) :
    synthesis x (reflection f)=conj (synthesis x f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf,hg]
  | single k c => simp [reflection_single,synthesis_single,character_neg]

theorem synthesis_im_zero (f : Fourier) (hf : Hermitian f) (x : Space) :
    (synthesis x f).im=0 := by
  have h := synthesis_reflection f x
  rw [(hermitian_iff_reflection f).mp hf] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem ofReal_synthesis_re (f : Fourier) (hf : Hermitian f) (x : Space) :
    ((synthesis x f).re : ℂ)=synthesis x f := by
  apply Complex.ext
  · rfl
  · simp [synthesis_im_zero f hf x]

theorem hermitian_derivative (f : Fourier) (hf : Hermitian f) (j : Fin 3) :
    Hermitian (derivative j f) := by
  intro k
  simp [derivative_apply,d_coeff,weight,hf k] <;> ring

theorem hermitian_zero : Hermitian (0 : Fourier) := by intro k; simp

theorem hermitian_add (f g : Fourier) (hf : Hermitian f) (hg : Hermitian g) :
    Hermitian (f+g) := by
  intro k
  simp [hf k,hg k]

theorem hermitian_sub (f g : Fourier) (hf : Hermitian f) (hg : Hermitian g) :
    Hermitian (f-g) := by
  intro k
  simp [hf k,hg k]

theorem hermitian_real_smul (r : ℝ) (f : Fourier) (hf : Hermitian f) :
    Hermitian ((r : ℂ) • f) := by
  intro k
  simp [hf k]

theorem hermitian_sum {ι : Type*} (s : Finset ι) (f : ι → Fourier)
    (hf : ∀ i ∈ s, Hermitian (f i)) : Hermitian (∑ i ∈ s, f i) := by
  intro k
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi k)

end OperatorDerivativeRewrite.Foundation.FiniteFourierReality
