import Foundation.DifferentialTraceViscousCancellation
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Complex.Basic

/-! Concrete finite Fourier algebra: convolution multiplication, ik_j
coordinate derivations and the constant-coefficient trace. Analytic synthesis
and identification with actual torus integrals are separate obligations. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteFourierDifferentialTrace
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev Wave := Fin 3 → ℤ
abbrev Fourier := AddMonoidAlgebra ℂ Wave

def weight (i : Fin 3) (k : Wave) : ℂ := Complex.I*(k i : ℂ)

theorem weight_add (i : Fin 3) (k l : Wave) : weight i (k+l)=weight i k+weight i l := by
  simp [weight,Pi.add_apply,mul_add]

def dLinear (i : Fin 3) : Fourier →ₗ[ℂ] Fourier :=
  (Finsupp.linearCombination ℂ (fun k : Wave =>
    weight i k • (AddMonoidAlgebra.single k 1 : Fourier))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem d_single (i : Fin 3) (k : Wave) (c : ℂ) :
    dLinear i (AddMonoidAlgebra.single k c)=AddMonoidAlgebra.single k (weight i k*c) := by
  simp [dLinear,Finsupp.linearCombination_single,smul_smul,mul_comm]

theorem d_coeff (i : Fin 3) (f : Fourier) (k : Wave) :
    (dLinear i f).coeff k=weight i k*f.coeff k := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf,hg,mul_add]
  | single l c =>
    rw [d_single]
    by_cases h : l=k
    · subst l; simp
    · simp [Finsupp.single_apply,h,Ne.symm h]

theorem d_mul (i : Fin 3) (f g : Fourier) :
    dLinear i (f*g)=f*dLinear i g+g*dLinear i f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f f' hf hf' =>
    simp only [add_mul,map_add,hf,hf',mul_add]
    ring
  | single k c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g g' hg hg' =>
      simp only [mul_add,map_add,hg,hg',add_mul]
      ring
    | single l d =>
      ext m
      by_cases h : k+l=m
      · subst m
        simp [AddMonoidAlgebra.single_mul_single,d_single,weight_add,add_comm]
        ring
      · simp [AddMonoidAlgebra.single_mul_single,d_single,Finsupp.single_apply,h,add_comm l k]

theorem d_one (i : Fin 3) : dLinear i (1 : Fourier)=0 := by
  rw [AddMonoidAlgebra.one_def,d_single]
  simp [weight]

def derivative (i : Fin 3) : Derivation ℂ Fourier Fourier where
  toLinearMap := dLinear i
  map_one_eq_zero' := d_one i
  leibniz' f g := by simpa only [smul_eq_mul] using d_mul i f g

theorem derivative_apply (i : Fin 3) (f : Fourier) : derivative i f=dLinear i f := rfl

theorem derivative_commute (i j : Fin 3) (f : Fourier) :
    derivative i (derivative j f)=derivative j (derivative i f) := by
  ext k
  simp only [derivative_apply,d_coeff]
  ring

def constantTrace : Fourier →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (0 : Wave)).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem constantTrace_apply (f : Fourier) : constantTrace f=f.coeff 0 := rfl

theorem constantTrace_derivative (i : Fin 3) (f : Fourier) :
    constantTrace (derivative i f)=0 := by
  rw [constantTrace_apply,derivative_apply,d_coeff]
  simp [weight]

theorem transverse_divergence_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) : divergence derivative u=0 := by
  ext k
  simp only [divergence,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    derivative_apply,d_coeff,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,weight]
  simp only [mul_assoc]
  rw [← Finset.mul_sum,hu,mul_zero]

theorem fourier_helicity_zero (w : Fin 3 → Fourier) :
    constantTrace (dotProduct (advection derivative w w) (curl derivative w))=0 :=
  helicity_zero derivative constantTrace derivative_commute constantTrace_derivative w

theorem fourier_miller_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    constantTrace (∑ i, ∑ j,
      curl derivative u i*lap derivative (strain derivative u i j)*curl derivative u j)=0 :=
  miller_zero derivative constantTrace derivative_commute constantTrace_derivative u
    (transverse_divergence_zero u hu)

theorem fourier_cross_zero (u : Fin 3 → Fourier)
    (hu : ∀ k : Wave, ∑ i, (k i : ℂ)*(u i).coeff k=0) :
    constantTrace (crossContraction derivative (curl derivative u) (strain derivative u))=0 :=
  cross_zero derivative constantTrace derivative_commute constantTrace_derivative u
    (transverse_divergence_zero u hu)

end OperatorDerivativeRewrite.Foundation.FiniteFourierDifferentialTrace
