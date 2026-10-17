import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Helicity cancellation in a commutative differential algebra with commuting
coordinate derivations and an invariant linear trace. Analytic realizations
must separately supply these explicit hypotheses. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CommutingDerivationHelicity
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

variable {𝕜 A : Type*} [Field 𝕜] [CharZero 𝕜] [CommRing A] [Algebra 𝕜 A]

def axis (B : Matrix (Fin 3) (Fin 3) A) : Fin 3 → A :=
  ![B 2 1-B 1 2,B 0 2-B 2 0,B 1 0-B 0 1]

theorem skew_axis_pairing (B : Matrix (Fin 3) (Fin 3) A) (w : Fin 3 → A) :
    dotProduct (B.mulVec w) (axis B)=dotProduct (B.transpose.mulVec w) (axis B) := by
  simp [axis,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ] <;> ring

def jacobian (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) : Matrix (Fin 3) (Fin 3) A :=
  fun i j => D j (w i)
def curl (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) : Fin 3 → A := axis (jacobian D w)
def divergence (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) : A := ∑ i, D i (w i)
def gradient (D : Fin 3 → Derivation 𝕜 A A) (f : A) : Fin 3 → A := fun i => D i f
def energy (w : Fin 3 → A) : A := ∑ i, (w i)^2
def advection (D : Fin 3 → Derivation 𝕜 A A) (v w : Fin 3 → A) : Fin 3 → A :=
  (jacobian D w).mulVec v

theorem divergence_curl (D : Fin 3 → Derivation 𝕜 A A)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f)) (w : Fin 3 → A) :
    divergence D (curl D w)=0 := by
  norm_num [divergence,curl,axis,jacobian,Fin.sum_univ_succ,map_sub]
  rw [hcomm 0 1 (w 2),hcomm 0 2 (w 1),hcomm 1 2 (w 0)]
  abel

theorem gradient_energy (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) :
    gradient D (energy w)=(2 : A) • (jacobian D w).transpose.mulVec w := by
  ext i
  simp [gradient,energy,jacobian,Matrix.mulVec,Matrix.transpose_apply,dotProduct,
    Fin.sum_univ_succ,pow_two,Derivation.leibniz,smul_eq_mul] <;> ring

theorem twice_helicity_pointwise (D : Fin 3 → Derivation 𝕜 A A) (w : Fin 3 → A) :
    2*dotProduct (advection D w w) (curl D w)=
      dotProduct (gradient D (energy w)) (curl D w) := by
  rw [gradient_energy,smul_dotProduct,smul_eq_mul]
  exact congrArg (fun x : A => 2*x) (skew_axis_pairing (jacobian D w) w)

theorem integration_by_parts (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hT : ∀ i f, T (D i f)=0) (i : Fin 3) (f g : A) :
    T (D i f*g)=-T (f*D i g) := by
  have h := hT i (f*g)
  rw [Derivation.leibniz,map_add] at h
  simp only [smul_eq_mul] at h
  rw [mul_comm g (D i f)] at h
  exact eq_neg_of_add_eq_zero_right h

theorem gradient_pairing (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hT : ∀ i f, T (D i f)=0) (f : A) (w : Fin 3 → A) :
    T (dotProduct (gradient D f) w)=-T (f*divergence D w) := by
  calc
    T (dotProduct (gradient D f) w)=∑ i, T (D i f*w i) := by
      simp only [dotProduct,gradient,map_sum]
    _ = ∑ i, -T (f*D i (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integration_by_parts D T hT i f (w i)
    _ = -T (f*divergence D w) := by
      simp only [divergence,Finset.mul_sum,map_sum,Finset.sum_neg_distrib]

theorem helicity_zero (D : Fin 3 → Derivation 𝕜 A A) (T : A →ₗ[𝕜] 𝕜)
    (hcomm : ∀ i j f, D i (D j f)=D j (D i f))
    (hT : ∀ i f, T (D i f)=0) (w : Fin 3 → A) :
    T (dotProduct (advection D w w) (curl D w))=0 := by
  have hg := gradient_pairing D T hT (energy w) (curl D w)
  rw [divergence_curl D hcomm,mul_zero,map_zero,neg_zero] at hg
  have h := congrArg T (twice_helicity_pointwise D w)
  rw [two_mul,map_add,hg] at h
  have hz : (2 : 𝕜)*T (dotProduct (advection D w w) (curl D w))=0 := by
    rw [two_mul]
    exact h
  exact (mul_eq_zero.mp hz).resolve_left two_ne_zero

end OperatorDerivativeRewrite.Foundation.CommutingDerivationHelicity
