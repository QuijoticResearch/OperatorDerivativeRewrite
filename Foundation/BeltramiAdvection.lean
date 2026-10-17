import Foundation.ABCFourierProfile

/-! Exact Beltrami advection identities in a commutative differential algebra.
These are algebraic identities, with no Navier–Stokes existence assertion. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.BeltramiAdvection
open CommutingDerivationHelicity DifferentialTraceViscousCancellation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

variable {𝕜 A : Type*} [Field 𝕜] [CharZero 𝕜] [CommRing A] [Algebra 𝕜 A]

theorem skew_axis_annihilation (B : Matrix (Fin 3) (Fin 3) A) :
    B.mulVec (axis B)=B.transpose.mulVec (axis B) := by
  ext i
  fin_cases i <;>
    simp [axis,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ] <;> ring

def kinetic (u : Fin 3 → A) : A := (1/2 : 𝕜) • energy u

theorem gradient_kinetic (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A) :
    gradient D (kinetic (𝕜 := 𝕜) u)=(jacobian D u).transpose.mulVec u := by
  have hs : gradient D (kinetic (𝕜 := 𝕜) u)=
      (1/2 : 𝕜) • gradient D (energy u) := by
    ext i
    exact Derivation.map_smul (D i) (1/2 : 𝕜) (energy u)
  rw [hs,gradient_energy]
  have ht : (2 : A) • (jacobian D u).transpose.mulVec u=
      (2 : 𝕜) • (jacobian D u).transpose.mulVec u := by
    simp only [two_smul]
  rw [ht,smul_smul]
  norm_num
theorem beltrami_advection (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A)
    (hu : curl D u=u) : advection D u u=gradient D (kinetic (𝕜 := 𝕜) u) := by
  rw [gradient_kinetic]
  have h := skew_axis_annihilation (jacobian D u)
  change (jacobian D u).mulVec (curl D u)=
    (jacobian D u).transpose.mulVec (curl D u) at h
  simpa only [hu,advection] using h

theorem beltrami_strain (D : Fin 3 → Derivation 𝕜 A A) (u : Fin 3 → A)
    (hu : curl D u=u) : Matrix.mulVec (strain D u) u=gradient D (kinetic (𝕜 := 𝕜) u) := by
  have h := beltrami_advection D u hu
  rw [gradient_kinetic] at h ⊢
  change (jacobian D u).mulVec u=(jacobian D u).transpose.mulVec u at h
  have hs : Matrix.mulVec (strain D u) u=
      (1/2 : 𝕜) • ((jacobian D u).mulVec u+(jacobian D u).transpose.mulVec u) := by
    ext i
    simp [strain,twiceStrain,jacobian,Matrix.mulVec,Matrix.transpose_apply,
      dotProduct,Fin.sum_univ_succ,smul_add,Algebra.smul_def] <;> ring
  rw [hs,h]
  module

theorem beltrami_stretching_trace (D : Fin 3 → Derivation 𝕜 A A)
    (T : A →ₗ[𝕜] 𝕜) (hT : ∀ i f, T (D i f)=0) (u : Fin 3 → A)
    (hu : curl D u=u) (hdiv : divergence D u=0) :
    T (dotProduct (Matrix.mulVec (strain D u) u) u)=0 := by
  rw [beltrami_strain D u hu,gradient_pairing D T hT,hdiv,mul_zero,map_zero,neg_zero]

theorem beltrami_pressure_trace (D : Fin 3 → Derivation 𝕜 A A)
    (T : A →ₗ[𝕜] 𝕜) (hT : ∀ i f, T (D i f)=0) (u : Fin 3 → A)
    (hu : curl D u=u) (hdiv : divergence D u=0) :
    T (linearContraction D u (gradient D (-kinetic (𝕜 := 𝕜) u)))=
      T (dotProduct (gradient D (kinetic (𝕜 := 𝕜) u))
        (gradient D (kinetic (𝕜 := 𝕜) u))) := by
  have hn : gradient D (-kinetic (𝕜 := 𝕜) u)=
      -gradient D (kinetic (𝕜 := 𝕜) u) := by
    ext i
    simp [gradient]
  rw [trace_linearContraction D T hT u _ hdiv,beltrami_advection D u hu,
    hn,dotProduct_neg,map_neg,neg_neg]

end OperatorDerivativeRewrite.Foundation.BeltramiAdvection
