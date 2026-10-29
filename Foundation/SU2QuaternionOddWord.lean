import Foundation.FourCubeMovingSchurLimit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Exact odd Wilson words isolate the cubic channel without matching third matrix jets. -/
noncomputable section
open Filter Set
open scoped Quaternion Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2QuaternionOddWord
open QuaternionSU2Representation SU2TraceHessianModel

abbrev Vector := Fin 3 → ℝ

def imagVector (q : ℍ) : Vector := ![q.imI,q.imJ,q.imK]
def triple (u v w : Vector) : ℝ :=
  u 0*(v 1*w 2-v 2*w 1)-u 1*(v 0*w 2-v 2*w 0)+u 2*(v 0*w 1-v 1*w 0)
def weightedCubic (r : Fin 4 → ℝ) (v : Fin 4 → Vector) : ℝ :=
  r 3*triple (v 0) (v 1) (v 2)+r 2*triple (v 0) (v 1) (v 3)+
    r 1*triple (v 0) (v 2) (v 3)+r 0*triple (v 1) (v 2) (v 3)
def cubic (v : Fin 4 → Vector) : ℝ := weightedCubic (fun _ => 1) v

def rawAction (q : Fin 4 → ℍ) : ℝ := 1-(q 0*q 1*q 2*q 3).re

theorem exact_odd_word (q : Fin 4 → ℍ) :
    rawAction q-rawAction (fun i => star (q i))=
      2*weightedCubic (fun i => (q i).re) (fun i => imagVector (q i)) := by
  simp [rawAction,weightedCubic,triple,imagVector,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
  ring

theorem odd_quotient (q : Fin 4 → ℍ) (t : ℝ) (ht : t ≠ 0) :
    (rawAction q-rawAction (fun i => star (q i)))/(2*t^3)=
      weightedCubic (fun i => (q i).re) (fun i a => imagVector (q i) a/t) := by
  rw [exact_odd_word]
  unfold weightedCubic triple
  field_simp [ht] <;> ring

theorem weightedCubic_continuous : Continuous (fun p : (Fin 4 → ℝ) × (Fin 4 → Vector) =>
    weightedCubic p.1 p.2) := by
  unfold weightedCubic triple
  fun_prop

theorem odd_word_limit (q : ℝ → Fin 4 → ℍ) (v : Fin 4 → Vector)
    (hp : ∀ t i,q (-t) i=star (q t i))
    (hr : ∀ i,Tendsto (fun t => (q t i).re) (𝓝[≠] 0) (𝓝 1))
    (hv : ∀ i a,Tendsto (fun t => imagVector (q t i) a/t) (𝓝[≠] 0) (𝓝 (v i a))) :
    Tendsto (fun t : ℝ => (rawAction (q t)-rawAction (q (-t)))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubic v)) := by
  have hreal : Tendsto (fun t i => (q t i).re) (𝓝[≠] 0) (𝓝 (fun _ => 1)) :=
    tendsto_pi_nhds.mpr hr
  have him : Tendsto (fun t i a => imagVector (q t i) a/t) (𝓝[≠] 0) (𝓝 v) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hv i))
  have hh := weightedCubic_continuous.continuousAt.tendsto.comp (hreal.prodMk_nhds him)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : q (-t)=(fun i => star (q t i)) := funext (hp t)
  rw [he,odd_quotient (q t) t ht]
  rfl

def coordinate (a : Fin 4) (M : M2) : ℝ :=
  ![(M 0 0).re,(M 0 0).im,(M 0 1).re,(M 0 1).im] a

def coordinateLinear (a : Fin 4) : M2 →ₗ[ℝ] ℝ where
  toFun := coordinate a
  map_add' M N := by fin_cases a <;> simp [coordinate]
  map_smul' r M := by fin_cases a <;> simp [coordinate,Complex.real_smul]

def coordinateCLM (a : Fin 4) : M2 →L[ℝ] ℝ := (coordinateLinear a).toContinuousLinearMap

theorem recover_inverse (U : SU2) : recover ((U⁻¹ : SU2) : M2)=star (recover (U : M2)) := by
  apply repr_injective
  rw [repr_recover _ (U⁻¹).property,repr_star,repr_recover _ U.property]
  rfl

def wordAction (U : Fin 4 → SU2) : ℝ :=
  1-QuaternionSU2Representation.halfTrace (U 0*U 1*U 2*U 3)

theorem wordAction_raw (U : Fin 4 → SU2) :
    wordAction U=rawAction (fun i => recover (U i : M2)) := by
  have he : (U 0*U 1*U 2*U 3 : SU2).val=
      QuaternionSU2Representation.repr (recover (U 0 : M2)*recover (U 1 : M2)*recover (U 2 : M2)*recover (U 3 : M2)) := by
    simp only [repr_mul,repr_recover _ (U 0).property,repr_recover _ (U 1).property,
      repr_recover _ (U 2).property,repr_recover _ (U 3).property,Submonoid.coe_mul]
  unfold wordAction QuaternionSU2Representation.halfTrace
  rw [he,repr_halfTrace]
  rfl

theorem matrix_word_odd_limit (P : ℝ → Fin 4 → SU2) (B : Fin 4 → M2)
    (h0 : ∀ i,P 0 i=1) (hp : ∀ t i,P (-t) i=(P t i)⁻¹)
    (hd : ∀ i,HasDerivAt (fun t => (P t i : M2)) (B i) 0) :
    Tendsto (fun t : ℝ => (wordAction (P t)-wordAction (P (-t)))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubic (fun i => imagVector (recover (B i))))) := by
  have hc (i : Fin 4) (a : Fin 4) :
      HasDerivAt (fun t => coordinate a (P t i : M2)) (coordinate a (B i)) 0 := by
    convert! (coordinateCLM a).hasFDerivAt.comp_hasDerivAt 0 (hd i) using 1
  have hr (i : Fin 4) : Tendsto (fun t => (recover (P t i : M2)).re) (𝓝[≠] 0) (𝓝 1) := by
    have hh := (hc i 0).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
    simpa [h0,coordinate,recover] using hh
  have hv (i : Fin 4) (a : Fin 3) :
      Tendsto (fun t => imagVector (recover (P t i : M2)) a/t) (𝓝[≠] 0)
        (𝓝 (imagVector (recover (B i)) a)) := by
    have hh := (hc i a.succ).tendsto_slope_zero
    fin_cases a <;> simpa [h0,coordinate,recover,imagVector,zero_add,smul_eq_mul,
      div_eq_mul_inv,mul_comm] using hh
  have hpar (t : ℝ) (i : Fin 4) :
      recover (P (-t) i : M2)=star (recover (P t i : M2)) := by rw [hp,recover_inverse]
  simpa only [wordAction_raw] using odd_word_limit (fun t i => recover (P t i : M2))
    (fun i => imagVector (recover (B i))) hpar hr hv
end OperatorDerivativeRewrite.Foundation.SU2QuaternionOddWord
