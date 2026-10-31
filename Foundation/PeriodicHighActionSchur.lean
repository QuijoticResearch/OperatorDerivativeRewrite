import Foundation.PeriodicHighActionL2
/-! Exact high-sector elimination for the actual stationary Wilson operator.
The low sector is the orthogonal complement of the explicitly completed high
domain. No global gap or hard-indicator identification is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicHighActionSchur
open PeriodicSlabGround PeriodicSlabL2 PeriodicHighActionL2
open SelfAdjointContractionIteration

def threshold : ℝ := Real.log (2*(PeriodicGroundHaarScale.upperConstant/
  PeriodicGaugeSaturatedGround.eigenLowerConstant))
abbrev High {β : ℝ} (g : GroundData β) := completed g threshold
abbrev low {β : ℝ} (g : GroundData β) : Submodule ℝ (StateL2 g) := (High g).toSubmoduleᗮ
def cross {β : ℝ} (g : GroundData β) : low g →L[ℝ] High g :=
  (High g).toSubmodule.orthogonalProjectionOnto.comp ((operator g).comp (low g).subtypeL)
def lowCompression {β : ℝ} (g : GroundData β) : low g →L[ℝ] low g :=
  (low g).orthogonalProjectionOnto.comp ((operator g).comp (low g).subtypeL)
def schur {β : ℝ} (g : GroundData β) (R : High g →L[ℝ] High g) : low g →L[ℝ] low g :=
  1-lowCompression g-(cross g).adjoint.comp (R.comp (cross g))
def harmonic {β : ℝ} (g : GroundData β) (R : High g →L[ℝ] High g) : low g →L[ℝ] StateL2 g :=
  (low g).subtypeL+(High g).toSubmodule.subtypeL.comp (R.comp (cross g))

attribute [local irreducible] represented completed
variable {β : ℝ} (g : GroundData β)

private theorem cross_pairing (x : low g) (y : High g) :
    inner ℝ (cross g x) y=inner ℝ (operator g (x : StateL2 g)) (y : StateL2 g) := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right y _
private theorem low_orthogonal (x : low g) (y : High g) :
    inner ℝ (x : StateL2 g) (y : StateL2 g)=0 := by
  rw [real_inner_comm]
  exact ((High g).toSubmodule.mem_orthogonal _).mp x.property y y.property

theorem high_coercivity (hb : 16777216 ≤ β) (y : High g) :
    (1/2 : ℝ)*‖y‖^2 ≤ dissipation (operator g) (y : StateL2 g) := by
  have hN := compression_half hb g
  have h := real_inner_le_norm (compression g threshold y) y
  have hA := (compression g threshold).le_opNorm y
  have hB := mul_le_mul_of_nonneg_right hN (norm_nonneg y)
  rw [compression_pairing] at h
  unfold dissipation
  rw [real_inner_self_eq_norm_sq]
  change (1/2 : ℝ)*‖(y : StateL2 g)‖^2 ≤ _
  have he : ‖(y : StateL2 g)‖=‖y‖ := rfl
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right (hA.trans hB) (norm_nonneg y)]

private theorem energy_split (x : low g) (y : High g) :
    dissipation (operator g) ((x : StateL2 g)+(y : StateL2 g))=
      dissipation (operator g) (x : StateL2 g)-2*inner ℝ (cross g x) y+
        dissipation (operator g) (y : StateL2 g) := by
  have ho := low_orthogonal g x y
  have hs := operator_symmetric g (y : StateL2 g) (x : StateL2 g)
  rw [real_inner_comm (operator g (x : StateL2 g)) (y : StateL2 g)] at hs
  simp only [dissipation,map_add,inner_add_left,inner_add_right,ho,
    real_inner_comm (x : StateL2 g) (y : StateL2 g),hs,← cross_pairing g x y]
  ring

private theorem high_pairing (y z : High g) :
    inner ℝ ((1-compression g threshold) y) z=
      inner ℝ (y : StateL2 g) (z : StateL2 g)-
        inner ℝ (operator g (y : StateL2 g)) (z : StateL2 g) := by
  simp only [sub_apply,one_apply_eq_self,inner_sub_left,
    compression_pairing]
  rfl

theorem schur_pairing (R : High g →L[ℝ] High g) (x z : low g) :
    inner ℝ (schur g R x) z=
      inner ℝ (x : StateL2 g) (z : StateL2 g)-
        inner ℝ (operator g (x : StateL2 g)) (z : StateL2 g)-
          inner ℝ (R (cross g x)) (cross g z) := by
  simp only [schur,sub_apply,one_apply_eq_self,
    ContinuousLinearMap.comp_apply,inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  rw [show inner ℝ (lowCompression g x) z=inner ℝ (operator g (x : StateL2 g)) (z : StateL2 g) from
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right z _]
  rfl

private theorem energy_sub (u v : StateL2 g) :
    dissipation (operator g) (u-v)=dissipation (operator g) u+dissipation (operator g) v-
      2*(inner ℝ v u-inner ℝ (operator g v) u) := by
  have hs := operator_symmetric g u v
  rw [real_inner_comm (operator g v) u] at hs
  simp only [dissipation,map_sub,inner_sub_left,inner_sub_right]
  rw [real_inner_comm v u,hs]
  ring

attribute [local irreducible] operator compression cross lowCompression schur harmonic

/-- The actual completed-square identity with the full mixed correction retained. -/
theorem completed_square (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) (y : High g) :
    dissipation (operator g) ((x : StateL2 g)+(y : StateL2 g))=
      inner ℝ (schur g R x) x+
        dissipation (operator g) ((y-R (cross g x) : High g) : StateL2 g) := by
  have hr := congrArg (fun T : High g →L[ℝ] High g => T (cross g x)) hR
  change (1-compression g threshold) (R (cross g x))=cross g x at hr
  have hpair := high_pairing g (R (cross g x)) y
  have hself := high_pairing g (R (cross g x)) (R (cross g x))
  rw [hr] at hpair hself
  have he := energy_sub g (y : StateL2 g) (R (cross g x) : StateL2 g)
  change inner ℝ (cross g x) (R (cross g x))=
    dissipation (operator g) (R (cross g x) : StateL2 g) at hself
  have hS := schur_pairing g R x x
  change inner ℝ (schur g R x) x=dissipation (operator g) (x : StateL2 g)-
    inner ℝ (R (cross g x)) (cross g x) at hS
  change dissipation (operator g) ((y-R (cross g x) : High g) : StateL2 g)=
    dissipation (operator g) (y : StateL2 g)+
    dissipation (operator g) (R (cross g x) : StateL2 g)-
    2*(inner ℝ (R (cross g x) : StateL2 g) (y : StateL2 g)-
      inner ℝ (operator g (R (cross g x) : StateL2 g)) (y : StateL2 g)) at he
  have hc := real_inner_comm (cross g x) (R (cross g x))
  rw [energy_split]
  linarith only [he,hpair,hself,hS,hc]

theorem harmonic_energy (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) :
    dissipation (operator g) (harmonic g R x)=inner ℝ (schur g R x) x := by
  have h := completed_square g R hR x (R (cross g x))
  simpa only [harmonic,add_apply,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,sub_self,Submodule.coe_zero,dissipation,map_zero,
    inner_zero_left,inner_zero_right,sub_zero,add_zero] using h

theorem schur_nonnegative (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) :
    0 ≤ inner ℝ (schur g R x) x := by
  rw [← harmonic_energy g R hR x]
  exact dissipation_nonneg (operator g) (operator_contraction g) (operator_symmetric g) _

theorem variational_remainder (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) (y : High g) :
    inner ℝ (schur g R x) x+(1/2 : ℝ)*‖y-R (cross g x)‖^2 ≤
      dissipation (operator g) ((x : StateL2 g)+(y : StateL2 g)) := by
  rw [completed_square g R hR]
  exact add_le_add_right (high_coercivity g hb _) _

/-- The Neumann inverse is symmetric on the actual completed high space. -/
theorem resolvent_symmetric (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) : R.IsSymmetric := by
  have hi (u : High g) : (1-compression g threshold) (R u)=u :=
    congrArg (fun T : High g →L[ℝ] High g => T u) hR
  have hD : (1-compression g threshold).IsSymmetric := by
    intro u v
    change inner ℝ ((1-compression g threshold) u) v=inner ℝ u ((1-compression g threshold) v)
    simp only [sub_apply,one_apply_eq_self,inner_sub_left,inner_sub_right]
    have hC := compression_symmetric g threshold u v
    change inner ℝ (compression g threshold u) v=inner ℝ u (compression g threshold v) at hC
    exact congrArg (fun a : ℝ => inner ℝ u v-a) hC
  intro u v
  calc
    inner ℝ (R u) v = inner ℝ (R u) ((1-compression g threshold) (R v)) := by rw [hi]
    _ = inner ℝ ((1-compression g threshold) (R u)) (R v) := (hD _ _).symm
    _ = inner ℝ u (R v) := by rw [hi]

theorem schur_symmetric (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) : (schur g R).IsSymmetric := by
  intro x z
  change inner ℝ (schur g R x) z=inner ℝ x (schur g R z)
  rw [schur_pairing,real_inner_comm (schur g R z) x,schur_pairing]
  have hP := operator_symmetric g (x : StateL2 g) (z : StateL2 g)
  have hInv := resolvent_symmetric g R hR (cross g x) (cross g z)
  rw [real_inner_comm (operator g (z : StateL2 g)) (x : StateL2 g)] at hP
  change inner ℝ (R (cross g x)) (cross g z)=inner ℝ (cross g x) (R (cross g z)) at hInv
  rw [real_inner_comm (R (cross g z)) (cross g x)] at hInv
  rw [real_inner_comm (x : StateL2 g) (z : StateL2 g)]
  linarith only [hP,hInv]

/-- The coupling correction is positive and at most twice its native squared norm. -/
theorem coupling_cost (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (hN : ‖R‖ ≤ 2) (b : High g) :
    0 ≤ inner ℝ (R b) b ∧ inner ℝ (R b) b ≤ 2*‖b‖^2 := by
  have hi := congrArg (fun T : High g →L[ℝ] High g => T b) hR
  change (1-compression g threshold) (R b)=b at hi
  have he := high_pairing g (R b) (R b)
  rw [hi] at he
  change inner ℝ b (R b)=dissipation (operator g) (R b : StateL2 g) at he
  have hc := high_coercivity g hb (R b)
  have hn := (R.le_opNorm b).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg b))
  have hcs := real_inner_le_norm (R b) b
  rw [real_inner_comm (R b) b] at he
  constructor
  · nlinarith only [he,hc,sq_nonneg ‖R b‖]
  · nlinarith only [hcs,mul_le_mul_of_nonneg_right hn (norm_nonneg b)]

theorem schur_energy_bounds (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (hN : ‖R‖ ≤ 2) (x : low g) :
    dissipation (operator g) (x : StateL2 g)-2*‖cross g x‖^2 ≤ inner ℝ (schur g R x) x ∧
      inner ℝ (schur g R x) x ≤ dissipation (operator g) (x : StateL2 g) := by
  have h := coupling_cost g hb R hR hN (cross g x)
  rw [schur_pairing]
  unfold dissipation
  constructor <;> linarith only [h.1,h.2]

/-- Exact minimum, with uniqueness supplied by the genuine high-sector coercivity. -/
theorem unique_minimizer (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) :
    ∃! y : High g,dissipation (operator g) ((x : StateL2 g)+(y : StateL2 g))=
      inner ℝ (schur g R x) x := by
  have hm := harmonic_energy g R hR x
  simp only [harmonic,add_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply] at hm
  refine ⟨R (cross g x),hm,?_⟩
  intro y hy
  have h := variational_remainder g hb R hR x y
  rw [hy] at h
  have hz : ‖y-R (cross g x)‖=0 := by nlinarith only [h,sq_nonneg ‖y-R (cross g x)‖,norm_nonneg (y-R (cross g x))]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Exact high projection of the FULL original-operator residual. -/
theorem high_residual (x : low g) (y : High g) :
    (High g).toSubmodule.orthogonalProjectionOnto
      (((x : StateL2 g)+(y : StateL2 g))-operator g ((x : StateL2 g)+(y : StateL2 g)))=
        (1-compression g threshold) y-cross g x := by
  let Q := (High g).toSubmodule.orthogonalProjectionOnto
  have hx : Q (x : StateL2 g)=0 :=
    (High g).toSubmodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.property
  have hy : Q (y : StateL2 g)=y :=
    (High g).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self y
  have hxP : Q (operator g (x : StateL2 g))=cross g x := by unfold cross; rfl
  have hyP : Q (operator g (y : StateL2 g))=compression g threshold y := by unfold compression; rfl
  change Q (((x : StateL2 g)+(y : StateL2 g))-operator g ((x : StateL2 g)+(y : StateL2 g)))=_
  simp only [map_sub,map_add,hx,hy,hxP,hyP,zero_add,sub_apply,one_apply_eq_self]
  abel

theorem residual_identity (R : High g →L[ℝ] High g)
    (hR : R*(1-compression g threshold)=1) (x : low g) (y : High g) :
    y-R (cross g x)=R ((High g).toSubmodule.orthogonalProjectionOnto
      (((x : StateL2 g)+(y : StateL2 g))-operator g ((x : StateL2 g)+(y : StateL2 g)))) := by
  rw [high_residual,map_sub]
  have hi := congrArg (fun T : High g →L[ℝ] High g => T y) hR
  change R ((1-compression g threshold) y)=y at hi
  rw [hi]

/-- Every near1 vector of the ORIGINAL operator lies near its low harmonic lift.
No assertion identifying projected powers with native evolution is needed. -/
theorem residual_control (R : High g →L[ℝ] High g)
    (hR : R*(1-compression g threshold)=1) (hN : ‖R‖ ≤ 2) (x : low g) (y : High g) :
    ‖y-R (cross g x)‖ ≤
      2*‖((x : StateL2 g)+(y : StateL2 g))-operator g ((x : StateL2 g)+(y : StateL2 g))‖ := by
  rw [residual_identity g R hR]
  exact (R.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hN (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left ((High g).toSubmodule.norm_orthogonalProjectionOnto_apply_le _) (by norm_num)))

/-- Every ambient native vector has this exact orthogonal decomposition. -/
theorem native_decomposition (v : StateL2 g) :
    ∃ x : low g,∃ y : High g,(x : StateL2 g)+(y : StateL2 g)=v := by
  obtain ⟨y,hy,x,hx,he⟩ := (High g).toSubmodule.exists_add_mem_mem_orthogonal v
  exact ⟨⟨x,hx⟩,⟨y,hy⟩,by simpa only [add_comm] using he.symm⟩

/-- Native zero-energy vectors survive exactly on the low harmonic manifold. -/
theorem zero_energy_lift (hb : 16777216 ≤ β) (R : High g →L[ℝ] High g)
    (hR : (1-compression g threshold)*R=1) (x : low g) (y : High g)
    (he : dissipation (operator g) ((x : StateL2 g)+(y : StateL2 g))=0) :
    y=R (cross g x) ∧ inner ℝ (schur g R x) x=0 := by
  have hS := schur_nonnegative g R hR x
  have h := variational_remainder g hb R hR x y
  rw [he] at h
  have hz : ‖y-R (cross g x)‖=0 := by nlinarith only [h,hS,sq_nonneg ‖y-R (cross g x)‖,norm_nonneg (y-R (cross g x))]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hz),by nlinarith only [h,hS,sq_nonneg ‖y-R (cross g x)‖]⟩

end OperatorDerivativeRewrite.Foundation.PeriodicHighActionSchur
