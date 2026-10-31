import Foundation.PeriodicFlatBackgroundHessian
import Foundation.SU2JointPlaquetteCubic
/-! Charged period-four modes of the ACTUAL flat-background Wilson spatial
Hessian. The actual adjoint phase, wrap characters, curl symbol, Hermitian
energy identity and transverse amplitude dimensions are proved. The symbol
size is a Euclidean spatial-Hessian coefficient, NOT a native stationary
transfer eigenvalue. Full Fourier completeness, global multiplicities, temporal
Gaussian integration and ground-law asymptotics are not asserted. -/
noncomputable section
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicChargedFourier
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets SU2RootAdjoint
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicFlatBackgroundHessian

def charge (u : Triple) : ℂ := (u 1 : ℂ)+(u 2 : ℂ)*Complex.I
def lift (z : ℂ) : Triple := ![0,z.re,z.im]
def phase (α : ℝ) : ℂ := ⟨Real.cos (2*α),Real.sin (2*α)⟩
def background (α : Fin 3 → ℝ) (i : Fin 3) : SU2 := SU2JointPlaquetteCubic.axis 0 (α i)

theorem lift_add (z w : ℂ) : lift (z+w)=lift z+lift w := by
  ext i
  fin_cases i <;> simp [lift]

theorem lift_sub (z w : ℂ) : lift (z-w)=lift z-lift w := by
  ext i
  fin_cases i <;> simp [lift]

theorem charge_lift (z : ℂ) : charge (lift z)=z := by
  apply Complex.ext <;> simp [charge,lift]

theorem lift_size (z : ℂ) : sizeSq (lift z)=Complex.normSq z := by
  simp [sizeSq,lift,Complex.normSq_apply]
  ring

theorem rotate_lift (α : ℝ) (z : ℂ) :
    rotate (SU2JointPlaquetteCubic.axis 0 α) (lift z)=lift (phase α*z) := by
  let c := SU2JointPlaquetteCubic.axis 0 α
  have hr : recover (c : SU2TraceHessianModel.M2)=SU2JointPlaquetteCubic.axisRaw 0 α := recover_repr _
  change ![(recover (c : SU2TraceHessianModel.M2)*(⟨0,0,z.re,z.im⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imI,
    (recover (c : SU2TraceHessianModel.M2)*(⟨0,0,z.re,z.im⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imJ,
    (recover (c : SU2TraceHessianModel.M2)*(⟨0,0,z.re,z.im⟩ : ℍ)*star (recover (c : SU2TraceHessianModel.M2))).imK]=_
  rw [hr]
  ext i
  fin_cases i <;> norm_num [SU2JointPlaquetteCubic.axisRaw,lift,phase,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,Complex.mul_re,Complex.mul_im,
    Real.cos_two_mul',Real.sin_two_mul] <;> ring

theorem background_commutes (α : Fin 3 → ℝ) (i j : Fin 3) :
    background α i*background α j=background α j*background α i := by
  unfold background SU2JointPlaquetteCubic.axis
  rw [← hom.map_mul,← hom.map_mul]
  apply congrArg hom
  apply Subtype.ext
  apply Quaternion.ext <;> norm_num [SU2JointPlaquetteCubic.axisRaw,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

def root4 (n : ZMod 4) : ℂ := Complex.I^n.val

theorem root4_zero : root4 0=1 := by norm_num [root4,ZMod.val_zero]

theorem root4_add (m n : ZMod 4) : root4 (m+n)=root4 m*root4 n := by
  have h : ∀ a b : Fin 4,Complex.I^(a+b).val=Complex.I^a.val*Complex.I^b.val := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [Fin.add_def]
  exact h m n

abbrev Frequency := Fin 3 → ZMod 4

def character (k : Frequency) (v : SpatialVertex) : ℂ := ∏ i,root4 (k i*v i)

theorem character_shift (k : Frequency) (v : SpatialVertex) (i : Fin 3) :
    character k (shift v i)=root4 (k i)*character k v := by
  fin_cases i <;> simp [character,Fin.prod_univ_succ,shift,mul_add,root4_add,root4_zero] <;> ring

theorem root4_normSq (n : ZMod 4) : Complex.normSq (root4 n)=1 := by
  simp [root4,map_pow]

theorem character_normSq (k : Frequency) (v : SpatialVertex) : Complex.normSq (character k v)=1 := by
  simp [character,Fin.prod_univ_succ,map_mul,root4_normSq]

def delta (α : Fin 3 → ℝ) (k : Frequency) (i : Fin 3) : ℂ := phase (α i)*root4 (k i)-1

def field (k : Frequency) (a : Fin 3 → ℂ) : Velocity := fun e => lift (character k e.1*a e.2)

theorem curl_symbol (α : Fin 3 → ℝ) (k : Frequency) (a : Fin 3 → ℂ)
    (v : SpatialVertex) (i j : Fin 3) :
    covariantCurl (background α) (field k a) v i j=
      lift (character k v*(delta α k i*a j-delta α k j*a i)) := by
  unfold covariantCurl field background
  rw [rotate_lift,rotate_lift,character_shift,character_shift,← lift_add,← lift_sub,← lift_sub]
  congr 1
  unfold delta
  ring


open PeriodicConstantQuarticJet (Pair3)

private def faceEquiv : SpatialFace ≃ SpatialVertex × Pair3 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairEnergy (d a : Fin 3 → ℂ) : ℝ :=
  ∑ p : Pair3,Complex.normSq (d p.val.1*a p.val.2-d p.val.2*a p.val.1)

def total (a : Fin 3 → ℂ) : ℝ := ∑ i,Complex.normSq (a i)
def longitudinal (d a : Fin 3 → ℂ) : ℂ := ∑ i,starRingEnd ℂ (d i)*a i

theorem quadratic_mode (α : Fin 3 → ℝ) (k : Frequency) (a : Fin 3 → ℂ) :
    PeriodicFlatBackgroundHessian.quadratic (background α) (field k a)=64*pairEnergy (delta α k) a := by
  unfold PeriodicFlatBackgroundHessian.quadratic
  simp_rw [curl_symbol,lift_size,map_mul,character_normSq,one_mul]
  rw [← faceEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type,faceEquiv,Equiv.coe_fn_symm_mk]
  simp only [Finset.sum_const,Finset.card_univ]
  norm_num only [SpatialVertex,Fintype.card_fun,Fintype.card_fin,ZMod.card,show 4^3=64 by norm_num]
  unfold pairEnergy
  ring

theorem field_size (k : Frequency) (a : Fin 3 → ℂ) :
    (∑ e : SpatialEdge,sizeSq (field k a e))=64*total a := by
  unfold field
  simp_rw [lift_size,map_mul,character_normSq,one_mul]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ]
  norm_num only [SpatialVertex,Fintype.card_fun,Fintype.card_fin,ZMod.card,show 4^3=64 by norm_num]
  norm_num [total,nsmul_eq_mul]

theorem hermitian_curl_identity (d a : Fin 3 → ℂ) :
    pairEnergy d a=total d*total a-Complex.normSq (longitudinal d a) := by
  have hp : (Finset.univ : Finset Pair3)=
      {⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(1,2),by decide⟩} := by decide
  unfold pairEnergy total longitudinal
  rw [hp]
  norm_num [Finset.sum_insert,Fin.sum_univ_succ,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  <;> ring

def symbolSize (α : Fin 3 → ℝ) (k : Frequency) : ℝ := total (delta α k)

theorem transverse_second (α : Fin 3 → ℝ) (k : Frequency) (a : Fin 3 → ℂ)
    (ha : longitudinal (delta α k) a=0) :
    deriv (deriv (fun t : ℝ => spatialAction (state (background α) (field k a) t))) 0=
      symbolSize α k*(∑ e : SpatialEdge,sizeSq (field k a e)) := by
  rw [spatial_second _ _ (background_commutes α),quadratic_mode,hermitian_curl_identity,ha]
  simp only [map_zero,sub_zero]
  rw [field_size]
  unfold symbolSize
  ring

theorem gauge_symbol (α : Fin 3 → ℝ) (k : Frequency) (c : ℂ) :
    gaugeGradient (background α) (fun v => lift (character k v*c))=
      field k (fun i => -delta α k i*c) := by
  funext e
  unfold gaugeGradient field background
  rw [rotate_lift,character_shift,← lift_sub]
  congr 1
  unfold delta
  ring

theorem phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  apply Complex.ext <;> simp [phase,mul_add,Real.cos_add,Real.sin_add,Complex.mul_re,Complex.mul_im] <;> ring

theorem phase_nat_mul (α : ℝ) (n : ℕ) : phase ((n : ℝ)*α)=phase α^n := by
  induction n with
  | zero => apply Complex.ext <;> simp [phase]
  | succ n ih =>
    have he : ((n+1 : ℕ) : ℝ)*α=(n : ℝ)*α+α := by push_cast; ring
    rw [he,phase_add,ih,pow_succ]

theorem phase_quarter_pi : phase (Real.pi/4)=Complex.I := by
  have he : 2*(Real.pi/4)=Real.pi/2 := by ring
  apply Complex.ext <;> simp [phase,he]

theorem root4_phase (n : ZMod 4) : root4 n=phase (Real.pi*(n.val : ℝ)/4) := by
  have he : Real.pi*(n.val : ℝ)/4=(n.val : ℝ)*(Real.pi/4) := by ring
  rw [he,phase_nat_mul,phase_quarter_pi]
  rfl

theorem phase_defect (α : ℝ) : Complex.normSq (phase α-1)=4*Real.sin α^2 := by
  norm_num [phase,Complex.normSq_apply,Real.cos_two_mul,Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq α]

theorem delta_sine (α : Fin 3 → ℝ) (k : Frequency) (i : Fin 3) :
    Complex.normSq (delta α k i)=4*Real.sin (α i+Real.pi*((k i).val : ℝ)/4)^2 := by
  unfold delta
  rw [root4_phase,← phase_add,phase_defect]

theorem symbolSize_sine (α : Fin 3 → ℝ) (k : Frequency) :
    symbolSize α k=4*∑ i,Real.sin (α i+Real.pi*((k i).val : ℝ)/4)^2 := by
  unfold symbolSize total
  simp_rw [delta_sine]
  rw [Finset.mul_sum]


def longitudinalMap (d : Fin 3 → ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun := longitudinal d
  map_add' a b := by simp [longitudinal,mul_add,Finset.sum_add_distrib]
  map_smul' r a := by
    change (∑ i,starRingEnd ℂ (d i)*(r*a i))=r*∑ i,starRingEnd ℂ (d i)*a i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem longitudinal_surjective (d : Fin 3 → ℂ) (hd : ∃ i,d i≠0) :
    Function.Surjective (longitudinalMap d) := by
  obtain ⟨j,hj⟩ := hd
  have hs : starRingEnd ℂ (d j)≠0 := by simpa using hj
  intro z
  refine ⟨(fun i => if i=j then z/starRingEnd ℂ (d j) else 0),?_⟩
  change (∑ i,starRingEnd ℂ (d i)*(if i=j then z/starRingEnd ℂ (d j) else 0))=z
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp

theorem transverse_finrank (d : Fin 3 → ℂ) (hd : ∃ i,d i≠0) :
    Module.finrank ℂ (LinearMap.ker (longitudinalMap d))=2 := by
  have h := (longitudinalMap d).finrank_range_add_finrank_ker
  have hr : LinearMap.range (longitudinalMap d)=⊤ :=
    LinearMap.range_eq_top.mpr (longitudinal_surjective d hd)
  have hv : Module.finrank ℂ (Fin 3 → ℂ)=3 := by simp
  have hrr : Module.finrank ℂ (LinearMap.range (longitudinalMap d))=1 := by rw [hr]; simp
  omega

theorem symbolSize_nonneg (α : Fin 3 → ℝ) (k : Frequency) : 0≤symbolSize α k := by
  unfold symbolSize total
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (delta α k i))

theorem symbolSize_zero_iff (α : Fin 3 → ℝ) (k : Frequency) :
    symbolSize α k=0 ↔ ∀ i,delta α k i=0 := by
  constructor
  · intro h i
    have he := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => Complex.normSq_nonneg (delta α k j))
      (Finset.mem_univ i)
    change Complex.normSq (delta α k i)≤symbolSize α k at he
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (he.trans_eq h) (Complex.normSq_nonneg _)
  · intro h
    simp [symbolSize,total,h]

theorem mode_transverse_dimension (α : Fin 3 → ℝ) (k : Frequency) (hEig : 0<symbolSize α k) :
    Module.finrank ℂ (LinearMap.ker (longitudinalMap (delta α k)))=2 := by
  apply transverse_finrank
  by_contra h
  push Not at h
  have hz := (symbolSize_zero_iff α k).mpr h
  linarith

theorem zero_mode_dimension (α : Fin 3 → ℝ) (k : Frequency) (hEig : symbolSize α k=0) :
    Module.finrank ℂ (LinearMap.ker (longitudinalMap (delta α k)))=3 := by
  have hd := (symbolSize_zero_iff α k).mp hEig
  have he : longitudinalMap (delta α k)=0 := by
    apply LinearMap.ext
    intro a
    change longitudinal (delta α k) a=0
    simp [longitudinal,hd]
  rw [he,LinearMap.ker_zero]
  simp

theorem root4_four (n : ZMod 4) : root4 n^4=1 := by
  calc
    _ = (Complex.I^4)^n.val := by
      unfold root4
      simp only [← pow_mul]
      congr 1
      omega
    _ = _ := by norm_num

theorem symbolSize_pos_of_holonomy (α : Fin 3 → ℝ) (k : Frequency)
    (h : ∃ i,phase (α i)^4≠1) : 0<symbolSize α k := by
  by_contra hnot
  have hz : symbolSize α k=0 := le_antisymm (le_of_not_gt hnot) (symbolSize_nonneg α k)
  obtain ⟨i,hi⟩ := h
  have he : phase (α i)*root4 (k i)=1 := sub_eq_zero.mp ((symbolSize_zero_iff α k).mp hz i)
  have hp := congrArg (fun z : ℂ => z^4) he
  rw [mul_pow,root4_four,mul_one,one_pow] at hp
  exact hi hp

theorem parallel_energy_zero (d : Fin 3 → ℂ) (c : ℂ) : pairEnergy d (fun i => d i*c)=0 := by
  unfold pairEnergy
  apply Finset.sum_eq_zero
  intro p _
  have he : d p.val.1*(d p.val.2*c)-d p.val.2*(d p.val.1*c)=0 := by ring
  rw [he,map_zero]

theorem field_injective (k : Frequency) : Function.Injective (field k) := by
  intro a b h
  funext i
  have he := congrArg (fun X : Velocity => charge (X ((fun _ => 0),i))) h
  simpa only [field,charge_lift,character,mul_zero,root4_zero,Finset.prod_const_one,one_mul] using he


theorem winding_transport (α : Fin 3 → ℝ) (i : Fin 3) (z : ℂ) :
    rotate (PeriodicSpatialHolonomy.winding (fun e => background α e.2) (fun _ => 0) i) (lift z)=
      lift (phase (α i)^4*z) := by
  change rotate (background α i*background α i*background α i*background α i) (lift z)=_
  rw [PeriodicFlatBackgroundHessian.rotate_mul,PeriodicFlatBackgroundHessian.rotate_mul,
    PeriodicFlatBackgroundHessian.rotate_mul]
  simp only [background,rotate_lift]
  congr 1
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicChargedFourier
