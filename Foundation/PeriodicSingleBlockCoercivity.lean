import Foundation.PeriodicInteriorGaugeKernel
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The actual single-origin-block incidence embedded in the periodic lattice.
Three distinct exterior plaquettes per local edge supply a coercivity bound. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicSingleBlockCoercivity
open PeriodicInteriorGaugeKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

def localEdge (e : Edge) : Prop := block e.1=0 ∧ interior e
instance localEdge_decidable (e : Edge) : Decidable (localEdge e) :=
  inferInstanceAs (Decidable (block e.1=0 ∧ interior e))
abbrev Local := {e : Edge // localEdge e}
abbrev Exterior := (e : Local) × {j : Direction // j ≠ e.val.2}

theorem local_card : Fintype.card Local=32 := by decide
theorem exterior_card : Fintype.card Exterior=96 := by decide

def localExtend : (Local → ℝ) →ₗ[ℝ] (Edge → ℝ) where
  toFun f e := if he : localEdge e then f ⟨e,he⟩ else 0
  map_add' f g := by ext e; by_cases he : localEdge e <;> simp [he]
  map_smul' r f := by ext e; by_cases he : localEdge e <;> simp [he]

def localIncidence : (Local → ℝ) →ₗ[ℝ] (Face → ℝ) := incidence.comp localExtend

def exteriorBase (a : Exterior) : Vertex :=
  if a.1.val.1 a.2.val=0 then shift (shift (shift a.1.val.1 a.2.val) a.2.val) a.2.val else a.1.val.1

def exteriorFace (a : Exterior) : Face :=
  if hij : a.1.val.2 < a.2.val then ⟨(exteriorBase a,(a.1.val.2,a.2.val)),hij⟩
  else ⟨(exteriorBase a,(a.2.val,a.1.val.2)),lt_of_le_of_ne (le_of_not_gt hij) a.2.property⟩

def exteriorSign (a : Exterior) : ℤ :=
  (if a.1.val.2 < a.2.val then 1 else -1)*(if a.1.val.1 a.2.val=0 then -1 else 1)

def coefficient (p : Face) (e : Edge) : ℤ :=
  (if e=(p.val.1,p.val.2.1) then 1 else 0)+
  (if e=(shift p.val.1 p.val.2.1,p.val.2.2) then 1 else 0)-
  (if e=(shift p.val.1 p.val.2.2,p.val.2.1) then 1 else 0)-
  (if e=(p.val.1,p.val.2.2) then 1 else 0)

theorem exteriorFace_injective : Function.Injective exteriorFace := by decide

theorem exterior_coefficient : ∀ a : Exterior, ∀ e : Local,
    coefficient (exteriorFace a) e.val=if e=a.1 then exteriorSign a else 0 := by decide

theorem exteriorSign_square (a : Exterior) : (exteriorSign a)^2=1 := by
  unfold exteriorSign
  split_ifs <;> norm_num

theorem other_directions_card (i : Direction) : Fintype.card {j : Direction // j ≠ i}=3 := by
  fin_cases i <;> decide

theorem localExtend_single (e : Local) : localExtend (Pi.single e (1 : ℝ))=Pi.single e.val 1 := by
  funext k
  by_cases hk : localEdge k
  · simp [localExtend,hk,Pi.single_apply,Subtype.ext_iff]
  · have hne : e.val ≠ k := by
      intro he
      exact hk (he ▸ e.property)
    simp [localExtend,hk,Pi.single_apply,hne]

theorem localIncidence_single (p : Face) (e : Local) :
    localIncidence (Pi.single e (1 : ℝ)) p=(coefficient p e.val : ℝ) := by
  change incidence (localExtend (Pi.single e (1 : ℝ))) p=_
  rw [localExtend_single]
  simp [incidence,curl,coefficient,Pi.single_apply,eq_comm]

theorem localIncidence_expansion (f : Local → ℝ) (p : Face) :
    localIncidence f p=∑ e : Local, (coefficient p e.val : ℝ)*f e := by
  have hf : f=∑ e : Local, f e • Pi.single e (1 : ℝ) := by
    funext e
    simp [Pi.single_apply,mul_ite]
  conv_lhs => rw [hf,map_sum]
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul,localIncidence_single]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem exterior_row (f : Local → ℝ) (a : Exterior) :
    localIncidence f (exteriorFace a)=(exteriorSign a : ℝ)*f a.1 := by
  rw [localIncidence_expansion]
  simp only [exterior_coefficient]
  push_cast
  simp

theorem exterior_row_square (f : Local → ℝ) (a : Exterior) :
    (localIncidence f (exteriorFace a))^2=(f a.1)^2 := by
  rw [exterior_row,mul_pow]
  have hs : (exteriorSign a : ℝ)^2=1 := by exact_mod_cast exteriorSign_square a
  rw [hs,one_mul]

def squaredSize (f : Local → ℝ) : ℝ := ∑ e, (f e)^2
def energy (f : Local → ℝ) : ℝ := ∑ p : Face, (localIncidence f p)^2

theorem exterior_sum (f : Local → ℝ) :
    (∑ a : Exterior, (localIncidence f (exteriorFace a))^2)=3*squaredSize f := by
  simp_rw [exterior_row_square]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,other_directions_card,nsmul_eq_mul]
  unfold squaredSize
  rw [Finset.mul_sum]
  norm_num

theorem exterior_sum_le_energy (f : Local → ℝ) :
    (∑ a : Exterior, (localIncidence f (exteriorFace a))^2) ≤ energy f := by
  calc
    _ = ∑ p ∈ Finset.univ.image exteriorFace, (localIncidence f p)^2 := by
      rw [Finset.sum_image (fun a _ b _ he => exteriorFace_injective he)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => sq_nonneg (localIncidence f p))

theorem energy_coercive (f : Local → ℝ) : 3*squaredSize f ≤ energy f := by
  rw [← exterior_sum]
  exact exterior_sum_le_energy f

theorem localIncidence_injective : Function.Injective localIncidence := by
  intro f g hfg
  have hz : localIncidence (f-g)=0 := by rw [map_sub,hfg,sub_self]
  have he := energy_coercive (f-g)
  have he0 : energy (f-g)=0 := by simp [energy,hz]
  rw [he0] at he
  have hs : squaredSize (f-g)=0 := by
    have hn : 0 ≤ squaredSize (f-g) := Finset.sum_nonneg (fun e _ => sq_nonneg _)
    linarith
  have hz' : ∀ e : Local, ((f-g) e)^2=0 := by
    intro e
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg ((f-g) e))).mp hs e (Finset.mem_univ _)
  funext e
  have hh := hz' e
  simp only [Pi.sub_apply] at hh
  nlinarith

def localMatrix : Matrix Face Local ℝ := LinearMap.toMatrix' localIncidence
def localHessian : Matrix Local Local ℝ := localMatrix.transpose*localMatrix

theorem localMatrix_mulVec (f : Local → ℝ) : localMatrix.mulVec f=localIncidence f :=
  LinearMap.toMatrix'_mulVec _ _

theorem hessian_energy (f : Local → ℝ) :
    (∑ e, f e*(localHessian.mulVec f) e)=energy f := by
  change dotProduct f (localHessian.mulVec f)=energy f
  rw [localHessian,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [localMatrix_mulVec,dotProduct,energy,pow_two]

theorem hessian_coercive (f : Local → ℝ) :
    3*squaredSize f ≤ ∑ e, f e*(localHessian.mulVec f) e := by
  rw [hessian_energy]
  exact energy_coercive f

theorem squaredSize_zero_iff (f : Local → ℝ) : squaredSize f=0 ↔ f=0 := by
  constructor
  · intro h
    have hz : ∀ e : Local, (f e)^2=0 := by
      intro e
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (f e))).mp h e (Finset.mem_univ _)
    funext e
    have hh := hz e
    change f e=0
    nlinarith
  · intro h
    simp [h,squaredSize]

theorem localHessian_injective : Function.Injective localHessian.mulVec := by
  intro f g hfg
  have hz : localHessian.mulVec (f-g)=0 := by rw [Matrix.mulVec_sub,hfg,sub_self]
  have he := hessian_coercive (f-g)
  rw [hz] at he
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at he
  have hs : squaredSize (f-g)=0 := by
    have hn : 0 ≤ squaredSize (f-g) := Finset.sum_nonneg (fun e _ => sq_nonneg _)
    linarith
  exact sub_eq_zero.mp ((squaredSize_zero_iff _).mp hs)

theorem localHessian_isUnit : IsUnit localHessian := Matrix.mulVec_injective_iff_isUnit.mp localHessian_injective

def intStar (e : Edge) : ℤ := if e.1=origin then 1 else 0
def star (e : Local) : ℝ := (intStar e.val : ℝ)

theorem intStar_outside : ∀ e : Edge, ¬ localEdge e → intStar e=0 := by decide
theorem intStar_norm : (∑ e : Local, (intStar e.val)^2)=4 := by decide
theorem intStar_energy : (∑ p : Face, (intCurl intStar p.val.1 p.val.2.1 p.val.2.2)^2)=12 := by decide

theorem star_extend : localExtend star=fun e => (intStar e : ℝ) := by
  funext e
  by_cases he : localEdge e
  · simp [localExtend,star,he]
  · simp [localExtend,he,intStar_outside e he]

theorem star_norm : squaredSize star=4 := by
  unfold squaredSize star
  exact_mod_cast intStar_norm

theorem star_energy : energy star=12 := by
  have hc (p : Face) : localIncidence star p=(intCurl intStar p.val.1 p.val.2.1 p.val.2.2 : ℝ) := by
    change incidence (localExtend star) p=_
    rw [star_extend]
    simp [incidence,curl,intCurl]
  unfold energy
  simp_rw [hc]
  exact_mod_cast intStar_energy

theorem sharp_rayleigh : energy star/squaredSize star=3 := by
  rw [star_energy,star_norm]
  norm_num

theorem no_stronger_coercivity (c : ℝ) (hc : 3 < c) :
    ¬ (∀ f : Local → ℝ, c*squaredSize f ≤ energy f) := by
  intro h
  have he := h star
  rw [star_norm,star_energy] at he
  linarith

def reducedHessian : Matrix Local Local ℝ := localHessian-3

theorem reduced_form (f : Local → ℝ) :
    dotProduct f (reducedHessian.mulVec f)=energy f-3*squaredSize f := by
  rw [reducedHessian,Matrix.sub_mulVec,Matrix.ofNat_mulVec,dotProduct_sub]
  change (∑ e, f e*(localHessian.mulVec f) e)-(∑ e, f e*(3*f e))=_
  rw [hessian_energy]
  have he : (∑ e, f e*(3*f e))=3*squaredSize f := by
    unfold squaredSize
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he]

theorem reducedHessian_posSemidef : reducedHessian.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (localHessian-(3 : Matrix Local Local ℝ)).IsHermitian
    have hc : localHessian.IsHermitian := by
      simpa [localHessian] using Matrix.isHermitian_conjTranspose_mul_self localMatrix
    exact hc.sub (Matrix.isHermitian_natCast 3)
  · intro f
    change 0 ≤ dotProduct f (reducedHessian.mulVec f)
    rw [reduced_form]
    have he := energy_coercive f
    linarith

theorem star_eigenvalue_three : localHessian.mulVec star=(3 : ℝ) • star := by
  have hz : dotProduct star (reducedHessian.mulVec star)=0 := by
    rw [reduced_form,star_energy,star_norm]
    norm_num
  have he : reducedHessian.mulVec star=0 :=
    reducedHessian_posSemidef.dotProduct_mulVec_zero_iff.mp (by simpa using hz)
  rw [reducedHessian,Matrix.sub_mulVec,Matrix.ofNat_mulVec] at he
  exact sub_eq_zero.mp he

theorem star_nonzero : star ≠ 0 := by
  intro h
  have he := star_norm
  simp [h,squaredSize] at he

theorem eigenvalue_three_exists :
    ∃ f : Local → ℝ, f ≠ 0 ∧ localHessian.mulVec f=(3 : ℝ) • f :=
  ⟨star,star_nonzero,star_eigenvalue_three⟩

end OperatorDerivativeRewrite.Foundation.PeriodicSingleBlockCoercivity
