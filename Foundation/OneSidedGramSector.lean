import Foundation.OneSidedBlockRank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A concrete Gram action and an exact rational two-dimensional sector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedGramSector
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

def innerMap : Field →ₗ[ℝ] (Inner → ℝ) :=
  (LinearMap.fst ℝ (Inner → ℝ) (Upper → ℝ)).comp incidence

def upperMap : Field →ₗ[ℝ] (Upper → ℝ) :=
  (LinearMap.snd ℝ (Inner → ℝ) (Upper → ℝ)).comp incidence

def innerMatrix : Matrix Inner Interior ℝ := LinearMap.toMatrix' innerMap
def upperMatrix : Matrix Upper Interior ℝ := LinearMap.toMatrix' upperMap
def gram : Matrix Interior Interior ℝ :=
  innerMatrix.transpose*innerMatrix+upperMatrix.transpose*upperMatrix

def coefficient (p : Inner) (e : Interior) : ℤ :=
  (if e.val=(p.val.1,p.val.2.1) then 1 else 0)+
    (if e.val=(shifted p.val.1 p.val.2.1,p.val.2.2) then 1 else 0)-
    (if e.val=(shifted p.val.1 p.val.2.2,p.val.2.1) then 1 else 0)-
    (if e.val=(p.val.1,p.val.2.2) then 1 else 0)

def upperCoefficient (p : Upper) (e : Interior) : ℤ := if e.val=p.val.1 then 1 else 0

theorem extend_single (e : Interior) (q : EdgeData) :
    extend (Pi.single e (1 : ℝ)) q=if e.val=q then 1 else 0 := by
  by_cases hq : q∈edges
  · simp [extend,hq,Pi.single_apply,Subtype.ext_iff,eq_comm]
  · have hn : e.val≠q := by intro he; exact hq (he ▸ e.property)
    simp [extend,hq,hn]

theorem innerMatrix_entry (p : Inner) (e : Interior) :
    innerMatrix p e=(coefficient p e : ℝ) := by
  rw [innerMatrix,LinearMap.toMatrix'_apply]
  change realCurl (extend (Pi.single e (1 : ℝ))) p=_
  simp [realCurl,extend_single,coefficient]

theorem upperMatrix_entry (p : Upper) (e : Interior) :
    upperMatrix p e=(upperCoefficient p e : ℝ) := by
  rw [upperMatrix,LinearMap.toMatrix'_apply]
  change extend (Pi.single e (1 : ℝ)) p.val.1=_
  simp [extend_single,upperCoefficient]

theorem innerMatrix_mulVec (f : Field) : innerMatrix.mulVec f=innerMap f :=
  LinearMap.toMatrix'_mulVec _ _

theorem upperMatrix_mulVec (f : Field) : upperMatrix.mulVec f=upperMap f :=
  LinearMap.toMatrix'_mulVec _ _

theorem gram_energy (f : Field) : dotProduct f (gram.mulVec f)=realEnergy (extend f) := by
  rw [gram,Matrix.add_mulVec,dotProduct_add,← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,
    Matrix.dotProduct_transpose_mulVec,innerMatrix_mulVec,upperMatrix_mulVec]
  change (∑ p : Inner, realCurl (extend f) p*realCurl (extend f) p)+
    (∑ p : Upper, extend f p.val.1*extend f p.val.1)=realEnergy (extend f)
  simp only [← pow_two]
  unfold realEnergy
  congr 1

theorem innerMap_integer (f : EdgeData → ℤ) (p : Inner) :
    innerMap (fun e => (f e.val : ℝ)) p=(curl f p : ℝ) := by
  obtain ⟨h1,h2,h3,h4⟩ := inner_edge_geometry p p.property
  have he (e : EdgeData) (h : e∈edges) : extend (fun d => (f d.val : ℝ)) e=(f e : ℝ) := by
    simp [extend,h]
  change realCurl (extend (fun e => (f e.val : ℝ))) p=_
  unfold realCurl
  rw [he _ h1,he _ h2,he _ h3,he _ h4]
  simp only [curl,Int.cast_add,Int.cast_sub]

theorem upperMap_integer (f : EdgeData → ℤ) (p : Upper) :
    upperMap (fun e => (f e.val : ℝ)) p=(f p.val.1 : ℝ) := by
  have he : p.val.1∈edges := (Finset.mem_filter.mp p.property).2.1
  change extend (fun e => (f e.val : ℝ)) p.val.1=_
  simp [extend,he]

def intGram (f : EdgeData → ℤ) (e : Interior) : ℤ :=
  (∑ p : Inner, coefficient p e*curl f p)+
    ∑ p : Upper, upperCoefficient p e*f p.val.1

theorem gram_integer (f : EdgeData → ℤ) (e : Interior) :
    gram.mulVec (fun d => (f d.val : ℝ)) e=(intGram f e : ℝ) := by
  rw [gram,Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    innerMatrix_mulVec,upperMatrix_mulVec]
  simp only [Pi.add_apply,Matrix.mulVec,Matrix.transpose_apply,dotProduct,
    innerMatrix_entry,upperMatrix_entry,innerMap_integer,upperMap_integer,intGram,
    Int.cast_add,Int.cast_sum,Int.cast_mul]

def intV (e : EdgeData) : ℤ :=
  if e=(![0,0,0,1],1) then 1 else
  if e=(![0,0,0,1],2) then -1 else
  if e=(![0,0,1,0],0) then 1 else
  if e=(![0,0,1,0],3) then -1 else
  if e=(![0,1,0,0],0) then -1 else
  if e=(![0,1,0,0],3) then 1 else
  if e=(![1,0,0,0],1) then -1 else
  if e=(![1,0,0,0],2) then 1 else
  0


def intW (e : EdgeData) : ℤ :=
  if e=(![0,0,0,1],1) then 4 else
  if e=(![0,0,0,1],2) then -4 else
  if e=(![0,0,1,0],0) then 4 else
  if e=(![0,0,1,0],3) then -4 else
  if e=(![0,0,1,1],0) then -3 else
  if e=(![0,0,1,1],1) then -3 else
  if e=(![0,1,0,0],0) then -4 else
  if e=(![0,1,0,0],3) then 4 else
  if e=(![0,1,0,1],0) then 3 else
  if e=(![0,1,0,1],2) then 3 else
  if e=(![1,0,0,0],1) then -4 else
  if e=(![1,0,0,0],2) then 4 else
  if e=(![1,0,1,0],1) then 3 else
  if e=(![1,0,1,0],3) then 3 else
  if e=(![1,1,0,0],2) then -3 else
  if e=(![1,1,0,0],3) then -3 else
  0

def v : Field := fun e => (intV e.val : ℝ)
def w : Field := fun e => (intW e.val : ℝ)

theorem intGram_v : ∀ e : Interior, intGram intV e=intW e.val := by decide

theorem intGram_w : ∀ e : Interior, intGram intW e=9*intW e.val-11*intV e.val := by decide

theorem gram_v : gram.mulVec v=w := by
  funext e
  change gram.mulVec (fun d => (intV d.val : ℝ)) e=(intW e.val : ℝ)
  rw [gram_integer]
  exact_mod_cast intGram_v e

theorem gram_w : gram.mulVec w=(9 : ℝ) • w-(11 : ℝ) • v := by
  funext e
  change gram.mulVec (fun d => (intW d.val : ℝ)) e=
    9*(intW e.val : ℝ)-11*(intV e.val : ℝ)
  rw [gram_integer]
  exact_mod_cast intGram_w e

theorem sector_independent (a b : ℝ) (h : a • v+b • w=0) : a=0 ∧ b=0 := by
  have h1 := congrFun h (⟨(![0,0,0,1],1),by decide⟩ : Interior)
  have h2 := congrFun h (⟨(![0,0,1,1],0),by decide⟩ : Interior)
  norm_num [v,w,intV,intW,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2
  constructor <;> linarith

end OperatorDerivativeRewrite.Foundation.OneSidedGramSector
