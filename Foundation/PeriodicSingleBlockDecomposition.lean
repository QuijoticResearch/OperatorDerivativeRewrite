import Foundation.PeriodicSingleBlockCoercivity

/-! Exact decomposition of the actual periodic single-block Hessian into
three times identity and the Gram matrix of its 24 internal cube curls. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicSingleBlockDecomposition
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
set_option backward.isDefEq.respectTransparency false

def coreFace (p : Face) : Prop := block p.val.1=0 ∧ p.val.1 p.val.2.1=0 ∧ p.val.1 p.val.2.2=0
instance coreFace_decidable (p : Face) : Decidable (coreFace p) :=
  inferInstanceAs (Decidable (block p.val.1=0 ∧ p.val.1 p.val.2.1=0 ∧ p.val.1 p.val.2.2=0))
abbrev Core := {p : Face // coreFace p}

def coreFaces : Finset Face := Finset.univ.filter coreFace
def exteriorFaces : Finset Face := Finset.univ.image exteriorFace

theorem core_card : Fintype.card Core=24 := by decide
theorem exterior_not_core : ∀ a : Exterior, ¬ coreFace (exteriorFace a) := by decide

theorem noncore_classification : ∀ p : Face, ¬ coreFace p →
    (∀ e : Local, coefficient p e.val=0) ∨ ∃ a : Exterior, exteriorFace a=p := by decide

theorem core_exterior_disjoint : Disjoint coreFaces exteriorFaces := by
  apply Finset.disjoint_left.mpr
  intro p hp hc
  have hcore := (Finset.mem_filter.mp hp).2
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hc
  rw [← ha] at hcore
  exact exterior_not_core a hcore

theorem inactive_row_zero (f : Local → ℝ) (p : Face) (hp : p ∉ coreFaces ∪ exteriorFaces) :
    localIncidence f p=0 := by
  have hcore : ¬ coreFace p := by
    intro h
    exact hp (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  rcases noncore_classification p hcore with hz | ⟨a,ha⟩
  · rw [localIncidence_expansion]
    simp only [hz,Int.cast_zero,zero_mul,Finset.sum_const_zero]
  · exact False.elim (hp (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩)))

def coreEnergy (f : Local → ℝ) : ℝ := ∑ p ∈ coreFaces, (localIncidence f p)^2

theorem exact_energy_decomposition (f : Local → ℝ) :
    PeriodicSingleBlockCoercivity.energy f=3*PeriodicSingleBlockCoercivity.squaredSize f+coreEnergy f := by
  have hsum : (∑ p ∈ coreFaces ∪ exteriorFaces, (localIncidence f p)^2)=
      ∑ p : Face, (localIncidence f p)^2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [inactive_row_zero f p hp]
    norm_num
  have hext : (∑ p ∈ exteriorFaces, (localIncidence f p)^2)=
      ∑ a : Exterior, (localIncidence f (exteriorFace a))^2 := by
    rw [exteriorFaces,Finset.sum_image (fun a _ b _ he => exteriorFace_injective he)]
  unfold PeriodicSingleBlockCoercivity.energy
  rw [← hsum,Finset.sum_union core_exterior_disjoint,hext,exterior_sum]
  unfold coreEnergy
  ring

def coreIncidence : (Local → ℝ) →ₗ[ℝ] (Core → ℝ) where
  toFun f p := localIncidence f p.val
  map_add' f g := by ext p; simp
  map_smul' r f := by ext p; simp

def coreMatrix : Matrix Core Local ℝ := LinearMap.toMatrix' coreIncidence
def coreGram : Matrix Local Local ℝ := coreMatrix.transpose*coreMatrix

theorem coreMatrix_mulVec (f : Local → ℝ) : coreMatrix.mulVec f=coreIncidence f :=
  LinearMap.toMatrix'_mulVec _ _

theorem coreGram_energy (f : Local → ℝ) :
    dotProduct f (coreGram.mulVec f)=coreEnergy f := by
  rw [coreGram,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  simp only [coreMatrix_mulVec]
  change (∑ p : Core, (localIncidence f p.val)*(localIncidence f p.val))=coreEnergy f
  simp only [← pow_two]
  symm
  exact Finset.sum_subtype coreFaces (fun p => by simp [coreFaces])
    (fun p => (localIncidence f p)^2)

theorem hermitian_eq_of_quadratic {N : Type*} [Fintype N] [DecidableEq N]
    (A B : Matrix N N ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hQ : ∀ f : N → ℝ, dotProduct f (A.mulVec f)=dotProduct f (B.mulVec f)) : A=B := by
  ext i j
  have hi := hQ (Pi.single i 1)
  have hj := hQ (Pi.single j 1)
  have hij := hQ (Pi.single i 1+Pi.single j 1)
  simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct,Matrix.mulVec_single_one,
    single_dotProduct,one_mul,Matrix.col_apply] at hi hj hij
  have hAs := hA.apply i j
  have hBs := hB.apply i j
  simp only [star_trivial] at hAs hBs
  linarith

theorem localHessian_decomposition : localHessian=(3 : Matrix Local Local ℝ)+coreGram := by
  have hL : localHessian.IsHermitian := by
    simpa [localHessian] using Matrix.isHermitian_conjTranspose_mul_self localMatrix
  have hC : coreGram.IsHermitian := by
    simpa [coreGram] using Matrix.isHermitian_conjTranspose_mul_self coreMatrix
  apply hermitian_eq_of_quadratic _ _ hL ((Matrix.isHermitian_natCast 3).add hC)
  intro f
  rw [Matrix.add_mulVec,dotProduct_add,Matrix.natCast_mulVec,coreGram_energy]
  change (∑ e, f e*(localHessian.mulVec f) e)=
    (∑ e, f e*(3*f e))+coreEnergy f
  rw [hessian_energy,exact_energy_decomposition]
  unfold PeriodicSingleBlockCoercivity.squaredSize
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem reducedHessian_eq_coreGram : reducedHessian=coreGram := by
  rw [reducedHessian,localHessian_decomposition]
  abel

end OperatorDerivativeRewrite.Foundation.PeriodicSingleBlockDecomposition
