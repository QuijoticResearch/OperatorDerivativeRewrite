import Foundation.FourCubeHarmonicIntegerData
import Foundation.FourCubeCompletedGram

/-! Exact full32-variable source witnesses for the completed Dirichlet quadratic.
The old pinned response is not used as a solution of this changed problem. -/
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedIntegerData
open OneSidedSourceMatrixData OneSidedBoundaryCycleData OneSidedSparseSourceData

def denominator : ℤ := 2079

def Xnum : Matrix (Fin 32) (Fin 3) ℤ :=
  ![
  ![-9,-16,-9],
  ![2,-2,-9],
  ![16,9,-61],
  ![-9,9,79],
  ![-79,-61,-79],
  ![9,-9,-79],
  ![61,79,237],
  ![9,-61,9],
  ![-2,-9,9],
  ![9,79,614],
  ![-614,-456,-614],
  ![-9,-79,-614],
  ![-2,-6,-2],
  ![6,2,-16],
  ![-2,2,9],
  ![-9,-16,-9],
  ![16,9,-61],
  ![2,-16,2],
  ![2,9,-9],
  ![9,-61,9],
  ![9,2,-2],
  ![61,-9,-16],
  ![-79,-9,9],
  ![79,9,-9],
  ![-237,-79,-61],
  ![-9,9,2],
  ![-614,-79,-9],
  ![614,79,9],
  ![16,-2,-6],
  ![-9,-2,2],
  ![61,-9,-16],
  ![9,-9,-2]]

def Rnum : Matrix (Fin 72) (Fin 3) ℤ :=
  ![
  ![0,-6,0],
  ![27,27,27],
  ![0,27,0],
  ![-6,0,27],
  ![0,0,0],
  ![-27,0,237],
  ![0,-27,0],
  ![237,237,237],
  ![-79,-61,-79],
  ![-27,0,237],
  ![9,-9,-79],
  ![61,79,237],
  ![0,-27,0],
  ![9,-61,9],
  ![0,237,0],
  ![-2,-9,9],
  ![0,0,0],
  ![-9,-79,1465],
  ![0,-237,0],
  ![1465,1623,1465],
  ![-614,-456,-614],
  ![-9,-79,1465],
  ![-9,-79,-614],
  ![-2,-6,-2],
  ![6,6,6],
  ![0,6,0],
  ![-6,-2,16],
  ![2,-2,-9],
  ![-6,0,27],
  ![-9,-16,-9],
  ![27,27,27],
  ![-9,-16,-9],
  ![-16,-9,61],
  ![16,9,-61],
  ![2,-16,2],
  ![2,-16,2],
  ![0,27,0],
  ![-2,-9,9],
  ![-2,-9,9],
  ![9,-61,9],
  ![9,-61,9],
  ![9,-61,9],
  ![-9,-2,2],
  ![-61,9,16],
  ![79,9,-9],
  ![-27,0,6],
  ![0,0,0],
  ![-237,0,27],
  ![-79,-9,9],
  ![237,79,61],
  ![-237,0,27],
  ![79,9,-9],
  ![-237,-79,-61],
  ![9,-9,-2],
  ![614,79,9],
  ![-9,9,2],
  ![0,0,0],
  ![-1465,79,9],
  ![-614,-79,-9],
  ![-1465,79,9],
  ![614,79,9],
  ![-16,2,6],
  ![9,2,-2],
  ![-16,2,6],
  ![9,2,-2],
  ![-27,0,6],
  ![-61,9,16],
  ![-61,9,16],
  ![61,-9,-16],
  ![-9,9,2],
  ![-9,9,2],
  ![-9,9,2]]

def Mnum : Fin 32 → ℤ := ![3,3,3,3,2,2,2,2,2,2,1,1,2,2,2,1,1,1,1,0,2,2,2,1,1,1,1,0,1,1,0,0]

theorem multiplicities : ∀ i : Fin 32,
    (FourCubeNegativeCompletion.multiplicity (interiorPoint i) : ℤ)=Mnum i := by
  intro i
  fin_cases i <;> decide +kernel

def linkValue (e : Fin 32 ⊕ Fin 80) (j : Fin 3) : ℤ :=
  Sum.elim (fun i => Xnum i j)
    (fun k => denominator*FourCubeHarmonicIntegerData.Bnum k j) e

theorem residual_sparse : ∀ (p : Fin 72) (j : Fin 3),
    (∑ t : Fin 4,rowSign t*linkValue (rowLink p t) j)=Rnum p j := by
  intro p
  fin_cases p <;> decide +kernel

theorem residual_equations (p : Fin 72) (j : Fin 3) :
    (∑ i : Fin 32,Adata p i*Xnum i j)+
      denominator*(∑ k : Fin 80,Bdata p k*FourCubeHarmonicIntegerData.Bnum k j)=Rnum p j := by
  have ht := OneSidedIntegerResponseData.sparse_row_action p (fun i => Xnum i j)
    (fun k => denominator*FourCubeHarmonicIntegerData.Bnum k j)
  change _=(∑ t : Fin 4,rowSign t*linkValue (rowLink p t) j) at ht
  rw [residual_sparse] at ht
  calc
    _ = (∑ i : Fin 32,Adata p i*Xnum i j)+
        ∑ k : Fin 80,Bdata p k*(denominator*FourCubeHarmonicIntegerData.Bnum k j) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := ht

theorem normal_sparse : ∀ (i : Fin 32) (j : Fin 3),
    (∑ t : Fin 6,normalSign i t*Rnum (normalIndex i t) j)+Mnum i*Xnum i j=0 := by
  intro i
  fin_cases i <;> decide +kernel

theorem normal_equations (i : Fin 32) (j : Fin 3) :
    (∑ p : Fin 72,Adata p i*Rnum p j)+Mnum i*Xnum i j=0 := by
  have h : (∑ p : Fin 72,Adata p i*Rnum p j)=
      ∑ t : Fin 6,normalSign i t*Rnum (normalIndex i t) j := by
    calc
      _ = ∑ t : Fin 6,∑ p : Fin 72,
          (if normalIndex i t=p then normalSign i t else 0)*Rnum p j := by
        simp_rw [A_column_sparse,Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = _ := by simp [ite_mul]
  rw [h]
  exact normal_sparse i j

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedIntegerData
