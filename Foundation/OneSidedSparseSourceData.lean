import Foundation.OneSidedSourceMatrixData

/-! Sparse integer witnesses for the four-edge rows and at-most-six-face columns. -/
namespace OperatorDerivativeRewrite.Foundation.OneSidedSparseSourceData
open OneSidedSourceMatrixData
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 100000

def rowSign : Fin 4 → ℤ := ![1,1,-1,-1]

def rowLink : Fin 72 → Fin 4 → (Fin 32 ⊕ Fin 80) :=
  ![![.inl 0,.inl 20,.inl 12,.inl 1],
    ![.inl 0,.inl 21,.inl 7,.inl 2],
    ![.inl 0,.inl 22,.inl 4,.inl 3],
    ![.inl 1,.inl 13,.inl 8,.inl 2],
    ![.inl 1,.inl 14,.inl 5,.inl 3],
    ![.inl 2,.inl 9,.inl 6,.inl 3],
    ![.inl 4,.inl 23,.inl 15,.inl 5],
    ![.inl 4,.inl 24,.inl 10,.inl 6],
    ![.inl 4,.inr 38,.inr 1,.inr 0],
    ![.inl 5,.inl 16,.inl 11,.inl 6],
    ![.inl 5,.inr 16,.inr 2,.inr 0],
    ![.inl 6,.inr 6,.inr 3,.inr 0],
    ![.inl 7,.inl 25,.inl 17,.inl 8],
    ![.inl 7,.inr 42,.inr 9,.inr 4],
    ![.inl 7,.inl 26,.inl 10,.inl 9],
    ![.inl 8,.inr 20,.inr 10,.inr 4],
    ![.inl 8,.inl 18,.inl 11,.inl 9],
    ![.inr 4,.inr 11,.inr 5,.inl 9],
    ![.inl 10,.inl 27,.inl 19,.inl 11],
    ![.inl 10,.inr 44,.inr 12,.inr 5],
    ![.inl 10,.inr 45,.inr 7,.inr 6],
    ![.inl 11,.inr 22,.inr 13,.inr 5],
    ![.inl 11,.inr 23,.inr 8,.inr 6],
    ![.inl 12,.inr 51,.inr 28,.inr 14],
    ![.inl 12,.inl 28,.inl 17,.inl 13],
    ![.inl 12,.inl 29,.inl 15,.inl 14],
    ![.inr 14,.inr 29,.inr 19,.inl 13],
    ![.inr 14,.inr 30,.inr 15,.inl 14],
    ![.inl 13,.inl 18,.inl 16,.inl 14],
    ![.inl 15,.inr 53,.inr 31,.inr 15],
    ![.inl 15,.inl 30,.inl 19,.inl 16],
    ![.inl 15,.inr 54,.inr 17,.inr 16],
    ![.inr 15,.inr 32,.inr 21,.inl 16],
    ![.inl 16,.inr 23,.inr 18,.inr 16],
    ![.inl 17,.inr 57,.inr 33,.inr 19],
    ![.inl 17,.inr 58,.inr 25,.inr 20],
    ![.inl 17,.inl 31,.inl 19,.inl 18],
    ![.inr 19,.inr 34,.inr 21,.inl 18],
    ![.inr 20,.inr 26,.inr 22,.inl 18],
    ![.inl 19,.inr 60,.inr 35,.inr 21],
    ![.inl 19,.inr 61,.inr 27,.inr 22],
    ![.inl 19,.inr 62,.inr 24,.inr 23],
    ![.inr 36,.inr 68,.inr 50,.inl 20],
    ![.inr 36,.inr 69,.inr 41,.inl 21],
    ![.inr 36,.inr 70,.inr 37,.inl 22],
    ![.inl 20,.inl 28,.inl 25,.inl 21],
    ![.inl 20,.inl 29,.inl 23,.inl 22],
    ![.inl 21,.inl 26,.inl 24,.inl 22],
    ![.inr 37,.inr 71,.inr 52,.inl 23],
    ![.inr 37,.inr 72,.inr 43,.inl 24],
    ![.inl 23,.inl 30,.inl 27,.inl 24],
    ![.inl 23,.inr 54,.inr 39,.inr 38],
    ![.inl 24,.inr 45,.inr 40,.inr 38],
    ![.inr 41,.inr 73,.inr 56,.inl 25],
    ![.inr 41,.inr 74,.inr 43,.inl 26],
    ![.inl 25,.inr 58,.inr 47,.inr 42],
    ![.inl 25,.inl 31,.inl 27,.inl 26],
    ![.inr 42,.inr 48,.inr 44,.inl 26],
    ![.inr 43,.inr 75,.inr 59,.inl 27],
    ![.inl 27,.inr 61,.inr 49,.inr 44],
    ![.inl 27,.inr 62,.inr 46,.inr 45],
    ![.inr 50,.inr 76,.inr 56,.inl 28],
    ![.inr 50,.inr 77,.inr 52,.inl 29],
    ![.inr 51,.inr 64,.inr 57,.inl 28],
    ![.inr 51,.inr 65,.inr 53,.inl 29],
    ![.inl 28,.inl 31,.inl 30,.inl 29],
    ![.inr 52,.inr 78,.inr 59,.inl 30],
    ![.inr 53,.inr 66,.inr 60,.inl 30],
    ![.inl 30,.inr 62,.inr 55,.inr 54],
    ![.inr 56,.inr 79,.inr 59,.inl 31],
    ![.inr 57,.inr 67,.inr 60,.inl 31],
    ![.inr 58,.inr 63,.inr 61,.inl 31]]

def normalIndex : Fin 32 → Fin 6 → Fin 72 :=
  ![![0,1,2,0,0,0],
    ![0,3,4,0,0,0],
    ![1,3,5,0,0,0],
    ![2,4,5,0,0,0],
    ![2,6,7,8,0,0],
    ![4,6,9,10,0,0],
    ![5,7,9,11,0,0],
    ![1,12,13,14,0,0],
    ![3,12,15,16,0,0],
    ![5,14,16,17,0,0],
    ![7,14,18,19,20,0],
    ![9,16,18,21,22,0],
    ![0,23,24,25,0,0],
    ![3,24,26,28,0,0],
    ![4,25,27,28,0,0],
    ![6,25,29,30,31,0],
    ![9,28,30,32,33,0],
    ![12,24,34,35,36,0],
    ![16,28,36,37,38,0],
    ![18,30,36,39,40,41],
    ![0,42,45,46,0,0],
    ![1,43,45,47,0,0],
    ![2,44,46,47,0,0],
    ![6,46,48,50,51,0],
    ![7,47,49,50,52,0],
    ![12,45,53,55,56,0],
    ![14,47,54,56,57,0],
    ![18,50,56,58,59,60],
    ![24,45,61,63,65,0],
    ![25,46,62,64,65,0],
    ![30,50,65,66,67,68],
    ![36,56,65,69,70,71]]

def normalSign : Fin 32 → Fin 6 → ℤ :=
  ![![1,1,1,0,0,0],
    ![-1,1,1,0,0,0],
    ![-1,-1,1,0,0,0],
    ![-1,-1,-1,0,0,0],
    ![-1,1,1,1,0,0],
    ![-1,-1,1,1,0,0],
    ![-1,-1,-1,1,0,0],
    ![-1,1,1,1,0,0],
    ![-1,-1,1,1,0,0],
    ![1,-1,-1,-1,0,0],
    ![-1,-1,1,1,1,0],
    ![-1,-1,-1,1,1,0],
    ![-1,1,1,1,0,0],
    ![1,-1,-1,1,0,0],
    ![1,-1,-1,-1,0,0],
    ![-1,-1,1,1,1,0],
    ![1,-1,-1,-1,1,0],
    ![-1,-1,1,1,1,0],
    ![1,1,-1,-1,-1,0],
    ![-1,-1,-1,1,1,1],
    ![1,-1,1,1,0,0],
    ![1,-1,-1,1,0,0],
    ![1,-1,-1,-1,0,0],
    ![1,-1,-1,1,1,0],
    ![1,-1,-1,-1,1,0],
    ![1,-1,-1,1,1,0],
    ![1,1,-1,-1,-1,0],
    ![1,-1,-1,-1,1,1],
    ![1,1,-1,-1,1,0],
    ![1,1,-1,-1,-1,0],
    ![1,1,-1,-1,-1,1],
    ![1,1,1,-1,-1,-1]]

def rowA (r : Fin 72) (t : Fin 4) (i : Fin 32) : ℤ :=
  match rowLink r t with
  | .inl k => if k=i then rowSign t else 0
  | .inr _ => 0

def rowB (r : Fin 72) (t : Fin 4) (k : Fin 80) : ℤ :=
  match rowLink r t with
  | .inl _ => 0
  | .inr q => if q=k then rowSign t else 0

theorem A_sparse : ∀ r i, Adata r i=∑ t : Fin 4, rowA r t i := by
  decide +kernel

theorem B_sparse : ∀ r k, Bdata r k=∑ t : Fin 4, rowB r t k := by
  decide +kernel
theorem A_column_sparse : ∀ i r, Adata r i=
    ∑ t : Fin 6, if normalIndex i t=r then normalSign i t else 0 := by
  decide +kernel

end OperatorDerivativeRewrite.Foundation.OneSidedSparseSourceData
