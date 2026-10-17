import Foundation.PeriodicFineEnergyWitnessCertificates

/-! A six-pair local stencil for the actual full fine curl Gram, without a planar hypothesis. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicFineSparseGram
open PeriodicInteriorGaugeKernel PeriodicCoarseGaugeDiagnostics
open PeriodicFineEnergyWitnessCertificates
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def stencil (f : Edge → ℤ) (e : Edge) : ℤ := ∑ ij : Pair,
  ((if e.2 = ij.val.1 then
    intCurl f e.1 ij.val.1 ij.val.2 - intCurl f (backShift e.1 ij.val.2) ij.val.1 ij.val.2
    else 0) +
  (if e.2 = ij.val.2 then
    intCurl f (backShift e.1 ij.val.1) ij.val.1 ij.val.2 - intCurl f e.1 ij.val.1 ij.val.2
    else 0))

theorem intGram_stencil (f : Edge → ℤ) (e : Edge) : intGram f e = stencil f e := by
  unfold intGram stencil
  rw [← faceEquiv.symm.sum_comp
    (fun p => incidenceCoefficient p e * intCurl f p.val.1 p.val.2.1 p.val.2.2)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  change (∑ v : Vertex, incidenceCoefficient (⟨(v,ij.val),ij.property⟩ : Face) e *
    intCurl f v ij.val.1 ij.val.2) = _
  simp only [incidenceCoefficient, add_mul, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_vertex_delta, sum_shift_delta, sum_shift_delta, sum_vertex_delta]
  have hne : ij.val.1 ≠ ij.val.2 := ne_of_lt ij.property
  by_cases hi : e.2 = ij.val.1 <;> by_cases hj : e.2 = ij.val.2 <;>
    simp [hi,hj,hne,Ne.symm hne]

end OperatorDerivativeRewrite.Foundation.PeriodicFineSparseGram
