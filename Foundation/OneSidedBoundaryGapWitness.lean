import Foundation.OneSidedBoundaryGap

/-! A nonzero physical Rayleigh witness strictly below the rounded0.6964 value. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGapWitness
open OneSidedCapComplex OneSidedBoundaryGauge OneSidedBoundaryCycles
  OneSidedIntegerResponseData OneSidedBoundaryGramData OneSidedSchurCompression
  OneSidedSchurForm OneSidedBoundaryGap
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1000000

def z : Fin 34 → ℤ := ![2000,0,2000,760,2000,2000,-704,-704,9,-1935,-704,-704,-1935,9,-1935,9,-130,-130,-1935,-704,-704,-1935,-1935,0,0,-56,-56,-56,-56,-130,-56,-56,-130,-130]

def y : Fin 34 → ℝ := fun i => (z i : ℝ)

def eta : BoundaryField := cycleMatrix.mulVec y

theorem integer_norm : (∑ i : Fin 34, ∑ j : Fin 34, z i*Hdata i j*z j)=117410484 := by
  decide +kernel

theorem integer_gram : (∑ i : Fin 34, ∑ j : Fin 34, z i*Qdata i j*z j)=15782847719760 := by
  decide +kernel

theorem orthogonal (phi : Potential) : dotProduct eta (boundaryGradient phi)=0 := by
  have hm : eta∈LinearMap.range cycleMap := ⟨y,rfl⟩
  exact (divergence_zero_iff eta).mp (cycles_physical hm) phi

theorem metric_dot : dotProduct y (metric.mulVec y)=117410484 := by
  have ht : (∑ i : Fin 34, ∑ j : Fin 34,
      (z i : ℝ)*(Hdata i j : ℝ)*(z j : ℝ))=117410484 := by
    exact_mod_cast integer_norm
  change (∑ i : Fin 34, y i*(∑ j : Fin 34, metric i j*y j))=_
  simp_rw [Finset.mul_sum,metric_as_data]
  simpa only [y,mul_assoc] using ht

theorem compressed_dot : dotProduct y (compressed.mulVec y)=
    15782847719760/(denominator : ℝ) := by
  have ht : (∑ i : Fin 34, ∑ j : Fin 34,
      (z i : ℝ)*(Qdata i j : ℝ)*(z j : ℝ))=15782847719760 := by
    exact_mod_cast integer_gram
  calc
    _ = (∑ i : Fin 34, ∑ j : Fin 34, y i*(Qdata i j : ℝ)*y j)/(denominator : ℝ) := by
      change (∑ i : Fin 34, y i*(∑ j : Fin 34, compressed i j*y j))=_
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [compressed_as_data]
      ring
    _ = _ := by simpa only [y,ht]

theorem norm_value : dotProduct eta eta=117410484 := by
  change dotProduct (cycleMatrix.mulVec y) (cycleMatrix.mulVec y)=_
  rw [← metric_quadratic]
  exact metric_dot

theorem nonzero : eta≠0 := by
  intro h
  have ht := norm_value
  rw [h,dotProduct_zero] at ht
  norm_num at ht

theorem energy_value : dotProduct eta (schur.mulVec eta)=15782847719760/(denominator : ℝ) := by
  change dotProduct (cycleMatrix.mulVec y) (schur.mulVec (cycleMatrix.mulVec y))=_
  rw [← compressed_quadratic]
  exact compressed_dot

theorem below_rounded : dotProduct eta (schur.mulVec eta)<(1741/2500 : ℝ)*dotProduct eta eta := by
  rw [energy_value,norm_value]
  norm_num [denominator]

theorem rayleigh_value : dotProduct eta (schur.mulVec eta)/dotProduct eta eta=
    (729067245/1046910149 : ℝ) := by
  rw [energy_value,norm_value]
  norm_num [denominator]

theorem rounded_bound_fails : ¬(∀ e : BoundaryField,
    (∀ phi : Potential, dotProduct e (boundaryGradient phi)=0) →
    (1741/2500 : ℝ)*dotProduct e e≤dotProduct e (schur.mulVec e)) := by
  intro h
  exact (not_le_of_gt below_rounded) (h eta orthogonal)

theorem witness_bracket :
    (69639/100000 : ℝ)*dotProduct eta eta≤dotProduct eta (schur.mulVec eta) ∧
      dotProduct eta (schur.mulVec eta)<(1741/2500 : ℝ)*dotProduct eta eta :=
  ⟨boundary_gap eta orthogonal,below_rounded⟩

end OperatorDerivativeRewrite.Foundation.OneSidedBoundaryGapWitness
