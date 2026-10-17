import Foundation.FibonacciShearCentroid

/-! Actual unit-direction normalization and spherical nearest-center interpretation of the partition. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FibonacciAngularRealization
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FibonacciNearestPartition
open FibonacciSphereWitness FibonacciShearCentroid

def length (k : Wave) : ℝ := Real.sqrt (∑ q : Fin 3, (k q : ℝ)^2)

def normalized (k : Wave) : Direction := fun q => (k q : ℝ)/length k

theorem length_positive (k : Wave) (hk : k ≠ 0) : 0 < length k := by
  obtain ⟨q,hq⟩ : ∃ q, k q ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hk
    funext q
    exact hn q
  have hqR : (k q : ℝ) ≠ 0 := by exact_mod_cast hq
  apply Real.sqrt_pos.mpr
  exact (sq_pos_of_ne_zero hqR).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (k j : ℝ)) (Finset.mem_univ q))

theorem length_square (k : Wave) : length k^2=∑ q : Fin 3, (k q : ℝ)^2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem normalized_unit (k : Wave) (hk : k ≠ 0) : ∑ q, (normalized k q)^2=1 := by
  simp only [normalized,div_pow,← Finset.sum_div]
  rw [← length_square]
  exact div_self (pow_ne_zero 2 (ne_of_gt (length_positive k hk)))

theorem label_normalized (k : Wave) (hk : k ≠ 0) : label (normalized k)=partition k := by
  have he : normalized k=(fun q => (1/length k)*(k q : ℝ)) := by
    funext q
    dsimp [normalized]
    ring
  rw [he,label_scale (1/length k) (one_div_pos.mpr (length_positive k hk))]
  rfl

theorem spherical_nearest (k : Wave) (hk : k ≠ 0) (j : Fin 16) :
    (∑ q, (normalized k q-center 16 (partition k) q)^2) ≤
      ∑ q, (normalized k q-center 16 j q)^2 := by
  have h := nearest (normalized k) j
  rw [label_normalized k hk] at h
  exact h

end OperatorDerivativeRewrite.Foundation.FibonacciAngularRealization
