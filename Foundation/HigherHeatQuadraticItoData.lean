import Foundation.HigherHeatQuadraticChannelLimit
import Foundation.HigherHeatContinuousDualCoordinate
import Mathlib.Topology.Order.ProjIcc

/-! Actual predictable quadratic data and the native dyadic time partition. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoData
open HigherHeatPolynomialCylinders HigherHeatAdaptedStepDuality HigherHeatQuadraticChannelLimit
open HigherHeatDyadicStepAgreement HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatDyadicTimeDensity HigherHeatContinuousDualCoordinate HigherHeatDyadicDualNodes

def prefixPolynomial (n c : ℕ) : Test n := ∑ i ∈ Finset.univ.filter (fun i : Fin (size n) => i.val < c), MvPolynomial.X i

def past (n : ℕ) (j : Fin (size n)) : Test n := prefixPolynomial n j.val

theorem prefix_zero (n : ℕ) : prefixPolynomial n 0 = 0 := by simp [prefixPolynomial]

theorem prefix_end (n : ℕ) : prefixPolynomial n (size n) = (HigherHeatMultivariateMoments.terminal : Test n) := by
  have hs : Finset.univ.filter (fun i : Fin (size n) => i.val < size n) = Finset.univ := by
    ext i; simp [i.isLt]
  rw [prefixPolynomial, hs]
  rfl

theorem prefix_succ (n c : ℕ) (hc : c < size n) :
    prefixPolynomial n (c+1) = prefixPolynomial n c + MvPolynomial.X ⟨c, hc⟩ := by
  classical
  let k : Fin (size n) := ⟨c, hc⟩
  have hs : Finset.univ.filter (fun i : Fin (size n) => i.val < c+1) =
      insert k (Finset.univ.filter (fun i : Fin (size n) => i.val < c)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    dsimp [k]
    omega
  have hk : k ∉ Finset.univ.filter (fun i : Fin (size n) => i.val < c) := by simp [k]
  rw [prefixPolynomial, hs, Finset.sum_insert hk]
  exact add_comm _ _

theorem past_adapted (n : ℕ) : Adapted (past n) := by
  intro j i hi
  obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hi)
  have he : i = k := by simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hik
  subst i
  exact (Finset.mem_filter.mp hk).2

theorem constants_adapted (n : ℕ) : Adapted (fun _ : Fin (size n) => (1:Test n)) := by
  intro j i hi
  simp at hi

theorem quadratic_telescope (n : ℕ) :
    (HigherHeatMultivariateMoments.terminal : Test n)^2 =
      stepPolynomial (past n) + stepPolynomial (past n) + quadraticPolynomial n (fun _ => 1) := by
  have ht := Finset.sum_range_sub (fun c => (prefixPolynomial n c)^2) (size n)
  have hf := Fin.sum_univ_eq_sum_range (fun c => (prefixPolynomial n (c+1))^2-(prefixPolynomial n c)^2) (size n)
  have hs : (∑ j : Fin (size n), ((prefixPolynomial n (j.val+1))^2 - (prefixPolynomial n j.val)^2)) =
      (HigherHeatMultivariateMoments.terminal : Test n)^2 := by
    rw [hf, ht, prefix_end, prefix_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero]
  have he (j : Fin (size n)) : (prefixPolynomial n (j.val+1))^2-(prefixPolynomial n j.val)^2 =
      past n j * MvPolynomial.X j + past n j * MvPolynomial.X j + (MvPolynomial.X j)^2 := by
    rw [prefix_succ n j.val j.isLt]
    change (past n j + MvPolynomial.X j)^2-(past n j)^2 = _
    ring
  simp only [he, Finset.sum_add_distrib] at hs
  simpa only [stepPolynomial, quadraticPolynomial, one_mul] using hs.symm

theorem cell_unique (n : ℕ) (j k : Fin (size n)) (t : ℝ)
    (hj : t ∈ gridCell n j) (hk : t ∈ gridCell n k) : j = k := by
  have hd := (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have he : (j.val:ℝ)+1 ≤ (k.val:ℝ) := by exact_mod_cast (show j.val+1 ≤ k.val by omega)
    have hh := mul_le_mul_of_nonneg_right he hd
    exact (not_lt_of_ge (hj.2.trans hh)) hk.1
  · have he : (k.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (show k.val+1 ≤ j.val by omega)
    have hh := mul_le_mul_of_nonneg_right he hd
    exact (not_lt_of_ge (hk.2.trans hh)) hj.1

theorem cell_exists (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
    ∃ j : Fin (size n), t ∈ gridCell n j := by
  classical
  let d : ℝ := HigherHeatDyadicLaws.duration 1 n
  let S : Finset (Fin (size n)) := Finset.univ.filter (fun j => t ≤ ((j.val:ℝ)+1)*d)
  have he : (((HigherHeatTerminalPositions.lastIndex n).val:ℝ)+1)*d = 1 := by
    have hc := HigherHeatTerminalPositions.lastIndex_count n
    have hh : (((HigherHeatTerminalPositions.lastIndex n).val:ℝ)+1) = (size n:ℝ) := by exact_mod_cast hc
    rw [hh]
    exact size_duration n
  have hn : S.Nonempty := by
    refine ⟨HigherHeatTerminalPositions.lastIndex n, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, he]
    exact ht.2
  let j : Fin (size n) := S.min' hn
  have hj : j ∈ S := Finset.min'_mem S hn
  refine ⟨j, ?_, (Finset.mem_filter.mp hj).2⟩
  by_cases hz : j.val = 0
  · simpa only [hz, Nat.cast_zero, zero_mul] using ht.1
  · by_contra hl
    have hp : j.val-1 < size n := by have := j.isLt; omega
    let k : Fin (size n) := ⟨j.val-1, hp⟩
    have hk : k ∈ S := by
      have hv : (k.val:ℝ)+1 = (j.val:ℝ) := by
        dsimp [k]
        exact_mod_cast (show j.val-1+1=j.val by omega)
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hv]
      exact le_of_not_gt hl
    have hh : j ≤ k := Finset.min'_le S k hk
    change j.val ≤ j.val-1 at hh
    omega

theorem past_curve (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) :
    pairing m hm T hT (core (cylinderOf n (past n j))) =
      curve m hm T hT (node n (prefixNode n j.val (Nat.le_of_lt j.isLt))) := by
  rw [curve_node]
  by_cases hz : j.val = 0
  · simp [past, hz, prefix_zero, prefixNode, dualNode]
  · let k : Fin (size n) := ⟨j.val-1, by have := j.isLt; omega⟩
    have hs : Finset.univ.filter (fun i : Fin (size n) => i.val < j.val) =
        Finset.univ.filter (fun i : Fin (size n) => i ≤ k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < j.val ↔ i.val ≤ j.val-1
      omega
    have hp : cylinderOf n (past n j) = HigherHeatPolynomialPathDomain.positionCylinder n k := by
      unfold past prefixPolynomial HigherHeatPolynomialPathDomain.positionCylinder HigherHeatPolynomialPathDomain.positionPolynomial
      rw [hs]
    rw [hp]
    simp only [prefixNode, dif_neg hz, dualNode, Option.elim_some]
    rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoData
