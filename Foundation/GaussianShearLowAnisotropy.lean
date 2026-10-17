import Foundation.GaussianShearShellSplit
import Mathlib.Algebra.Order.Chebyshev

/-! Actual low-shell angular weights of the Fibonacci shear have a uniform positive variance. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.GaussianShearLowAnisotropy
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearSectorMoments
open GaussianShearRayMoments LabelledShearCentroid FibonacciNearestPartition FibonacciShearCentroid
open GaussianShearShellSplit
attribute [local instance] Classical.propDecidable

def sectorDensity (N : ℕ) (nu t : ℝ) (j : Fin 16) (k : Wave) : ℝ :=
  if partition k=j then lowDensity N 1 nu t k else 0

def energy (N : ℕ) (nu t : ℝ) (j : Fin 16) : ℝ := ∑' k : Wave, sectorDensity N nu t j k

def weight (N : ℕ) (nu t : ℝ) (j : Fin 16) : ℝ := energy N nu t j/lowMoment N 1 nu t

def variance (N : ℕ) (nu t : ℝ) : ℝ := ∑ j : Fin 16, (weight N nu t j-1/16)^2

theorem sector_summable (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16) :
    Summable (sectorDensity N nu t j) := summable_filter _ (low_summable N 1 nu t hs) _

theorem sum_energy (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    ∑ j : Fin 16, energy N nu t j=lowMoment N 1 nu t := by
  unfold energy
  rw [← Summable.tsum_finsetSum (fun j _ => sector_summable N nu t hs j)]
  apply tsum_congr
  intro k
  simp [sectorDensity]

theorem energy_outside (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16)
    (hj : j ∉ Set.range rayLabels) : energy N nu t j=0 := by
  have he (k : Wave) : sectorDensity N nu t j k=0 := by
    by_cases hk : radius k ≤ (N:ℝ)^2
    · have hid : sectorDensity N nu t j k=partitionDensity partition j 1 nu t k := by
        simp [sectorDensity,lowDensity,hk,partitionDensity]
      rw [hid,partition_density_eq rayLabels partition compatible 1 (by omega) nu t hs,
        FiniteRayCentroid.spread_outside _ _ j hj]
    · simp [sectorDensity,lowDensity,hk]
  simp only [energy,he,tsum_zero]

theorem weight_sum (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    ∑ j : Fin 16, weight N nu t j=1 := by
  simp only [weight,← Finset.sum_div,sum_energy N nu t hs]
  exact div_self (ne_of_gt (low_positive N 1 hN nu t hs))

theorem weight_outside (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16)
    (hj : j ∉ Set.range rayLabels) : weight N nu t j=0 := by
  rw [weight,energy_outside N nu t hs j hj,zero_div]

theorem four_support_variance (L : Fin 4 ↪ Fin 16) (w : Fin 16 → ℝ)
    (hsum : ∑ j, w j=1) (hout : ∀ j, j ∉ Set.range L → w j=0) :
    (3:ℝ)/16 ≤ ∑ j, (w j-1/16)^2 := by
  let v : Fin 4 → ℝ := fun r => w (L r)
  have hrep : w=FiniteRayCentroid.spread L v := by
    funext j
    by_cases hj : j ∈ Set.range L
    · obtain ⟨r,rfl⟩ := hj
      rw [FiniteRayCentroid.spread_image]
    · rw [hout j hj,FiniteRayCentroid.spread_outside _ _ j hj]
  have hv : ∑ r, v r=1 := by
    rw [← FiniteRayCentroid.sum_spread L v,← hrep]
    exact hsum
  have hsq : (fun j => (w j)^2)=FiniteRayCentroid.spread L (fun r => (v r)^2) := by
    funext j
    rw [hrep]
    simpa only [pow_two] using FiniteRayCentroid.spread_mul L v v j
  have hsqsum : (∑ j, (w j)^2)=∑ r, (v r)^2 := by
    change (∑ j, (fun j => (w j)^2) j)=_
    rw [hsq,FiniteRayCentroid.sum_spread]
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := v)
  norm_num only [Finset.card_univ,Fintype.card_fin,hv,one_pow] at hc
  rw [← hsqsum] at hc
  have he (j : Fin 16) : (w j-1/16)^2=(w j)^2-w j/8+1/256 := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,hsum]
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  nlinarith

theorem low_variance_bound (N : ℕ) (hN : 1 ≤ N) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    (3:ℝ)/16 ≤ variance N nu t :=
  four_support_variance rayLabels (weight N nu t) (weight_sum N hN nu t hs)
    (weight_outside N nu t hs)

theorem initial_low_variance_positive (N : ℕ) (hN : 1 ≤ N) (nu : ℝ) :
    0 < variance N nu 0 := by
  have h := low_variance_bound N hN nu 0 (by norm_num)
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianShearLowAnisotropy
