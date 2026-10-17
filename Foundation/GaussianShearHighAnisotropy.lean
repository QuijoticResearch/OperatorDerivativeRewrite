import Foundation.GaussianShearAsymptoticCountertest

/-! Actual normalized high-shell angular weights retain a nonzero anisotropy. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianShearHighAnisotropy
open FiniteFourierDifferentialTrace FiniteFourierSynthesis GaussianShearSectorMoments
open GaussianShearShellSplit FibonacciNearestPartition FibonacciShearCentroid LabelledShearCentroid
attribute [local instance] Classical.propDecidable

def highEnergy (N : ℕ) (nu t : ℝ) (j : Fin 16) : ℝ :=
  partitionMoment partition 1 nu t j-GaussianShearLowAnisotropy.energy N nu t j

def highWeight (N : ℕ) (nu t : ℝ) (j : Fin 16) : ℝ := highEnergy N nu t j/highMoment N 1 nu t

def highVariance (N : ℕ) (nu t : ℝ) : ℝ := ∑ j : Fin 16, (highWeight N nu t j-1/16)^2

theorem high_energy_is_sum (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16) :
    highEnergy N nu t j=∑' k : Wave, if partition k=j then highDensity N 1 nu t k else 0 := by
  unfold highEnergy partitionMoment GaussianShearLowAnisotropy.energy
  rw [← (partition_summable rayLabels partition compatible 1 (by omega) nu t hs j).tsum_sub
    (GaussianShearLowAnisotropy.sector_summable N nu t hs j)]
  apply tsum_congr
  intro k
  by_cases hj : partition k=j
  · simp only [partitionDensity,GaussianShearLowAnisotropy.sectorDensity,hj,ite_true]
    have h := density_split N 1 nu t k
    linarith
  · simp [partitionDensity,GaussianShearLowAnisotropy.sectorDensity,hj]

theorem high_energy_nonnegative (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16) :
    0 ≤ highEnergy N nu t j := by
  rw [high_energy_is_sum N nu t hs j]
  apply tsum_nonneg
  intro k
  split_ifs
  · exact high_nonnegative N 1 nu t k
  · rfl

theorem high_energy_sum (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    ∑ j : Fin 16, highEnergy N nu t j=highMoment N 1 nu t := by
  simp only [highEnergy,Finset.sum_sub_distrib]
  rw [GaussianShearLowAnisotropy.sum_energy N nu t hs,
    partition_moments 1 (by omega) nu t hs,FiniteRayCentroid.sum_energy]
  have h := moments_split N 1 nu t hs
  linarith

theorem high_energy_outside (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16)
    (hj : j ∉ range rayLabels) : highEnergy N nu t j=0 := by
  rw [highEnergy,partition_moment_eq rayLabels partition compatible 1 (by omega) nu t hs,
    FiniteRayCentroid.spread_outside _ _ j hj,
    GaussianShearLowAnisotropy.energy_outside N nu t hs j hj]
  simp

theorem high_weight_nonnegative (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16) :
    0 ≤ highWeight N nu t j :=
  div_nonneg (high_energy_nonnegative N nu t hs j) (high_positive N 1 nu t hs).le

theorem high_weight_sum (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    ∑ j : Fin 16, highWeight N nu t j=1 := by
  simp only [highWeight,← Finset.sum_div,high_energy_sum N nu t hs]
  exact div_self (ne_of_gt (high_positive N 1 nu t hs))

theorem high_weight_outside (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) (j : Fin 16)
    (hj : j ∉ range rayLabels) : highWeight N nu t j=0 := by
  rw [highWeight,high_energy_outside N nu t hs j hj,zero_div]

theorem high_variance_bound (N : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    (3:ℝ)/16 ≤ highVariance N nu t :=
  GaussianShearLowAnisotropy.four_support_variance rayLabels (highWeight N nu t)
    (high_weight_sum N nu t hs) (high_weight_outside N nu t hs)

theorem empty_sector : ∃ j : Fin 16, j ∉ range rayLabels := by
  have hn : ¬ Function.Surjective (rayLabels : Fin 4 → Fin 16) := by
    intro h
    have hc := Fintype.card_le_of_surjective rayLabels h
    norm_num at hc
  unfold Function.Surjective at hn
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  refine ⟨j,?_⟩
  rintro ⟨r,hr⟩
  exact hj r hr

theorem fixed_empty_bias : ∃ j : Fin 16, ∀ (N : ℕ) (nu t : ℝ), 0 < 1+nu*t →
    highWeight N nu t j-1/16=-(1:ℝ)/16 := by
  obtain ⟨j,hj⟩ := empty_sector
  refine ⟨j,fun N nu t hs => ?_⟩
  rw [high_weight_outside N nu t hs j hj]
  ring

theorem no_componentwise_suppression (nu t : ℝ) (hs : 0 < 1+nu*t) :
    ¬ ∀ j : Fin 16, Tendsto (fun N : ℕ => highWeight N nu t j-1/16) atTop (𝓝 0) := by
  intro h
  obtain ⟨j,hj⟩ := fixed_empty_bias
  have ht : Tendsto (fun N : ℕ => highWeight N nu t j-1/16) atTop (𝓝 (-(1:ℝ)/16)) := by
    simpa only [hj _ nu t hs] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (-(1:ℝ)/16)) atTop (𝓝 (-(1:ℝ)/16)))
  have he := tendsto_nhds_unique (h j) ht
  norm_num at he

end OperatorDerivativeRewrite.Foundation.GaussianShearHighAnisotropy
