import Foundation.IBMRightGermEnergyMeasure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Genuine deterministic IBM-germ stochastic sums and their exact time-L2
Gram identity. Coefficients are finite real time dictionaries. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermDeterministicIntegral
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMRightGermFiltration
open IBMRightGermEnergyMeasure
set_option backward.isDefEq.respectTransparency false

abbrev TimeL2 := Lp ℝ 2 energyMeasure

def timePrefix (t : ℝ≥0) : TimeL2 :=
  indicatorConstLp 2 measurableSet_Ioc (energyMeasure_Ioc_finite 0 t).ne (1 : ℝ)

theorem covariance_le {s t : ℝ≥0} (hst : s ≤ t) :
    inner ℝ (rightLimitClass s) (rightLimitClass t) = energy s := by
  have he := (rightPast s).inner_starProjection_left_eq_right
    (rightLimitClass s) (rightLimitClass t)
  rw [Submodule.starProjection_eq_self_iff.mpr (rightLimitClass_mem s),
    project_rightLimit hst, real_inner_self_eq_norm_sq] at he
  exact he

theorem covariance (s t : ℝ≥0) :
    inner ℝ (rightLimitClass s) (rightLimitClass t) = energy (min s t) := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact covariance_le hst
  · rw [min_eq_right hts, real_inner_comm]
    exact covariance_le hts

theorem prefix_inner (s t : ℝ≥0) : inner ℝ (timePrefix s) (timePrefix t) = energy (min s t) := by
  rw [timePrefix, timePrefix, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    measurableSet_Ioc measurableSet_Ioc (energyMeasure_Ioc_finite 0 s).ne
      (energyMeasure_Ioc_finite 0 t).ne]
  have hs : Ioc (0 : ℝ≥0) s ∩ Ioc 0 t = Ioc 0 (min s t) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, le_min_iff]
    tauto
  rw [hs, Measure.real, energyMeasure_Ioc, energy_zero, sub_zero,
    ENNReal.toReal_ofReal (show 0 ≤ energy (min s t) from sq_nonneg _)]

theorem prefix_gram (s t : ℝ≥0) :
    inner ℝ (timePrefix s) (timePrefix t) = inner ℝ (rightLimitClass s) (rightLimitClass t) := by
  rw [prefix_inner, covariance]

def timeDictionary : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] TimeL2 := Finsupp.linearCombination ℝ timePrefix

def stochasticDictionary : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] JointL2 :=
  Finsupp.linearCombination ℝ rightLimitClass

theorem dictionary_inner (a b : ℝ≥0 →₀ ℝ) :
    inner ℝ (stochasticDictionary a) (stochasticDictionary b) =
      inner ℝ (timeDictionary a) (timeDictionary b) := by
  simp only [stochasticDictionary, timeDictionary, Finsupp.linearCombination_apply,
    Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    prefix_gram]

theorem dictionary_norm (a : ℝ≥0 →₀ ℝ) :
    ‖stochasticDictionary a‖ = ‖timeDictionary a‖ := by
  have h := dictionary_inner a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem dictionary_eq_iff (a b : ℝ≥0 →₀ ℝ) :
    stochasticDictionary a = stochasticDictionary b ↔ timeDictionary a = timeDictionary b := by
  calc
    _ ↔ ‖stochasticDictionary (a - b)‖ = 0 := by
      rw [map_sub, norm_eq_zero, sub_eq_zero]
    _ ↔ ‖timeDictionary (a - b)‖ = 0 := by rw [dictionary_norm]
    _ ↔ _ := by rw [map_sub, norm_eq_zero, sub_eq_zero]

theorem interval_dictionary (s t : ℝ≥0) (c : ℝ) :
    stochasticDictionary (Finsupp.single t c - Finsupp.single s c) =
      c • (rightLimitClass t - rightLimitClass s) := by
  simp only [map_sub, stochasticDictionary, Finsupp.linearCombination_single,
    smul_sub]

theorem interval_time_dictionary {s t : ℝ≥0} (hst : s ≤ t) :
    timeDictionary (Finsupp.single t 1 - Finsupp.single s 1) =
      indicatorConstLp 2 measurableSet_Ioc (energyMeasure_Ioc_finite s t).ne (1 : ℝ) := by
  have hu := indicatorConstLp_disjoint_union (p := 2) measurableSet_Ioc measurableSet_Ioc
    (energyMeasure_Ioc_finite 0 s).ne (energyMeasure_Ioc_finite s t).ne
      (Ioc_disjoint_Ioc_of_le (le_rfl : s ≤ s)) (1 : ℝ)
  have hs : Ioc (0 : ℝ≥0) s ∪ Ioc s t = Ioc 0 t := Ioc_union_Ioc_eq_Ioc zero_le hst
  simp only [hs] at hu
  change timePrefix t = timePrefix s + _ at hu
  simp only [map_sub, timeDictionary, Finsupp.linearCombination_single, one_smul]
  rw [hu]
  abel

theorem stochasticDictionary_ae (a : ℝ≥0 →₀ ℝ) :
    stochasticDictionary a =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => ∑ t ∈ a.support, a t * rightValue t ω) := by
  classical
  have hs := Lp.coeFn_finsetSum a.support (fun t => a t • rightLimitClass t)
  have hm : ∀ t ∈ a.support,
      (a t • rightLimitClass t : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => a t * rightValue t ω) := by
    intro t _
    exact Lp.coeFn_smul _ _
  change (∑ t ∈ a.support, a t • rightLimitClass t : JointL2) =ᵐ[_] _
  filter_upwards [hs, eventuallyEq_sum hm] with ω hω hsum
  have hh := hω.trans hsum
  simpa only [Finset.sum_apply] using hh

end OperatorDerivativeRewrite.Foundation.IBMRightGermDeterministicIntegral
