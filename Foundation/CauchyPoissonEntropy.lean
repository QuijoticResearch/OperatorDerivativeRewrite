import Foundation.CauchyPoissonLaplaceResolvent
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
/-! Actual forward-law relative entropy monotonicity and uniform positive-time
minorization by the invariant Circle law. No sharp LSI or entropy decay rate
is inferred from curvature or from this existential minorization. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonEntropy
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonFeller

theorem density_minorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi),
      ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ := by
  let R : Circle × ℝ → ℝ := fun p => poleWeight (evolution q t p.1) p.2 / poleWeight q p.2
  have hc : Continuous R := (joint_weight_continuous q t hq ht).div
    ((poleWeight_continuous q (by simpa using hq)).comp continuous_snd)
    (fun p => ne_of_gt (poleWeight_positive q (by simpa using hq) p.2))
  have hk : IsCompact (univ ×ˢ Icc (0:ℝ) (2*Real.pi) : Set (Circle × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨ε,hε,hbound⟩ := hk.exists_forall_le' hc.continuousOn
    (a := 0) (fun p hp => div_pos (poleWeight_positive _
      (evolution_strict_disk q t hq ht p.1 (by simp)) p.2)
      (poleWeight_positive q (by simpa using hq) p.2))
  refine ⟨ε,hε,fun z θ hθ => ?_⟩
  exact (le_div_iff₀ (poleWeight_positive q (by simpa using hq) θ)).mp (hbound (z,θ) ⟨mem_univ _,hθ⟩)

theorem poleLaw_minorization (q t ε : ℝ) (hq : |q| < 1) (hε : 0 ≤ ε)
    (h : ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi), ε*poleWeight q θ ≤ poleWeight (evolution q t z) θ)
    (z : Circle) : ENNReal.ofReal ε • poleLaw q ≤ poleLaw (evolution q t z) := by
  change ENNReal.ofReal ε • (volume.restrict (Ioc 0 (2*Real.pi))).withDensity (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ)) ≤ _
  rw [← withDensity_smul' (ENNReal.ofReal ε) (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ENNReal.ofReal ε * ENNReal.ofReal (poleWeight q θ) ≤ _
  rw [← ENNReal.ofReal_mul hε]
  exact ENNReal.ofReal_le_ofReal (h z θ ⟨hθ.1.le,hθ.2⟩)

theorem kernel_minorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Circle, ENNReal.ofReal ε • invariantLaw q ≤ kernel q t z := by
  obtain ⟨ε,hε,h⟩ := density_minorization q t hq ht
  refine ⟨ε,hε,fun z => ?_⟩
  rw [kernel_positive_apply q t ht z,invariantLaw,← Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable]
  exact Measure.map_mono (poleLaw_minorization q t ε hq hε.le h z) Circle.exp.continuous.measurable

theorem invariant_comp (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    (kernel q t) ∘ₘ (invariantLaw q) = invariantLaw q := by
  exact kernel_invariant q t hq ht

theorem relative_entropy_contracts (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    InformationTheory.klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤
      InformationTheory.klDiv μ (invariantLaw q) := by
  let := kernel_markov q t hq ht
  let := invariantLaw_probability q hq
  have h := InformationTheory.klDiv_comp_right_le μ (invariantLaw q) (kernel q t)
  rwa [invariant_comp q t hq ht] at h


theorem entropy_time_monotone (q s t : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    InformationTheory.klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤
      InformationTheory.klDiv ((kernel q s) ∘ₘ μ) (invariantLaw q) := by
  let := kernel_markov q s hq hs
  have h := relative_entropy_contracts q (t-s) hq (sub_nonneg.mpr hst) ((kernel q s) ∘ₘ μ)
  rw [Measure.comp_assoc,kernel_composition q s (t-s) hq hs (sub_nonneg.mpr hst)] at h
  simpa only [add_sub_cancel] using h

theorem entropy_stays_finite (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (μ : Measure Circle) [IsProbabilityMeasure μ]
    (h : InformationTheory.klDiv μ (invariantLaw q) ≠ ⊤) :
    InformationTheory.klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≠ ⊤ :=
  ne_top_of_le_ne_top h (relative_entropy_contracts q t hq ht μ)


theorem strict_kernel_minorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ z : Circle, ENNReal.ofReal ε • invariantLaw q ≤ kernel q t z := by
  obtain ⟨a,ha,h⟩ := kernel_minorization q t hq ht
  let ε := min a 1 / 2
  have hε : 0 < ε := half_pos (lt_min ha (by norm_num))
  have hεa : ε ≤ a := le_trans (half_le_self (le_of_lt (lt_min ha (by norm_num)))) (min_le_left _ _)
  have hε1 : ε < 1 := by dsimp [ε]; have := min_le_right a (1:ℝ); linarith
  refine ⟨ε,hε,hε1,fun z => ?_⟩
  apply le_trans _ (h z)
  apply Measure.le_iff.mpr
  intro B hB
  simp only [Measure.smul_apply,smul_eq_mul]
  gcongr

theorem forward_minorization (q t ε : ℝ) (μ : Measure Circle) [IsProbabilityMeasure μ]
    (h : ∀ z : Circle, ENNReal.ofReal ε • invariantLaw q ≤ kernel q t z) :
    ENNReal.ofReal ε • invariantLaw q ≤ (kernel q t) ∘ₘ μ := by
  apply Measure.le_iff.mpr
  intro B hB
  change (ENNReal.ofReal ε • invariantLaw q) B ≤ (μ.bind (kernel q t)) B
  rw [Measure.bind_apply hB (kernel q t).aemeasurable]
  have hb : ∀ z : Circle, (ENNReal.ofReal ε • invariantLaw q) B ≤ kernel q t z B :=
    fun z => Measure.le_iff.mp (h z) B hB
  simpa using lintegral_mono (μ := μ) hb

end OperatorDerivativeRewrite.Foundation.CauchyPoissonEntropy
