import Foundation.CauchyPoissonMixtureEntropy
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology ENNReal
/-! Positive-time upper domination and finite relative entropy for every
initial probability law of the actual drifted circle Poisson kernel. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonRegularization
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel CauchyPoissonFeller

theorem density_majorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Circle, ∀ θ ∈ Icc 0 (2*Real.pi),
      poleWeight (evolution q t z) θ ≤ C*poleWeight q θ := by
  let R : Circle × ℝ → ℝ := fun p => poleWeight (evolution q t p.1) p.2 / poleWeight q p.2
  have hc : Continuous R := (joint_weight_continuous q t hq ht).div
    ((poleWeight_continuous q (by simpa using hq)).comp continuous_snd)
    (fun p => ne_of_gt (poleWeight_positive q (by simpa using hq) p.2))
  have hk : IsCompact (univ ×ˢ Icc (0:ℝ) (2*Real.pi) : Set (Circle × ℝ)) := isCompact_univ.prod isCompact_Icc
  obtain ⟨B,hB⟩ := hk.bddAbove_image hc.continuousOn
  have hC : (0:ℝ) < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  refine ⟨max B 1,hC,fun z θ hθ => ?_⟩
  apply (div_le_iff₀ (poleWeight_positive q (by simpa using hq) θ)).mp
  have hb : R (z,θ) ≤ B := hB ⟨(z,θ),⟨mem_univ z,hθ⟩,rfl⟩
  exact hb.trans (le_max_left B 1)

theorem kernel_majorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Circle, kernel q t z ≤ ENNReal.ofReal C • invariantLaw q := by
  obtain ⟨C,hC,h⟩ := density_majorization q t hq ht
  refine ⟨C,hC,fun z => ?_⟩
  rw [kernel_positive_apply q t ht z,invariantLaw,← Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable]
  apply Measure.map_mono _ Circle.exp.continuous.measurable
  change (volume.restrict (Ioc 0 (2*Real.pi))).withDensity (fun θ : ℝ => ENNReal.ofReal (poleWeight (evolution q t z) θ)) ≤ ENNReal.ofReal C • (volume.restrict (Ioc 0 (2*Real.pi))).withDensity (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ))
  rw [← withDensity_smul' (ENNReal.ofReal C) (fun θ : ℝ => ENNReal.ofReal (poleWeight q θ)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change _ ≤ ENNReal.ofReal C * ENNReal.ofReal (poleWeight q θ)
  rw [← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (h z θ ⟨hθ.1.le,hθ.2⟩)

theorem forward_majorization (q t C : ℝ) (μ : Measure Circle) [IsProbabilityMeasure μ]
    (h : ∀ z : Circle, kernel q t z ≤ ENNReal.ofReal C • invariantLaw q) :
    (kernel q t) ∘ₘ μ ≤ ENNReal.ofReal C • invariantLaw q := by
  apply Measure.le_iff.mpr
  intro B hB
  change (μ.bind (kernel q t)) B ≤ _
  rw [Measure.bind_apply hB (kernel q t).aemeasurable]
  have hb : ∀ z : Circle, kernel q t z B ≤ (ENNReal.ofReal C • invariantLaw q) B :=
    fun z => Measure.le_iff.mp (h z) B hB
  simpa using lintegral_mono (μ := μ) hb

theorem rnDeriv_bound {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [SigmaFinite ν]
    (C : ℝ≥0∞) (h : μ ≤ C • ν) : μ.rnDeriv ν ≤ᵐ[ν] fun _ => C := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s hs _ => ?_
  simpa only [lintegral_const,Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul] using
    (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (Measure.le_iff.mp h s hs)

theorem entropy_finite_of_domination {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (C : ℝ) (hC : 0 ≤ C)
    (h : μ ≤ ENNReal.ofReal C • ν) : klDiv μ ν ≠ ⊤ := by
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (continuous_klFun.continuousOn : ContinuousOn klFun (Icc 0 C))
  apply ne_of_lt
  calc
    _ ≤ ∫⁻ _ : α, ENNReal.ofReal B ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [rnDeriv_bound μ ν (ENNReal.ofReal C) h] with x hx
      apply ENNReal.ofReal_le_ofReal
      apply hB
      apply mem_image_of_mem
      exact ⟨ENNReal.toReal_nonneg,by simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hx⟩
    _ < ⊤ := by simp

theorem positive_time_entropy_finite (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≠ ⊤ := by
  let := kernel_markov q t hq ht.le
  let := invariantLaw_probability q hq
  obtain ⟨C,hC,h⟩ := kernel_majorization q t hq ht
  exact entropy_finite_of_domination _ _ C hC.le (forward_majorization q t C μ h)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonRegularization
