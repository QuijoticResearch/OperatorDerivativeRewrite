import Foundation.RootMarkRealClarkLimit

/-! Genuine complex conditional approximation on the infinite root-mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkComplexClarkLimit
open RootMarkStochasticIntegral RootMarkRealClarkLimit
open MarkedRootRenewalProcess (MarkSample marks)

theorem split (Y : MarkSample → ℂ) :
    Y = lift (fun η => (Y η).re) + Complex.I • lift (fun η => (Y η).im) := by
  funext η
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lift, Function.comp_apply]
  change Y η = ((Y η).re : ℂ) + Complex.I * ((Y η).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (Y η)).symm

theorem error_split (Y : MarkSample → ℂ) (hY : Integrable Y marks) (n : ℕ) :
    (marks[Y | history n]-Y) =ᵐ[marks]
      ((marks[lift (fun η => (Y η).re) | history n]-lift (fun η => (Y η).re)) +
        Complex.I • (marks[lift (fun η => (Y η).im) | history n]-lift (fun η => (Y η).im))) := by
  have hr : Integrable (lift (fun η => (Y η).re)) marks :=
    Complex.ofRealCLM.integrable_comp (by simpa only [RCLike.re_eq_complex_re] using hY.re)
  have hi : Integrable (lift (fun η => (Y η).im)) marks :=
    Complex.ofRealCLM.integrable_comp (by simpa only [RCLike.im_eq_complex_im] using hY.im)
  have he := condExp_add hr (hi.smul Complex.I) (history n)
  have hs := condExp_smul (μ := marks) Complex.I (lift (fun η => (Y η).im)) (history n)
  have hy := split Y
  rw [← hy] at he
  filter_upwards [he,hs] with η heη hsη
  have heq : marks[Y | history n] η =
      marks[lift (fun η => (Y η).re) | history n] η +
        Complex.I * marks[lift (fun η => (Y η).im) | history n] η := by
    change _ = _ at heη
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsη] using heη
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  have hyη := congrFun hy η
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hyη
  linear_combination -hyη

theorem condExp_L1_limit (Y : MarkSample → ℂ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    Tendsto (fun n : ℕ => eLpNorm (marks[Y | history n]-Y) 1 marks) atTop (𝓝 0) := by
  have hr : Integrable (fun η => (Y η).re) marks := by
    simpa only [RCLike.re_eq_complex_re] using hY.re
  have hi : Integrable (fun η => (Y η).im) marks := by
    simpa only [RCLike.im_eq_complex_im] using hY.im
  have hR := lifted_condExp_limit _ hr (Complex.continuous_re.comp_stronglyMeasurable hm)
  have hI := lifted_condExp_limit _ hi (Complex.continuous_im.comp_stronglyMeasurable hm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds
    (by simpa only [add_zero] using hR.add hI) (fun _ => bot_le)
  intro n
  dsimp only
  rw [eLpNorm_congr_ae (error_split Y hY n)]
  exact (eLpNorm_add_le (by rfl)).trans_eq (by simp [eLpNorm_const_smul, enorm_eq_nnnorm])

theorem condExp_ae_limit (Y : MarkSample → ℂ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => marks[Y | history n] η) atTop (𝓝 (Y η)) := by
  have hr : Integrable (fun η => (Y η).re) marks := by
    simpa only [RCLike.re_eq_complex_re] using hY.re
  have hi : Integrable (fun η => (Y η).im) marks := by
    simpa only [RCLike.im_eq_complex_im] using hY.im
  have hR := lifted_condExp_ae_limit _ hr (Complex.continuous_re.comp_stronglyMeasurable hm)
  have hI := lifted_condExp_ae_limit _ hi (Complex.continuous_im.comp_stronglyMeasurable hm)
  have he := ae_all_iff.mpr (fun n => error_split Y hY n)
  filter_upwards [hR,hI,he] with η hrη hiη heη
  have ht := ((hrη.sub_const ((Y η).re : ℂ)).add
    ((hiη.sub_const ((Y η).im : ℂ)).const_mul Complex.I)).add_const (Y η)
  simp only [sub_self,mul_zero,add_zero,zero_add] at ht
  apply ht.congr
  intro n
  have h := heη n
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
  change _ = marks[Y | history n] η
  change marks[Y | history n] η-Y η =
    marks[lift (fun η => (Y η).re) | history n] η-((Y η).re : ℂ) +
      Complex.I * (marks[lift (fun η => (Y η).im) | history n] η-((Y η).im : ℂ)) at h
  linear_combination -h

theorem integrable_condExp_L1_limit (Y : MarkSample → ℂ) (hY : Integrable Y marks) :
    Tendsto (fun n : ℕ => eLpNorm (marks[Y | history n]-Y) 1 marks) atTop (𝓝 0) := by
  let f := hY.aestronglyMeasurable.mk Y
  have he : Y =ᵐ[marks] f := hY.aestronglyMeasurable.ae_eq_mk
  have hf : Integrable f marks := hY.congr he
  have ht := condExp_L1_limit f hf hY.aestronglyMeasurable.stronglyMeasurable_mk
  have hn (n : ℕ) : eLpNorm (marks[Y | history n]-Y) 1 marks =
      eLpNorm (marks[f | history n]-f) 1 marks :=
    eLpNorm_congr_ae ((condExp_congr_ae he).sub he)
  simpa only [hn] using ht

theorem integrable_condExp_ae_limit (Y : MarkSample → ℂ) (hY : Integrable Y marks) :
    ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => marks[Y | history n] η) atTop (𝓝 (Y η)) := by
  let f := hY.aestronglyMeasurable.mk Y
  have he : Y =ᵐ[marks] f := hY.aestronglyMeasurable.ae_eq_mk
  have hf : Integrable f marks := hY.congr he
  have ht := condExp_ae_limit f hf hY.aestronglyMeasurable.stronglyMeasurable_mk
  have hn : ∀ n : ℕ, marks[Y | history n] =ᵐ[marks] marks[f | history n] :=
    fun n => condExp_congr_ae he
  filter_upwards [ht,he,ae_all_iff.mpr hn] with η hη heη hnη
  rw [← heη] at hη
  exact hη.congr (fun n => (hnη n).symm)

theorem coherent_clark (a : ℝ) (ha : a ≠ 0) (Y : MarkSample → ℂ) :
    ∃ H : Fin 3 → Coefficients, ∀ n : ℕ,
      (fun η => marks[Y | history n] η-(∫ ξ, Y ξ ∂marks)) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n := by
  obtain ⟨H,hH⟩ := RootMarkMartingaleRepresentation.predictable_representation a ha
    (fun n => marks[Y | history n]) (martingale_condExp Y history marks)
  refine ⟨H, fun n => ?_⟩
  have he := hH n
  have h₀ : marks[Y | history 0] = (fun _ => ∫ ξ, Y ξ ∂marks) := by
    rw [RootMarkFiniteClark.history_zero, condExp_bot]
  rw [h₀] at he
  exact he

theorem infinite_clark (a : ℝ) (ha : a ≠ 0) (Y : MarkSample → ℂ)
    (hY : Integrable Y marks) :
    ∃ H : Fin 3 → Coefficients,
      (∀ n : ℕ, (fun η => marks[Y | history n] η-(∫ ξ, Y ξ ∂marks)) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n) ∧
      Tendsto (fun n : ℕ => eLpNorm
        (RootMarkItoIsometry.totalIntegral a H n - (fun η => Y η-(∫ ξ, Y ξ ∂marks)))
        1 marks) atTop (𝓝 0) ∧
      ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => RootMarkItoIsometry.totalIntegral a H n η)
        atTop (𝓝 (Y η-(∫ ξ, Y ξ ∂marks))) := by
  obtain ⟨H,hH⟩ := coherent_clark a ha Y
  refine ⟨H,hH,?_,?_⟩
  · have he (n : ℕ) :
        eLpNorm (RootMarkItoIsometry.totalIntegral a H n - (fun η => Y η-(∫ ξ, Y ξ ∂marks)))
          1 marks = eLpNorm (marks[Y | history n]-Y) 1 marks := by
      apply eLpNorm_congr_ae
      filter_upwards [hH n] with η hη
      simp only [Pi.sub_apply]
      change marks[Y | history n] η-(∫ ξ, Y ξ ∂marks) = _ at hη
      rw [← hη]
      ring
    simpa only [he] using integrable_condExp_L1_limit Y hY
  · filter_upwards [integrable_condExp_ae_limit Y hY,ae_all_iff.mpr hH] with η hη heη
    exact (hη.sub_const (∫ ξ, Y ξ ∂marks)).congr (fun n => heη n)

end OperatorDerivativeRewrite.Foundation.RootMarkComplexClarkLimit
