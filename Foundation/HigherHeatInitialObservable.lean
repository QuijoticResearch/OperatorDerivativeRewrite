import Foundation.HigherHeatObservableIto
import Foundation.HigherHeatSchwartzContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Initial Dirac realization, the right observable generator at zero, and the integrated observable Ito law. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap NNReal Topology Interval
namespace OperatorDerivativeRewrite.Foundation.HigherHeatInitialObservable
open HigherHeatL2 HigherHeatGenerator HigherHeatSpatialGenerator HigherHeatObservableIto HigherHeatSchwartzCalculus

def differenceIntegrand (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t ξ : ℝ) : ℂ :=
  (coefficient (weight m ξ) t:ℂ)*𝓕 f ξ

theorem mean_zero (m : ℕ) (f : 𝓢(ℝ,ℂ)) : mean m 0 f=f 0 := by
  have h := inverse_phase f 0
  simpa only [HigherHeatBackwardFourier.phase_zero,mean,symbol_zero,mul_one] using h

theorem initial_dirac (m : ℕ) (f : 𝓢(ℝ,ℂ)) : mean m 0 f=∫ x : ℝ, f x ∂Measure.dirac 0 := by
  simp [mean_zero]

theorem difference_measurable (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t : ℝ) :
    Measurable (differenceIntegrand m f t) := by
  apply Continuous.measurable
  unfold differenceIntegrand coefficient weight
  fun_prop

theorem difference_bound (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t ξ : ℝ) :
    ‖differenceIntegrand m f t ξ‖ ≤ ‖spectral m f ξ‖ := by
  rw [differenceIntegrand,norm_mul,Complex.norm_real,Real.norm_eq_abs,spectral_apply,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg (weight_nonnegative m ξ)]
  exact mul_le_mul_of_nonneg_right (coefficient_bound (weight m ξ) (weight_nonnegative m ξ) t) (norm_nonneg _)

theorem difference_tendsto (m : ℕ) (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    Tendsto (fun t : ℝ => differenceIntegrand m f t ξ) (𝓝[Set.Ioi 0] 0) (𝓝 (spectral m f ξ)) := by
  have h := ((Complex.continuous_ofReal.tendsto (-weight m ξ)).comp
    (coefficient_tendsto (weight m ξ))).mul (tendsto_const_nhds (x := 𝓕 f ξ))
  simpa only [differenceIntegrand,spectral_apply,Function.comp_apply] using h

theorem difference_integral_tendsto (m : ℕ) (f : 𝓢(ℝ,ℂ)) :
    Tendsto (fun t : ℝ => ∫ ξ : ℝ, differenceIntegrand m f t ξ)
      (𝓝[Set.Ioi 0] 0) (𝓝 (∫ ξ : ℝ, spectral m f ξ)) := by
  exact tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖spectral m f ξ‖)
    (Eventually.of_forall fun t => (difference_measurable m f t).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall (difference_bound m f t))
    (spectral m f).integrable.norm (Eventually.of_forall (difference_tendsto m f))

theorem difference_integral_identification (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t : ℝ) :
    (∫ ξ : ℝ, differenceIntegrand m f t ξ)=t⁻¹ • (mean m t.toNNReal f-mean m 0 f) := by
  have hi := flow_integrable m f (t.toNNReal:ℝ) t.toNNReal.coe_nonneg
  calc
    _ = ∫ ξ : ℝ, t⁻¹ • (flow m f t.toNNReal ξ-𝓕 f ξ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        simp only [differenceIntegrand,coefficient,flow,Complex.real_smul,Complex.ofReal_div,
          Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv]
        ring
    _ = t⁻¹ • (∫ ξ : ℝ, flow m f t.toNNReal ξ-𝓕 f ξ) := integral_smul _ _
    _ = t⁻¹ • ((∫ ξ : ℝ, flow m f t.toNNReal ξ)-(∫ ξ : ℝ, 𝓕 f ξ)) :=
      congrArg (fun z : ℂ => t⁻¹ • z) (integral_sub hi (𝓕 f).integrable)
    _ = _ := by
      rw [mean_eq_flow,mean_eq_flow]
      simp only [flow,NNReal.coe_zero,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,mul_one]

theorem initial_hasDerivWithinAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) :
    HasDerivWithinAt (fun t : ℝ => mean m t.toNNReal f) (differential m f 0) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0:ℝ) \ {0}=Set.Ioi 0 := by
    ext t
    change (0 ≤ t ∧ t ≠ 0) ↔ 0 < t
    constructor
    · rintro ⟨h1,h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le,ne_of_gt h⟩
  rw [hset]
  have he : slope (fun t : ℝ => mean m t.toNNReal f) 0=
      (fun t : ℝ => ∫ ξ : ℝ, differenceIntegrand m f t ξ) := by
    funext t
    rw [slope_def_module,sub_zero,Real.toNNReal_zero,← difference_integral_identification]
  rw [he]
  have h := difference_integral_tendsto m f
  have hval := inverse_phase (differential m f) 0
  simp only [differential_fourier,HigherHeatBackwardFourier.phase_zero,mul_one] at hval
  rw [hval] at h
  exact h

theorem observable_hasDerivWithinAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    HasDerivWithinAt (fun t : ℝ => mean m t.toNNReal f)
      (mean m T.toNNReal (differential m f)) (Set.Ici 0) T := by
  by_cases hp : 0 < T
  · exact (observable_hasDerivAt m f T hp).hasDerivWithinAt
  · have ht0 : T=0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    rw [Real.toNNReal_zero,mean_zero]
    exact initial_hasDerivWithinAt m f

theorem integrated_observable_ito (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) (T : ℝ≥0) :
    (∫ t in (0:ℝ)..(T:ℝ), mean m t.toNNReal (differential m f))=mean m T f-f 0 := by
  have hc : Continuous (fun t : ℝ => mean m t.toNNReal f) :=
    (HigherHeatSchwartzContinuity.mean_continuous m hm f).comp continuous_real_toNNReal
  have hd : Continuous (fun t : ℝ => mean m t.toNNReal (differential m f)) :=
    (HigherHeatSchwartzContinuity.mean_continuous m hm (differential m f)).comp continuous_real_toNNReal
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg hc.continuousOn
    (fun t ht => observable_hasDerivAt m f t ht.1) (hd.intervalIntegrable _ _)
  simpa only [Real.toNNReal_coe,Real.toNNReal_zero,mean_zero] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatInitialObservable
