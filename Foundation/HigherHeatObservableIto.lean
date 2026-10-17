import Foundation.HigherHeatObservableGenerator
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The ordinary positive-time observable Ito identity for actual higher-heat expectations. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatObservableIto
open HigherHeatL2 HigherHeatGenerator HigherHeatSpatialGenerator HigherHeatSchwartzTransition
open HigherHeatSchwartzCalculus

def flow (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t ξ : ℝ) : ℂ :=
  𝓕 f ξ*(Real.exp (-t*weight m ξ):ℂ)

def flowDerivative (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t ξ : ℝ) : ℂ :=
  spectral m f ξ*(Real.exp (-t*weight m ξ):ℂ)

theorem weight_nonnegative (m : ℕ) (ξ : ℝ) : 0 ≤ weight m ξ := by
  unfold weight
  rw [pow_mul]
  positivity

theorem flow_measurable (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t : ℝ) : Measurable (flow m f t) := by
  apply Continuous.measurable
  unfold flow weight
  fun_prop

theorem flow_hasDerivAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t ξ : ℝ) :
    HasDerivAt (fun s : ℝ => flow m f s ξ) (flowDerivative m f t ξ) t := by
  have hd := ((((hasDerivAt_id t).neg).mul_const (weight m ξ)).exp).ofReal_comp
  convert hd.const_mul (𝓕 f ξ) using 1
  · funext s
    simp only [flow,Pi.neg_apply,id_eq]
  · simp only [flowDerivative,spectral_apply,Pi.neg_apply,id_eq,Complex.ofReal_mul,
      Complex.ofReal_neg,Complex.ofReal_one]
    ring

theorem flowDerivative_bound (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t : ℝ) (ht : 0 ≤ t) (ξ : ℝ) :
    ‖flowDerivative m f t ξ‖ ≤ ‖spectral m f ξ‖ := by
  rw [flowDerivative,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (weight_nonnegative m ξ))

theorem flow_integrable (m : ℕ) (f : 𝓢(ℝ,ℂ)) (t : ℝ) (ht : 0 ≤ t) : Integrable (flow m f t) := by
  refine (𝓕 f).integrable.norm.mono' (flow_measurable m f t).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ξ => by
    rw [flow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (weight_nonnegative m ξ))

theorem mean_eq_flow (m : ℕ) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    mean m t f=∫ ξ : ℝ, flow m f t ξ := by
  unfold mean
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only
    rw [symbol_even]
    rfl

theorem flowDerivative_integral (m : ℕ) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    (∫ ξ : ℝ, flowDerivative m f t ξ)=mean m t (differential m f) := by
  rw [mean_eq_flow]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only [flowDerivative,flow]
    rw [differential_fourier]

theorem flow_integral_hasDerivAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => ∫ ξ : ℝ, flow m f t ξ)
      (∫ ξ : ℝ, flowDerivative m f T ξ) T := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := flow m f) (F' := flowDerivative m f) (μ := volume)
    (bound := fun ξ => ‖spectral m f ξ‖) (s := Set.Ioi 0)
    (isOpen_Ioi.mem_nhds hT)
    (Eventually.of_forall fun t => (flow_measurable m f t).aestronglyMeasurable)
    (flow_integrable m f T hT.le)
    (by apply Continuous.aestronglyMeasurable; unfold flowDerivative weight; fun_prop)
    (Eventually.of_forall fun ξ => fun t ht => flowDerivative_bound m f t ht.le ξ)
    (spectral m f).integrable.norm
    (Eventually.of_forall fun ξ => fun t _ => flow_hasDerivAt m f t ξ)).2

theorem observable_hasDerivAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => mean m t.toNNReal f) (mean m T.toNNReal (differential m f)) T := by
  have hd := flow_integral_hasDerivAt m f T hT
  have hp : ∀ᶠ t : ℝ in 𝓝 T, 0 < t := isOpen_Ioi.mem_nhds hT
  have he : (fun t : ℝ => mean m t.toNNReal f)=ᶠ[𝓝 T]
      (fun t : ℝ => ∫ ξ : ℝ, flow m f t ξ) := by
    filter_upwards [hp] with t ht
    rw [mean_eq_flow,Real.coe_toNNReal t ht.le]
  have hD := hd.congr_of_eventuallyEq he
  have hval : (∫ ξ : ℝ, flowDerivative m f T ξ)=mean m T.toNNReal (differential m f) := by
    simpa only [Real.coe_toNNReal T hT.le] using flowDerivative_integral m T.toNNReal f
  rw [hval] at hD
  exact hD

theorem mean_smul (m : ℕ) (t : ℝ≥0) (c : ℂ) (f : 𝓢(ℝ,ℂ)) : mean m t (c • f)=c*mean m t f := by
  unfold mean
  simp only [FourierTransform.fourier_smul,SchwartzMap.smul_apply,smul_eq_mul]
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem observable_ito (m : ℕ) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => mean m t.toNNReal f)
      ((-1:ℂ)^(m+1)*mean m T.toNNReal (jet (2*m) f)) T := by
  simpa only [differential,mean_smul] using observable_hasDerivAt m f T hT

theorem actual_signed_observable_deriv (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) (T : ℝ) (hT : 0 < T) :
    deriv (fun t : ℝ => mean m t.toNNReal f) T=
      (-1:ℂ)^(m+1)*(∫ᵛ x : ℝ, jet (2*m) f x
        ∂<•HigherHeatSignedLaws.law m hm T.toNNReal (Real.toNNReal_pos.mpr hT)) := by
  rw [(observable_ito m f T hT).deriv,mean_eq_signed_integral m hm T.toNNReal
    (Real.toNNReal_pos.mpr hT) (jet (2*m) f)]

end OperatorDerivativeRewrite.Foundation.HigherHeatObservableIto
