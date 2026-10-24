import Foundation.GaussianDensityTranslation
import Foundation.GaussianDensity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual Gaussian translation and differentiation for bounded continuous
real-Banach-valued observables. Every derivative majorant is integrable under
the ORIGINAL standard Gaussian; no differentiability of the observable is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundedTiltDerivative
open GaussianCore GaussianRandomDensityKernel GaussianDensityTranslation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def weighted (F : ℝ → E) (t : ℝ) : E := ∫ z, kernel t z • F z ∂γ

theorem translation (F : ℝ → E) (hF : Continuous F) (t : ℝ) :
    (∫ z, F (z+t) ∂γ) = weighted F (-t) := by
  have hl : HasLaw (fun z : ℝ => z+t) (gaussianReal t 1) γ := by
    refine ⟨by fun_prop, ?_⟩
    simp [γ,gaussianReal_map_add_const]
  have ht : tilted (-t) = gaussianReal t 1 := by rw [tilted_eq_gaussian]; simp
  calc
    _ = ∫ z, F z ∂gaussianReal t 1 := hl.integral_comp hF.aestronglyMeasurable
    _ = ∫ z, F z ∂tilted (-t) := by rw [ht]
    _ = weighted F (-t) := by
      rw [tilted,integral_withDensity_eq_integral_toReal_smul
        (kernel_measurable (-t)).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (ENNReal.ofReal (kernel (-t) z)).toReal • F z = kernel (-t) z • F z
        rw [ENNReal.toReal_ofReal (kernel_positive _ _).le]

private theorem kernel_derivative (t z : ℝ) :
    HasDerivAt (fun s => kernel s z) ((-z-t)*kernel t z) t := by
  have hd := (((hasDerivAt_id t).neg.mul_const z).sub
    (((hasDerivAt_id t).pow 2).div_const 2)).exp
  convert hd using 1 <;> simp [kernel] <;> ring

private theorem envelope_integrable :
    Integrable (fun z : ℝ => (|z|+1)*(Real.exp z+Real.exp (-z))) γ := by
  have hp : MemLp (fun z : ℝ => |z|+1) 2 γ :=
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)).norm).add (memLp_const 1)
  have he : MemLp (fun z : ℝ => Real.exp z+Real.exp (-z)) 2 γ := by
    exact ((gaussian_exp_memLp_two 1).add (gaussian_exp_memLp_two (-1))).ae_eq
      (Filter.Eventually.of_forall fun z => by simp only [Pi.add_apply,one_mul,neg_one_mul])
  exact hp.integrable_mul he

theorem weighted_hasDerivAt_zero (F : ℝ → E) (hF : Continuous F) (M : ℝ)
    (hM : 0 ≤ M) (hB : ∀ z, ‖F z‖ ≤ M) :
    HasDerivAt (weighted F) (-(∫ z : ℝ, z • F z ∂γ)) 0 := by
  let A : ℝ → ℝ → E := fun t z => kernel t z • F z
  let D : ℝ → ℝ → E := fun t z => ((-z-t)*kernel t z) • F z
  have hmeas (t : ℝ) : AEStronglyMeasurable (A t) γ :=
    ((kernel_measurable t).stronglyMeasurable.smul hF.stronglyMeasurable).aestronglyMeasurable
  have hi : Integrable (A 0) γ := by
    apply (integrable_const M).mono' (hmeas 0)
    exact Filter.Eventually.of_forall fun z => by simpa [A,kernel] using hB z
  have hdmeas : AEStronglyMeasurable (D 0) γ := by
    apply Continuous.aestronglyMeasurable
    exact ((continuous_neg.sub continuous_const).mul
      ((kernel_continuous.comp (continuous_const.prodMk continuous_id)))).smul hF
  have hbound : ∀ᵐ z ∂γ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      ‖D t z‖ ≤ M*((|z|+1)*(Real.exp z+Real.exp (-z))) := by
    filter_upwards with z t ht
    have ha : |t| ≤ 1 := (abs_lt.mpr ht).le
    have hc : |-z-t| ≤ |z|+1 := by
      have h := abs_sub (-z) t
      rw [abs_neg] at h
      exact h.trans (add_le_add le_rfl ha)
    calc
      _ = (|-z-t| * kernel t z)*‖F z‖ := by
        change ‖((-z-t)*kernel t z) • F z‖ = _
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos (kernel_positive _ _)]
      _ ≤ ((|z|+1)*(Real.exp z+Real.exp (-z)))*M :=
        mul_le_mul (mul_le_mul hc (kernel_bound t z ha) (kernel_positive _ _).le
          (by positivity)) (hB z) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdiff : ∀ᵐ z ∂γ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => A s z) (D t z) t :=
    Filter.Eventually.of_forall fun z t _ => (kernel_derivative t z).smul_const (F z)
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := D) (μ := γ) (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall hmeas) hi hdmeas hbound (envelope_integrable.const_mul M) hdiff
  have he : (∫ z, D 0 z ∂γ) = -(∫ z : ℝ, z • F z ∂γ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by simp [D,kernel,neg_smul]
  rw [he] at hd
  exact hd

theorem translate_hasDerivAt_zero (F : ℝ → E) (hF : Continuous F) (M : ℝ)
    (hM : 0 ≤ M) (hB : ∀ z, ‖F z‖ ≤ M) :
    HasDerivAt (fun t => ∫ z : ℝ, F (z+t) ∂γ) (∫ z : ℝ, z • F z ∂γ) 0 := by
  have hd := (weighted_hasDerivAt_zero F hF M hM hB).scomp_of_eq (0 : ℝ)
    (hasDerivAt_neg (0 : ℝ)) (by simp)
  have he : (fun t : ℝ => weighted F (-t)) = fun t => ∫ z : ℝ, F (z+t) ∂γ :=
    funext fun t => (translation F hF t).symm
  simpa only [Function.comp_def,he,neg_one_smul,neg_neg] using hd

end OperatorDerivativeRewrite.Foundation.GaussianBoundedTiltDerivative
