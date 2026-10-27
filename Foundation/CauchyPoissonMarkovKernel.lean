import Foundation.CauchyPoissonKernelComposition
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Group.Circle
/-! Actual measurable Markov transition kernels on Circle for the Cauchy/sine
drift flow. Exact Chapman-Kolmogorov composition, actual-law identification
and invariant probability are proved. Feller continuity, closed-generator
domains and path construction remain separate obligations. -/
noncomputable section
open Complex MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonMarkovKernel
open CauchyPoissonFlow CauchyPoissonKernelComposition

theorem circle_exp_coe (θ : ℝ) : (Circle.exp θ : ℂ) = circleMap 0 1 θ := by
  simp [Circle.coe_exp,circleMap]

theorem weight_measurable (q t : ℝ) :
    Measurable (fun p : Circle × ℝ => ENNReal.ofReal (poleWeight (evolution q t p.1) p.2)) := by
  unfold poleWeight evolution flow numerator denominator poissonKernel
  fun_prop

def angleKernel (q t : ℝ) : Kernel Circle ℝ :=
  (Kernel.const Circle (volume.restrict (Set.Ioc 0 (2*Real.pi)))).withDensity
    (fun z θ => ENNReal.ofReal (poleWeight (evolution q t z) θ))

theorem angleKernel_apply (q t : ℝ) (z : Circle) :
    angleKernel q t z = poleLaw (evolution q t z) := by
  rw [angleKernel,Kernel.withDensity_apply _ (weight_measurable q t)]
  rfl

theorem angleKernel_markov (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    IsMarkovKernel (angleKernel q t) := by
  constructor
  intro z
  rw [angleKernel_apply]
  exact poleLaw_probability _ (evolution_strict_disk q t hq ht z (by simp))

def kernel (q t : ℝ) : Kernel Circle Circle :=
  if t=0 then Kernel.id else (angleKernel q t).map Circle.exp

theorem kernel_zero (q : ℝ) : kernel q 0 = Kernel.id := by simp [kernel]

theorem kernel_positive_apply (q t : ℝ) (ht : 0 < t) (z : Circle) :
    kernel q t z = Measure.map Circle.exp (poleLaw (evolution q t z)) := by
  rw [kernel,if_neg (ne_of_gt ht),Kernel.map_apply _ Circle.exp.continuous.measurable,angleKernel_apply]

theorem kernel_markov (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) : IsMarkovKernel (kernel q t) := by
  unfold kernel
  split_ifs with h
  · infer_instance
  · let := angleKernel_markov q t hq (lt_of_le_of_ne ht (Ne.symm h))
    exact Kernel.IsMarkovKernel.map _ Circle.exp.continuous.measurable

theorem kernel_matches_actual (q t : ℝ) (ht : 0 ≤ t) (z : Circle) :
    Measure.map (fun w : Circle => (w:ℂ)) (kernel q t z) = circleTransitionLaw q t z := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simp [kernel_zero,circleTransitionLaw_zero,Kernel.id_apply]
  · rw [kernel_positive_apply q t h z,circleTransitionLaw,if_neg (ne_of_gt h),
      Measure.map_map (by fun_prop) Circle.exp.continuous.measurable]
    congr 1
    funext θ
    exact circle_exp_coe θ

theorem integral_poleLaw_real (v : ℂ) (hv : ‖v‖ < 1) (f : ℝ → ℝ) :
    (∫ θ, f θ ∂poleLaw v) = (2*Real.pi)⁻¹ *
      ∫ θ in (0:ℝ)..2*Real.pi, poissonKernel 0 v (circleMap 0 1 θ) * f θ := by
  rw [poleLaw,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (le_of_lt (poleWeight_positive v hv _)),smul_eq_mul]
    rw [← intervalIntegral.integral_of_le (by positivity)]
    simp only [poleWeight,mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  · exact ENNReal.measurable_ofReal.comp (poleWeight_continuous v hv).measurable
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem integral_next_density (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l < 1)
    (v : ℂ) (hv : ‖v‖ < 1) (ψ : ℝ) :
    (∫ θ, poleWeight (flow q l (circleMap 0 1 θ)) ψ ∂poleLaw v) =
      poleWeight (flow q l v) ψ := by
  have h := poisson_density_average q l hq hl hl1 (circleMap 0 1 ψ) (by simp) v hv
  rw [integral_poleLaw_real v hv]
  simp only [poleWeight]
  simp_rw [mul_left_comm (poissonKernel 0 v (circleMap 0 1 _)) ((2*Real.pi)⁻¹)]
  rw [intervalIntegral.integral_const_mul]
  change (2*Real.pi)⁻¹ * ((2*Real.pi)⁻¹ * _) = _
  exact congrArg (fun x : ℝ => (2*Real.pi)⁻¹*x) h

theorem next_density_integrable (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l < 1)
    (v : ℂ) (hv : ‖v‖ < 1) (ψ : ℝ) :
    Integrable (fun θ => poleWeight (flow q l (circleMap 0 1 θ)) ψ) (poleLaw v) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_next_density q l hq hl hl1 v hv ψ]
  exact ne_of_gt (poleWeight_positive _ (flow_strict_disk q l hq hl hl1 v hv.le) ψ)

theorem lintegral_next_density (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l < 1)
    (v : ℂ) (hv : ‖v‖ < 1) (ψ : ℝ) :
    (∫⁻ θ, ENNReal.ofReal (poleWeight (flow q l (circleMap 0 1 θ)) ψ) ∂poleLaw v) =
      ENNReal.ofReal (poleWeight (flow q l v) ψ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (next_density_integrable q l hq hl hl1 v hv ψ)
    (Filter.Eventually.of_forall (fun θ => (poleWeight_positive _
      (flow_strict_disk q l hq hl hl1 _ (by simp)) ψ).le)),
    integral_next_density q l hq hl hl1 v hv ψ]

theorem mixture_set (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (v : ℂ) (hv : ‖v‖ < 1) (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ w, angleKernel q t w B ∂Measure.map Circle.exp (poleLaw v)) =
      poleLaw (evolution q t v) B := by
  let := poleLaw_probability v hv
  rw [MeasureTheory.lintegral_map ((angleKernel q t).measurable_coe hB) Circle.exp.continuous.measurable]
  have he (θ : ℝ) : angleKernel q t (Circle.exp θ) B =
      ∫⁻ ψ in B, ENNReal.ofReal (poleWeight (evolution q t (circleMap 0 1 θ)) ψ)
        ∂volume.restrict (Set.Ioc 0 (2*Real.pi)) := by
    rw [angleKernel_apply,circle_exp_coe,poleLaw,withDensity_apply _ hB]
  simp_rw [he]
  rw [lintegral_lintegral_swap]
  · conv_rhs => rw [poleLaw,withDensity_apply _ hB]
    apply lintegral_congr
    intro ψ
    exact lintegral_next_density q (decay q t) hq (decay_range q t hq ht.le).1
      (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (rate_pos q hq)) ht)) v hv ψ
  · apply Measurable.aemeasurable
    unfold Function.uncurry poleWeight evolution flow numerator denominator poissonKernel
    fun_prop

theorem kernel_composition_positive (q s t : ℝ) (hq : |q| < 1) (hs : 0 < s) (ht : 0 < t) :
    (kernel q t) ∘ₖ (kernel q s) = kernel q (s+t) := by
  ext z A hA
  rw [Kernel.comp_apply' _ _ _ hA,kernel_positive_apply q s hs z]
  have he (w : Circle) : kernel q t w A = angleKernel q t w (Circle.exp ⁻¹' A) := by
    rw [kernel_positive_apply q t ht,Measure.map_apply Circle.exp.continuous.measurable hA,
      angleKernel_apply]
  simp_rw [he]
  rw [mixture_set q t hq ht _ (evolution_strict_disk q s hq hs z (by simp)) _
      (Circle.exp.continuous.measurable hA),
    kernel_positive_apply q (s+t) (add_pos hs ht),Measure.map_apply Circle.exp.continuous.measurable hA]
  rw [← evolution_add q t s hq ht.le hs.le z (by simp),add_comm t s]

theorem kernel_composition (q s t : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (kernel q t) ∘ₖ (kernel q s) = kernel q (s+t) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s; simp [kernel_zero]
  rcases eq_or_lt_of_le ht with h' | h'
  · subst t; simp [kernel_zero]
  exact kernel_composition_positive q s t hq h h'

def invariantLaw (q : ℝ) : Measure Circle := Measure.map Circle.exp (poleLaw q)

theorem invariantLaw_probability (q : ℝ) (hq : |q| < 1) : IsProbabilityMeasure (invariantLaw q) := by
  let := poleLaw_probability (q:ℂ) (by simpa using hq)
  unfold invariantLaw
  infer_instance

theorem kernel_invariant_positive (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    (invariantLaw q).bind (kernel q t) = invariantLaw q := by
  ext A hA
  rw [Measure.bind_apply hA (kernel q t).aemeasurable]
  have he (w : Circle) : kernel q t w A = angleKernel q t w (Circle.exp ⁻¹' A) := by
    rw [kernel_positive_apply q t ht,Measure.map_apply Circle.exp.continuous.measurable hA,
      angleKernel_apply]
  simp_rw [he]
  rw [invariantLaw,mixture_set q t hq ht _ (by simpa using hq) _ (Circle.exp.continuous.measurable hA)]
  rw [evolution,flow_fixed q _ hq (decay_range q t hq ht.le).1 (decay_range q t hq ht.le).2]
  exact (Measure.map_apply Circle.exp.continuous.measurable hA).symm

theorem kernel_invariant (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    (invariantLaw q).bind (kernel q t) = invariantLaw q := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    rw [kernel_zero]
    have he : (⇑(Kernel.id : Kernel Circle Circle)) = Measure.dirac := funext (fun z => Kernel.id_apply z)
    rw [he,Measure.bind_dirac]
  · exact kernel_invariant_positive q t hq h

end OperatorDerivativeRewrite.Foundation.CauchyPoissonMarkovKernel
