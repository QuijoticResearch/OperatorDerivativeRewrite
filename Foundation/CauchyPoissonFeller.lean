import Foundation.CauchyPoissonMarkovKernel
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
/-! Actual circle transition operators preserve continuous observables and form a
complex-linear contraction semigroup. This proves spatial Feller continuity only;
strong continuity in time and identification of the closed generator remain open. -/
noncomputable section
open Complex MeasureTheory ProbabilityTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonFeller
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel

theorem evolution_circle_continuous (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    Continuous (fun z : Circle => evolution q t z) := by
  unfold evolution flow
  apply Continuous.div (by unfold numerator; fun_prop) (by unfold denominator; fun_prop)
  intro z
  exact denominator_ne_zero q _ hq (decay_range q t hq ht).1 (decay_range q t hq ht).2 z (by simp)

theorem joint_weight_continuous (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    Continuous (fun p : Circle × ℝ => poleWeight (evolution q t p.1) p.2) := by
  have he : Continuous (fun p : Circle × ℝ => evolution q t p.1) :=
    (evolution_circle_continuous q t hq ht.le).comp continuous_fst
  unfold poleWeight poissonKernel
  apply Continuous.const_mul
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  simp only [sub_zero]
  intro hh
  have hn := congrArg norm (sub_eq_zero.mp hh)
  simp only [norm_circleMap_zero,abs_one] at hn
  exact (ne_of_lt (evolution_strict_disk q t hq ht p.1 (by simp))) hn.symm

theorem integral_poleLaw_complex (v : ℂ) (hv : ‖v‖ < 1) (f : ℝ → ℂ) :
    (∫ θ, f θ ∂poleLaw v) = ∫ θ in Set.Icc 0 (2*Real.pi), poleWeight v θ • f θ := by
  rw [poleLaw,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (le_of_lt (poleWeight_positive v hv _))]
    exact integral_Icc_eq_integral_Ioc.symm
  · exact ENNReal.measurable_ofReal.comp (poleWeight_continuous v hv).measurable
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem integral_kernel_formula (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (f : C(Circle,ℂ)) (z : Circle) :
    (∫ w, f w ∂kernel q t z) =
      ∫ θ in Set.Icc 0 (2*Real.pi), poleWeight (evolution q t z) θ • f (Circle.exp θ) := by
  rw [kernel_positive_apply q t ht z,integral_map Circle.exp.continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact integral_poleLaw_complex _ (evolution_strict_disk q t hq ht z (by simp)) _

theorem feller (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (f : C(Circle,ℂ)) :
    Continuous (fun z : Circle => ∫ w, f w ∂kernel q t z) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simpa only [kernel_zero,Kernel.id_apply,integral_dirac] using f.continuous
  · simp_rw [integral_kernel_formula q t hq h f]
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    exact (joint_weight_continuous q t hq h).smul
      (f.continuous.comp (Circle.exp.continuous.comp continuous_snd))

theorem observable_integrable (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) (z : Circle) : Integrable f (kernel q t z) := by
  let := kernel_markov q t hq ht
  exact Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

def transition (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (f : C(Circle,ℂ)) : C(Circle,ℂ) :=
  ⟨fun z => ∫ w, f w ∂kernel q t z, feller q t hq ht f⟩

theorem transition_norm (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (f : C(Circle,ℂ)) :
    ‖transition q t hq ht f‖ ≤ ‖f‖ := by
  let := kernel_markov q t hq ht
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro z
  simpa [transition] using norm_integral_le_of_norm_le_const (μ := kernel q t z) (Filter.Eventually.of_forall f.norm_coe_le_norm)

def operator (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) : C(Circle,ℂ) →L[ℂ] C(Circle,ℂ) :=
  LinearMap.mkContinuous
    { toFun := transition q t hq ht
      map_add' := by
        intro f g
        ext z
        exact integral_add (observable_integrable q t hq ht f z) (observable_integrable q t hq ht g z)
      map_smul' := by
        intro c f
        ext z
        exact integral_smul c (fun w => f w) }
    1 (fun f => by simpa using transition_norm q t hq ht f)

theorem operator_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (f : C(Circle,ℂ)) (z : Circle) :
    operator q t hq ht f z = ∫ w, f w ∂kernel q t z := rfl

theorem operator_contraction (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) : ‖operator q t hq ht‖ ≤ 1 := by
  apply (operator q t hq ht).opNorm_le_bound (by norm_num)
  intro f
  change ‖transition q t hq ht f‖ ≤ 1 * ‖f‖
  simpa using transition_norm q t hq ht f

theorem operator_zero (q : ℝ) (hq : |q| < 1) : operator q 0 hq (by norm_num) = ContinuousLinearMap.id ℂ _ := by
  ext f z
  change (∫ w, f w ∂kernel q 0 z) = f z
  simp [kernel_zero,Kernel.id_apply]

theorem operator_add (q s t : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    operator q (s+t) hq (add_nonneg hs ht) = (operator q s hq hs).comp (operator q t hq ht) := by
  ext f z
  change (∫ w, f w ∂kernel q (s+t) z) = ∫ x, ∫ y, f y ∂kernel q t x ∂kernel q s z
  have hi : Integrable f (((kernel q t) ∘ₖ (kernel q s)) z) := by
    rw [kernel_composition q s t hq hs ht]
    exact observable_integrable q (s+t) hq (add_nonneg hs ht) f z
  simpa only [kernel_composition q s t hq hs ht] using Kernel.integral_comp hi

theorem operator_one (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    operator q t hq ht (1 : C(Circle,ℂ)) = 1 := by
  let := kernel_markov q t hq ht
  ext z
  change (∫ _, (1:ℂ) ∂kernel q t z) = 1
  simp

end OperatorDerivativeRewrite.Foundation.CauchyPoissonFeller
