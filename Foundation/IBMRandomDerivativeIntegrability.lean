import Foundation.IBMRandomTimeHilbert
import Foundation.IBMOffsetTranslation
import Foundation.IBMJointMollifierGaussian

/-! Global square integrability at the independent Brownian clock, including
the signed first and second derivative kernels. Values remain Gaussian L²
classes, rather than pointwise random-time evaluations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMRandomDerivativeIntegrability
open InfiniteGaussian IBMContinuousScenery IBMContinuousBulkVariance
open IBMRandomTimeHilbert IBMOffsetTranslation GaussianTimeProcess
open IBMJointMollifierGaussian

/-- Absolute kernel mass on a fixed offset window. -/
def kernelMass (R : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ r in Set.Icc (-R) R, |ρ (-r)|

/-- Signed kernels obey a global Brownian growth estimate. No positivity or
mass-one hypothesis on the kernel is used. -/
theorem offsetScenery_norm_sq_le {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    ‖offsetScenery (-R) R x ρ‖^2 ≤ (kernelMass R ρ)^2 * (|x|+R) := by
  have hroot : 0 ≤ |x|+R := by positivity
  have hnorm (r : ℝ) (hr : r ∈ Set.Icc (-R) R) :
      ‖sourceScenery (x+r)‖ ≤ Real.sqrt (|x|+R) := by
    have habs : |r| ≤ R := abs_le.mpr hr
    have hs := sourceScenery_norm_sq (x+r)
    have ha := abs_add_le x r
    nlinarith [Real.sq_sqrt hroot, Real.sqrt_nonneg (|x|+R),
      norm_nonneg (sourceScenery (x+r))]
  have hmajor : IntegrableOn (fun r : ℝ => |ρ (-r)| * Real.sqrt (|x|+R))
      (Set.Icc (-R) R) volume :=
    (((hρ.comp continuous_neg).abs).mul continuous_const).integrableOn_Icc
  have hn : ‖offsetScenery (-R) R x ρ‖ ≤
      kernelMass R ρ * Real.sqrt (|x|+R) := by
    rw [offsetScenery_eq_integral]
    calc
      ‖∫ r in Set.Icc (-R) R, ρ (-r) • sourceScenery (x+r)‖ ≤
          ∫ r in Set.Icc (-R) R, |ρ (-r)| * Real.sqrt (|x|+R) := by
        apply norm_integral_le_of_norm_le hmajor
        apply ae_restrict_of_forall_mem measurableSet_Icc
        intro r hr
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hnorm r hr) (abs_nonneg _)
      _ = _ := by rw [integral_mul_const]; rfl
  have hm : 0 ≤ kernelMass R ρ := integral_nonneg fun _ => abs_nonneg _
  have hsq := mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [Real.sq_sqrt hroot]

/-- Global growth bound for the original whole-line Gaussian convolution. -/
theorem wholeLineScenery_norm_sq_le {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : ∀ z, R < |z| → ρ z = 0) (x : ℝ) :
    ‖wholeLineScenery ρ x‖^2 ≤ (kernelMass R ρ)^2 * (|x|+R) := by
  have he : wholeLineScenery ρ x = offsetScenery (-R) R x ρ := by
    apply wholeLineScenery_eq_offsetScenery
    · linarith
    · intro r hr
      apply hsupp
      by_contra! h
      apply hr
      have hh := abs_le.mp h
      constructor <;> linarith
  rw [he]
  exact offsetScenery_norm_sq_le hρ hR x

def randomKernelClass (ρ : ℝ → ℝ) (t : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  wholeLineScenery ρ |process t ω|

/-- Fixed-time evaluation of every compactly supported C¹ kernel, including
signed derivative kernels, is square integrable as a Gaussian-L²-valued map. -/
theorem randomKernelClass_memLp {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (t : ℝ≥0) :
    MemLp (randomKernelClass ρ t) 2 gaussianProduct := by
  have hcont : Continuous (wholeLineScenery ρ) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (wholeLineScenery_hasDerivAt hc hρ x).continuousAt
  have hmeas : StronglyMeasurable (randomKernelClass ρ t) :=
    hcont.stronglyMeasurable.comp_measurable
      (continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable)
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hsupp : ∀ z, R < |z| → ρ z = 0 := by
    intro z hz
    by_contra hne
    have hm : z ∈ tsupport ρ := subset_closure hne
    have hh := hbound z hm
    simpa only [Real.norm_eq_abs] using (not_lt_of_ge hh hz)
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
  have hi : Integrable (fun ω => |process t ω|) gaussianProduct :=
    (process_memLp t 1 (by simp)).integrable (by norm_num) |>.abs
  have hmajor : Integrable (fun ω => (kernelMass R ρ)^2 * (|process t ω|+R))
      gaussianProduct := (hi.add (integrable_const R)).const_mul _
  apply Integrable.mono' hmajor
  · exact (hmeas.norm.measurable.pow_const 2).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    change |‖wholeLineScenery ρ |process t ω|‖^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [abs_abs] using
      wholeLineScenery_norm_sq_le hρ.continuous hR.le hsupp |process t ω|

/-- In particular the actual U, V and W convolutions, at every fixed Brownian
clock time, belong to L²(clock; L²(scenery)). This does not interchange a
representative with random-time evaluation on the product sample space. -/
theorem randomDerivativeClass_memLp (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    MemLp (randomKernelClass (derivativeKernel n i) t) 2 gaussianProduct := by
  have hc : HasCompactSupport (derivativeKernel n i) := by
    unfold derivativeKernel
    split_ifs
    · exact IBMMollifier.kernel_compactSupport n
    · exact (IBMMollifier.kernel_compactSupport n).deriv
    · exact (IBMMollifier.kernel_compactSupport n).deriv.deriv
  have hρ : ContDiff ℝ 1 (derivativeKernel n i) := by
    have h := IBMMollifier.kernel_smooth n
    have h' := (contDiff_infty_iff_deriv.mp h).2
    have h'' := (contDiff_infty_iff_deriv.mp h').2
    unfold derivativeKernel
    split_ifs
    · exact h.of_le (by norm_num)
    · exact h'.of_le (by norm_num)
    · exact h''.of_le (by norm_num)
  exact randomKernelClass_memLp hc hρ t

end OperatorDerivativeRewrite.Foundation.IBMRandomDerivativeIntegrability


