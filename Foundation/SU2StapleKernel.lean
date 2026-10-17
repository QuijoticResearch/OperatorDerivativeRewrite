import Foundation.SU2StapleExtremes
import Foundation.MeasurableExponentialKernel

/-! A measurable Markov kernel on actual finite SU(2) staple configurations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2StapleKernel
open QuaternionSU2Representation SU2TraceHessianModel SU2StaplePolar SU2StapleTiltLaw
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*}

def exponent (s : Finset ι) (β : ℝ) (U : ι → SU2) (A : SU2) : ℝ :=
  (β/2) * traceReal ((A : M2) * staple s U)

theorem exponent_measurable (s : Finset ι) (β : ℝ) :
    Measurable (Function.uncurry (exponent s β)) := by
  have hA : Measurable (fun p : (ι → SU2) × SU2 => (p.2 : M2)) :=
    measurable_subtype_coe.comp measurable_snd
  have ha (i j : Fin 2) : Measurable (fun p : (ι → SU2) × SU2 => (p.2 : M2) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  have hs (i j : Fin 2) : Measurable (fun p : (ι → SU2) × SU2 => staple s p.1 i j) := by
    simp only [staple, Matrix.sum_apply]
    apply Finset.measurable_sum
    intro k hk
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_subtype_coe.comp ((measurable_pi_apply k).comp measurable_fst)))
  have hc := (((ha 0 0).mul (hs 0 0)).add ((ha 0 1).mul (hs 1 0))).add
    (((ha 1 0).mul (hs 0 1)).add ((ha 1 1).mul (hs 1 1)))
  change Measurable (fun p : (ι → SU2) × SU2 =>
    (β/2) * traceReal ((p.2 : M2) * staple s p.1))
  simpa only [traceReal, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Function.comp_apply, Pi.add_apply, Pi.mul_apply] using
      (Complex.measurable_re.comp hc).const_mul (β/2)

theorem exponent_bound (s : Finset ι) (β : ℝ) (U : ι → SU2) (A : SU2) :
    |exponent s β U A| ≤ |β| * (s.card : ℝ) := by
  rw [exponent, wilson_exponent, concentration, abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (|β| * ‖quaternionSum s U‖) * 1 :=
      mul_le_mul_of_nonneg_left (axis_bound _ _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (radius_bound s U) (abs_nonneg β)

variable (ν : Measure SU2) [IsProbabilityMeasure ν]

theorem exponential_integrable (s : Finset ι) (β : ℝ) (U : ι → SU2) :
    Integrable (fun A => Real.exp (exponent s β U A)) ν := by
  have hm : Measurable (exponent s β U) :=
    (exponent_measurable s β).of_uncurry_left
  apply Integrable.mono' (integrable_const (Real.exp (|β| * (s.card : ℝ))))
    hm.exp.aestronglyMeasurable
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (exponent_bound s β U A))

def kernel (s : Finset ι) (β : ℝ) : Kernel (ι → SU2) SU2 :=
  MeasurableExponentialKernel.kernel ν (exponent s β)

theorem kernel_markov (s : Finset ι) (β : ℝ) : IsMarkovKernel (kernel ν s β) :=
  MeasurableExponentialKernel.kernel_markov ν (exponent s β)
    (exponent_measurable s β) (exponential_integrable ν s β)

theorem kernel_probability (s : Finset ι) (β : ℝ) (U : ι → SU2) :
    IsProbabilityMeasure (kernel ν s β U) :=
  MeasurableExponentialKernel.kernel_probability ν (exponent s β)
    (exponent_measurable s β) (exponential_integrable ν s β) U

variable [ν.IsHaarMeasure]

omit [IsProbabilityMeasure ν] in
theorem partition_identity (s : Finset ι) (β : ℝ) (U : ι → SU2) :
    MeasurableExponentialKernel.partition ν (exponent s β) U =
      BoundedExponentialTiltResponse.partition ν halfTrace (concentration s U β) := by
  have h : (fun A => Real.exp (exponent s β U A)) = fun A =>
      Real.exp (concentration s U β * axis (orientation (quaternionSum s U)) A) := by
    funext A
    rw [exponent, wilson_exponent]
  rw [MeasurableExponentialKernel.partition, h]
  simpa only [BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted, one_mul] using
      partition_axis ν (orientation (quaternionSum s U)) (concentration s U β)

theorem kernel_eq_stapleLaw (s : Finset ι) (β : ℝ) (U : ι → SU2) :
    kernel ν s β U = stapleLaw ν s U β := by
  rw [kernel, MeasurableExponentialKernel.kernel_apply ν _ (exponent_measurable s β),
    stapleLaw_density]
  congr 1
  funext A
  rw [MeasurableExponentialKernel.density, partition_identity]
  rfl

theorem kernel_halfTrace_map (s : Finset ι) (β : ℝ) (U : ι → SU2) :
    (kernel ν s β U).map (fun A => orientation (quaternionSum s U) * A) =
      BoundedExponentialTiltResponse.tiltedMeasure ν halfTrace (concentration s U β) := by
  rw [kernel_eq_stapleLaw]
  exact stapleLaw_map ν s U β

end OperatorDerivativeRewrite.Foundation.SU2StapleKernel
