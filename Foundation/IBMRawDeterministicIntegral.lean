import Foundation.IBMSignedClockCompanion
import Mathlib.Analysis.Normed.Operator.Extend

/-! A genuine bounded deterministic raw-IBM integral on the EXISTING H=1/4
fractional integrand space. Raw finite sums and interval normalization are
identified before completion. No isometry, Gaussian law, or random integrand
extension is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawDeterministicIntegral
open InfiniteGaussian IBMTimeAveragedObservable IBMDeterministicRangeObstruction
open IBMRawTemporalKernel GaussianAbsoluteMoments
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev Domain := FractionalGaussianProcess.integrandSpace (1/4) (by norm_num) (by norm_num)

def kernelVector (t : ℝ≥0) : Domain :=
  FractionalGaussianProcess.kernelVector (1/4) (by norm_num) (by norm_num) t

def reference : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Domain := Finsupp.linearCombination ℝ kernelVector

def finite : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] JointL2 := Finsupp.linearCombination ℝ observed

theorem kernel_inner (s t : ℝ≥0) :
    standardMoment 1 * inner ℝ (kernelVector s) (kernelVector t) = quarterKernel s t := by
  change standardMoment 1 * inner ℝ
    (FractionalGaussianProcess.kernelVector (1/4) (by norm_num) (by norm_num) s)
    (FractionalGaussianProcess.kernelVector (1/4) (by norm_num) (by norm_num) t) = _
  rw [FractionalGaussianProcess.kernelVector_inner]
  norm_num only [show (2:ℝ)*(1/4)=1/2 by norm_num]
  simp only [← Real.sqrt_eq_rpow,quarterKernel]

theorem reference_energy (a : ℝ≥0 →₀ ℝ) :
    standardMoment 1 * ‖reference a‖^2 =
      ∑ i ∈ a.support, ∑ j ∈ a.support, a i*a j*quarterKernel i j := by
  change standardMoment 1 * ‖∑ i ∈ a.support, a i • kernelVector i‖^2 = _
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = a i*a j*(standardMoment 1 * inner ℝ (kernelVector i) (kernelVector j)) := by
      rw [real_inner_comm (kernelVector j) (kernelVector i)]
      ring
    _ = _ := by rw [kernel_inner]

theorem finite_square_bound (a : ℝ≥0 →₀ ℝ) :
    ‖finite a‖^2 ≤ 2*standardMoment 1*‖reference a‖^2 := by
  have h := IBMSignedClockCompanion.finite_energy_bound a.support a (fun t => t)
  change ‖finite a‖^2 ≤ 2*(∑ i ∈ a.support, ∑ j ∈ a.support, a i*a j*quarterKernel i j) at h
  rw [← reference_energy] at h
  nlinarith

def bound : ℝ := Real.sqrt (2*standardMoment 1)

theorem finite_bound (a : ℝ≥0 →₀ ℝ) : ‖finite a‖ ≤ bound * ‖reference a‖ := by
  have hc := IBMPhysicalL2Obstruction.first_absolute_moment_pos
  have hs : ‖finite a‖^2 ≤ (bound*‖reference a‖)^2 := by
    rw [mul_pow]
    change ‖finite a‖^2 ≤ (Real.sqrt (2*standardMoment 1))^2*‖reference a‖^2
    rw [Real.sq_sqrt (by positivity)]
    exact finite_square_bound a
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

theorem reference_dense : DenseRange reference := by
  change Dense (reference.range : Set Domain)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,Submodule.eq_bot_iff]
  simp only [Submodule.mem_orthogonal']
  intro z hz
  apply FractionalGaussianProcess.cameronMartinFunction_injective (1/4)
    (by norm_num) (by norm_num)
  funext t
  change inner ℝ z (kernelVector t) = inner ℝ (0:Domain) (kernelVector t)
  rw [inner_zero_left]
  exact hz _ ⟨Finsupp.single t 1,by
    simp only [reference,Finsupp.linearCombination_single,one_smul]⟩

def integral : Domain →L[ℝ] JointL2 := finite.extendOfNorm reference

theorem integral_finite (a : ℝ≥0 →₀ ℝ) : integral (reference a) = finite a :=
  LinearMap.extendOfNorm_eq reference_dense ⟨bound,finite_bound⟩ a

theorem actual_finite (a : ℝ≥0 →₀ ℝ) :
    integral (reference a) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => ∑ t ∈ a.support, a t * IBMConstructedSources.ibmValue t p := by
  rw [integral_finite]
  change (∑ t ∈ a.support, a t • observed t) =ᵐ[IBMSourceLaws.jointMeasure] _
  have hc := (Finset.eventually_all a.support).mpr fun t _ =>
    (Lp.coeFn_smul (a t) (observed t)).and (observed_ae t)
  filter_upwards [Lp.coeFn_finsetSum a.support (fun t => a t • observed t),hc] with p hs hp
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro t ht
  rcases hp t ht with ⟨hsm,ha⟩
  simp only [hsm,Pi.smul_apply,smul_eq_mul,ha]

theorem integral_bound (f : Domain) : ‖integral f‖ ≤ bound * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le reference_dense bound finite_bound f

theorem integral_kernel (t : ℝ≥0) : integral (kernelVector t) = observed t := by
  have h := integral_finite (Finsupp.single t 1)
  simpa only [reference,finite,Finsupp.linearCombination_single,one_smul] using h

theorem integral_interval (s t : ℝ≥0) :
    integral (kernelVector t-kernelVector s) = observed t-observed s := by
  rw [map_sub,integral_kernel,integral_kernel]

theorem actual_interval (s t : ℝ≥0) :
    integral (kernelVector t-kernelVector s) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => IBMConstructedSources.ibmValue t p-IBMConstructedSources.ibmValue s p := by
  rw [integral_interval]
  filter_upwards [Lp.coeFn_sub (observed t) (observed s),observed_ae t,observed_ae s]
    with p hd ht hs
  simp only [hd,Pi.sub_apply,ht,hs]

theorem finite_limit (a : ℕ → (ℝ≥0 →₀ ℝ)) (f : Domain)
    (ha : Tendsto (fun n => reference (a n)) atTop (𝓝 f)) :
    Tendsto (fun n => finite (a n)) atTop (𝓝 (integral f)) := by
  simpa only [Function.comp_def,integral_finite] using
    integral.continuous.continuousAt.tendsto.comp ha

theorem exists_actual_approximation (f : Domain) :
    ∃ a : ℕ → (ℝ≥0 →₀ ℝ),
      Tendsto (fun n => reference (a n)) atTop (𝓝 f) ∧
      Tendsto (fun n => finite (a n)) atTop (𝓝 (integral f)) := by
  obtain ⟨u,hu,hlim⟩ := mem_closure_iff_seq_limit.mp (reference_dense f)
  choose a ha using hu
  have he : (fun n => reference (a n)) = u := funext ha
  have ht : Tendsto (fun n => reference (a n)) atTop (𝓝 f) := he.symm ▸ hlim
  exact ⟨a,ht,finite_limit a f ht⟩

theorem integral_observable (f : Domain) : integral f ∈ IntrinsicSpace := by
  have hm : ∀ x ∈ Set.range reference, integral x ∈ IntrinsicSpace := by
    rintro x ⟨a,rfl⟩
    rw [integral_finite]
    change (∑ t ∈ a.support, a t • observed t) ∈ IntrinsicSpace
    apply Submodule.sum_mem
    intro t ht
    exact IntrinsicSpace.smul_mem _ (intrinsicCurve t).property
  exact reference_dense.induction hm
    ((IBMConditionalObservable.observableSpace_isClosed _ _
      IBMConstructedSources.sceneryPath_measurable
      IBMConstructedSources.clockPath_measurable).preimage integral.continuous) f

theorem integral_unique (J : Domain →L[ℝ] JointL2)
    (hJ : ∀ t, J (kernelVector t) = observed t) : J = integral := by
  have hm : ∀ x ∈ Set.range reference, J x = integral x := by
    rintro x ⟨a,rfl⟩
    rw [integral_finite]
    change J (∑ t ∈ a.support, a t • kernelVector t) = ∑ t ∈ a.support, a t • observed t
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul,hJ]
  apply ContinuousLinearMap.ext
  intro f
  exact reference_dense.induction hm (isClosed_eq J.continuous integral.continuous) f

end OperatorDerivativeRewrite.Foundation.IBMRawDeterministicIntegral
