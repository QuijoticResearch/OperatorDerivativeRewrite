import Foundation.StochasticCauchyExitOccupation
import Foundation.RightContinuousBoundedSampling

/-! Actual polynomial martingales, stopped expectations and exit moments. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExitMoments
open InfiniteGaussian StochasticCauchyStoppedDomains StochasticCauchyExitClock StochasticCauchyExitOccupation
open StochasticCauchyPastReconstruction StochasticCauchyPolynomialPrediction StochasticCauchyContinuousPolynomials
open StochasticCauchyBrownianRealization
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Exact complex CE invariance under the EXISTING ambient-null augmentation.
The proof uses the old REAL theorem and continuous-linear real/imaginary maps. -/
theorem augmented_complex_condExp (T : ℝ≥0) (F : Sample → ℂ) (hF : Integrable F μ) :
    μ[F | jointPast T] =ᵐ[μ] μ[F | augmentedJoint T] := by
  have hr := AmbientNullAugmentation.condExp_invariant (jointPast T) μ (jointPast_le T)
    (fun w => (F w).re) (Complex.reCLM.integrable_comp hF)
  have hi := AmbientNullAugmentation.condExp_invariant (jointPast T) μ (jointPast_le T)
    (fun w => (F w).im) (Complex.imCLM.integrable_comp hF)
  have hrr := ContinuousLinearMap.comp_condExp_comm (μ := μ) (m := jointPast T) hF Complex.reCLM
  have hra := ContinuousLinearMap.comp_condExp_comm (μ := μ) (m := augmentedJoint T) hF Complex.reCLM
  have hir := ContinuousLinearMap.comp_condExp_comm (μ := μ) (m := jointPast T) hF Complex.imCLM
  have hia := ContinuousLinearMap.comp_condExp_comm (μ := μ) (m := augmentedJoint T) hF Complex.imCLM
  filter_upwards [hr,hi,hrr,hra,hir,hia] with w hr hi hrr hra hir hia
  apply Complex.ext
  · exact hrr.trans (hr.trans hra.symm)
  · exact hir.trans (hi.trans hia.symm)

/-- Polynomial of the ACTUAL continuous two-source Brownian path. -/
def polynomialProcess (p : Polynomial ℂ) (t : ℝ≥0) (w : Sample) : ℂ := p.eval (value t w)

private theorem polynomialProcess_ae (p : Polynomial ℂ) (t : ℝ≥0) :
    polynomialProcess p t =ᵐ[μ] fun w => p.eval (position t w) :=
  (continuous_value_ae t).mono fun _ hw => congrArg p.eval hw

theorem polynomialProcess_integrable (p : Polynomial ℂ) (t : ℝ≥0) : Integrable (polynomialProcess p t) μ :=
  ((polynomial_position_memLp t p).integrable (by norm_num)).congr (polynomialProcess_ae p t).symm

theorem polynomialProcess_continuous (p : Polynomial ℂ) (w : Sample) :
    Continuous (fun t => polynomialProcess p t w) := by
  have hp : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  exact hp.comp (value_continuous w)

theorem polynomialProcess_stronglyAdapted (p : Polynomial ℂ) : StronglyAdapted augmentedJoint (polynomialProcess p) := by
  intro T
  have hp : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  exact hp.comp_stronglyMeasurable (continuous_stronglyAdapted T)

/-- The ACTUAL continuous polynomial process is a martingale on the SPECIFIED
augmented joint filtration; no filtration enlargement shortcut is used. -/
theorem polynomialProcess_martingale (p : Polynomial ℂ) : Martingale (polynomialProcess p) augmentedJoint μ := by
  refine ⟨polynomialProcess_stronglyAdapted p,?_⟩
  intro S T hST
  have ha := augmented_complex_condExp S (polynomialProcess p T) (polynomialProcess_integrable p T)
  have he := condExp_congr_ae (m := jointPast S) (polynomialProcess_ae p T)
  exact ha.symm.trans (he.trans ((conditional_polynomial S T hST p).trans (polynomialProcess_ae p S).symm))

theorem polynomialProcess_mean (p : Polynomial ℂ) (T : ℝ≥0) :
    (∫ w,polynomialProcess p T w ∂μ)=p.eval 0 := by
  have hce := (polynomialProcess_martingale p).2 (0:ℝ≥0) T bot_le
  have he := integral_congr_ae hce
  rw [integral_condExp (augmented_joint_le 0)] at he
  calc
    (∫ w,polynomialProcess p T w ∂μ) = ∫ w,polynomialProcess p 0 w ∂μ := he
    _ = ∫ _ : Sample,p.eval 0 ∂μ := by
      apply integral_congr_ae
      filter_upwards [value_zero_ae] with w hw
      exact congrArg p.eval hw
    _ = p.eval 0 := by simp

/-- Bounded optional sampling instantiated on the ACTUAL complex martingale,
for any possibly infinite original clock under a deterministic finite horizon. -/
theorem clipped_polynomial_mean (p : Polynomial ℂ) (τ : Sample → WithTop ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint τ) (T : ℝ≥0) :
    (∫ w,p.eval (value (clippedClock T τ w) w) ∂μ)=p.eval 0 := by
  have hN : ∀ w,clippedClock T τ w≤(⌈T⌉₊:ℝ≥0) :=
    fun w => (clippedClock_le T τ w).trans (Nat.le_ceil T)
  have hs := RightContinuousBoundedSampling.stopped_expectation μ augmentedJoint (polynomialProcess p)
    (polynomialProcess_martingale p) (fun w => (polynomialProcess_continuous p w).isRightContinuous)
    (clippedClock T τ) (clippedClock_stopping T τ hτ) ⌈T⌉₊ hN
  exact hs.trans (polynomialProcess_mean p _)

/-- Bounds are on the ACTUAL disk, not a false global polynomial bound. -/
theorem polynomial_disk_bound (p : Polynomial ℂ) (R : ℝ) :
    ∃ M : ℝ,0≤M ∧ ∀ z : ℂ,‖z‖≤R → ‖p.eval z‖≤M := by
  have hp : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hp.continuousOn
  exact ⟨max 0 M,le_max_left _ _,fun z hz =>
    (hM z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans (le_max_right _ _)⟩

/-- Eventually exact equality of the clipped and actual clocks, AE. -/
theorem exit_clock_eventually (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,
    ∀ᶠ n : ℕ in atTop,clippedClock n (exitTime R) w=finiteExit R w := by
  filter_upwards [finiteExit_actual R hR] with w hw
  have hn : ∀ᶠ n : ℕ in atTop,finiteExit R w≤(n:ℝ≥0) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  exact hn.mono fun n hn => by
    apply WithTop.coe_injective
    rw [clippedClock_coe,← hw,min_eq_left (WithTop.coe_le_coe.mpr hn)]

theorem exit_polynomial_memLp (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    MemLp (fun w => p.eval (exitValue R w)) 2 μ := by
  obtain ⟨M,hM,hbound⟩ := polynomial_disk_bound p R
  have hp : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  apply MemLp.of_bound (hp.measurable.comp (exitValue_measurable R)).aestronglyMeasurable M
  filter_upwards [exitValue_boundary R hR] with w hw
  exact hbound _ hw.le

/-- Actual untruncated stopped polynomial expectation. No uniform exit law,
full Gaussian derivative, or infinite-horizon input representation is assumed. -/
theorem exit_polynomial_mean (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    (∫ w,p.eval (exitValue R w) ∂μ)=p.eval 0 := by
  obtain ⟨M,hM,hbound⟩ := polynomial_disk_bound p R
  have hp : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  have hlim : ∀ᵐ w ∂μ,Tendsto
      (fun n : ℕ => p.eval (value (clippedClock n (exitTime R) w) w)) atTop (𝓝 (p.eval (exitValue R w))) := by
    filter_upwards [exit_clock_eventually R hR] with w hw
    exact (tendsto_congr' (hw.mono fun n hn => by rw [hn];rfl)).mpr tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Sample => M)
    (fun n : ℕ => hp.comp_aestronglyMeasurable (exit_memLp R n).aestronglyMeasurable)
    (integrable_const M) (fun n : ℕ => ?_) hlim
  · have he (n : ℕ) : (∫ w,p.eval (value (clippedClock n (exitTime R) w) w) ∂μ)=p.eval 0 :=
      clipped_polynomial_mean p (exitTime R) (exitTime_stopping R) n
    simp only [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · filter_upwards [exit_bounded_ae R hR n] with w hw
    exact hbound _ hw

/-- All analytic moments, including the correctly normalized zeroth mode. -/
theorem exit_moment (R : ℝ) (hR : 0≤R) (n : ℕ) :
    (∫ w,(exitValue R w)^n ∂μ)=(0:ℂ)^n := by
  simpa only [Polynomial.eval_pow,Polynomial.eval_X] using exit_polynomial_mean (Polynomial.X^n) R hR

theorem conjugate_exit_moment (R : ℝ) (hR : 0≤R) (n : ℕ) :
    (∫ w,(starRingEnd ℂ (exitValue R w))^n ∂μ)=(0:ℂ)^n := by
  simp_rw [← map_pow]
  rw [integral_conj,exit_moment R hR n]
  simp

theorem mixed_exit_memLp (R : ℝ) (hR : 0≤R) (m n : ℕ) :
    MemLp (fun w => (exitValue R w)^m*(starRingEnd ℂ (exitValue R w))^n) 2 μ := by
  have hm : Measurable (fun w => (exitValue R w)^m*(starRingEnd ℂ (exitValue R w))^n) :=
    ((exitValue_measurable R).pow_const m).mul ((Complex.continuous_conj.measurable.comp (exitValue_measurable R)).pow_const n)
  apply MemLp.of_bound hm.aestronglyMeasurable (R^(m+n))
  filter_upwards [exitValue_boundary R hR] with w hw
  simp only [norm_mul,norm_pow,Complex.norm_conj,hw,pow_add]
  exact le_rfl

private theorem exit_norm_product (R : ℝ) (hR : 0≤R) : ∀ᵐ w ∂μ,
    exitValue R w*starRingEnd ℂ (exitValue R w)=(R:ℂ)^2 := by
  filter_upwards [exitValue_boundary R hR] with w hw
  rw [Complex.mul_conj,← Complex.sq_norm,hw,Complex.ofReal_pow]

private theorem mixed_step (R : ℝ) (hR : 0≤R) (m n : ℕ) :
    (∫ w,(exitValue R w)^(m+1)*(starRingEnd ℂ (exitValue R w))^(n+1) ∂μ)=
      (R:ℂ)^2*(∫ w,(exitValue R w)^m*(starRingEnd ℂ (exitValue R w))^n ∂μ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [exit_norm_product R hR] with w hw
  calc
    (exitValue R w)^(m+1)*(starRingEnd ℂ (exitValue R w))^(n+1) =
      (exitValue R w*starRingEnd ℂ (exitValue R w))*
        ((exitValue R w)^m*(starRingEnd ℂ (exitValue R w))^n) := by ring
    _ = _ := by rw [hw]

/-- Exact mixed Gram kernel for the ACTUAL exit observable; no density or
uniform-circle distribution premise occurs. -/
theorem mixed_exit_moment (R : ℝ) (hR : 0≤R) (m n : ℕ) :
    (∫ w,(exitValue R w)^m*(starRingEnd ℂ (exitValue R w))^n ∂μ)=
      if m=n then (R:ℂ)^(m+n) else 0 := by
  induction n generalizing m with
  | zero =>
    simp only [pow_zero,mul_one]
    rw [exit_moment R hR m]
    by_cases hm : m=0
    · simp [hm]
    · simp [hm,zero_pow hm]
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero,one_mul]
      rw [conjugate_exit_moment R hR (n+1)]
      simp
    | succ m =>
      rw [mixed_step R hR m n,ih]
      by_cases hmn : m=n
      · subst m
        simp only [ite_true]
        rw [← pow_add]
        congr 1
        omega
      · simp [hmn]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExitMoments
