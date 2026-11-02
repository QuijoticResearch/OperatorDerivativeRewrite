import Foundation.StochasticCauchyDiskDerivative
import Mathlib.Analysis.Complex.LocallyUniformLimit
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticDisk
open StochasticCauchyDiskCompletion StochasticCauchyDiskDerivative
open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyStoppedPolynomialIto StochasticCauchyExitClock
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Genuine polynomials for an arbitrary one-variable multilinear power series. -/
def seriesPolynomial (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range n,Polynomial.C (p j (fun _ => 1))*Polynomial.X^j

theorem seriesPolynomial_eval (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (z : ℂ) :
    (seriesPolynomial p n).eval z=p.partialSum n z := by
  simp only [seriesPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := (p j).map_smul_univ (fun _ => z) (fun _ => (1:ℂ))
  simpa only [smul_eq_mul,mul_one,Finset.prod_const,Finset.card_fin,mul_comm] using h.symm

/-- Derive bounded value approximation AND derivative convergence from a genuine
analytic power series, rather than assuming a polynomial approximation. -/
theorem series_approximation (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ℝ≥0∞)
    (hf : HasFPowerSeriesOnBall f p 0 r) (R : ℝ≥0) (hr : (R:ℝ≥0∞)<r) :
    ∃ M : ℝ,0≤M ∧
      (∀ n z,‖z‖≤R → ‖(seriesPolynomial p n).eval z‖≤M) ∧
      (∀ z,‖z‖≤R → Tendsto (fun n => (seriesPolynomial p n).eval z) atTop (𝓝 (f z))) ∧
      (∀ z,‖z‖≤R → Tendsto (fun n => (seriesPolynomial p n).derivative.eval z) atTop (𝓝 (deriv f z))) := by
  have hs := p.summable_norm_mul_pow (hr.trans_le hf.r_le)
  let M : ℝ := ∑' j,‖p j‖*(R:ℝ)^j
  have hm : 0≤M := tsum_nonneg (fun j => mul_nonneg (norm_nonneg _) (pow_nonneg R.coe_nonneg _))
  have hzmem (z : ℂ) (hz : ‖z‖≤R) : z∈Metric.eball (0:ℂ) r := by
    rw [mem_eball_zero_iff]
    exact lt_of_le_of_lt (by exact_mod_cast hz) hr
  have hv : TendstoLocallyUniformlyOn (fun n z => (seriesPolynomial p n).eval z) f atTop (Metric.eball (0:ℂ) r) := by
    simpa only [seriesPolynomial_eval,zero_add] using hf.tendstoLocallyUniformlyOn
  have hd := hv.deriv (Eventually.of_forall (fun n => (seriesPolynomial p n).differentiableOn)) Metric.isOpen_eball
  refine ⟨M,hm,?_,?_,?_⟩
  · intro n z hz
    rw [seriesPolynomial_eval,FormalMultilinearSeries.partialSum]
    calc
      _ ≤ ∑ j ∈ Finset.range n,‖p j (fun _ => z)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n,‖p j‖*(R:ℝ)^j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjz : ‖p j (fun _ => z)‖≤‖p j‖*‖z‖^j := by simpa using (p j).le_opNorm (fun _ => z)
        exact hjz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz j) (norm_nonneg _))
      _ ≤ M := hs.sum_le_tsum (Finset.range n) (fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg R.coe_nonneg _))
  · intro z hz
    exact hv.tendsto_at (hzmem z hz)
  · intro z hz
    simpa only [Function.comp_def,Polynomial.deriv] using hd.tendsto_at (hzmem z hz)

/-- Holomorphy on an OPEN neighborhood disk supplies every approximation
hypothesis needed by the original causal stochastic integration machinery. -/
theorem analytic_approximation (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    ∃ p : ℕ → Polynomial ℂ,∃ M : ℝ,0≤M ∧
      (∀ n z,‖z‖≤R → ‖(p n).eval z‖≤M) ∧
      (∀ z,‖z‖≤R → Tendsto (fun n => (p n).eval z) atTop (𝓝 (f z))) ∧
      (∀ z,‖z‖≤R → Tendsto (fun n => (p n).derivative.eval z) atTop (𝓝 (deriv f z))) := by
  obtain ⟨q,hRq,hqS⟩ := exists_between hRS
  have hq : 0<q := lt_of_le_of_lt (show (0:ℝ≥0)≤R from zero_le) hRq
  have hclosed : DifferentiableOn ℂ f (Metric.closedBall 0 q) := hf.mono (Metric.closedBall_subset_ball (by exact_mod_cast hqS))
  have hpower := hclosed.hasFPowerSeriesOnBall (by exact_mod_cast hq)
  obtain ⟨M,hM,hb,hl,hd⟩ := series_approximation f _ _ hpower R (by exact_mod_cast hRq)
  exact ⟨seriesPolynomial _,M,hM,hb,hl,hd⟩
/-- Actual stopped holomorphic Ito formula, with the SAME native input's
physical derivative field. A full flat Gaussian exit derivative is NOT assumed. -/
theorem analytic_ito (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    ∃ v : ComplexInput T,
      (channel T false (((Real.sqrt 2:ℝ):ℂ) • v) =ᵐ[μ] fun w =>
        f (StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)-f 0) ∧
      (∀ᵐ r ∂StochasticCauchyExponentialInput.timeLaw T,∀ᵐ w ∂μ,
        (StochasticCauchyPhysicalInput.fieldEmbedding T (realInput T v) ((r,w.1),w.2):ℂ)+
          Complex.I*(StochasticCauchyPhysicalInput.fieldEmbedding T (imagInput T v) ((r,w.1),w.2):ℂ)=
        {w : SampleSpace × SampleSpace | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
          (fun w => deriv f (StochasticCauchyBrownianRealization.value r.toNNReal w)) w) ∧
      channelAdjoint T true (channel T false (((Real.sqrt 2:ℝ):ℂ) • v))=0 := by
  obtain ⟨p,M,hM,hb,hl,hd⟩ := analytic_approximation f R S hRS hf
  obtain ⟨u,hu,hn,ha⟩ := sampled_completion f p R R.coe_nonneg M hM hb hl T
  let α : ℂ := ((Real.sqrt 2:ℝ):ℂ)
  have hα : α≠0 := by
    change ((Real.sqrt 2:ℝ):ℂ)≠0
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  change Tendsto (fun n => α • exitDerivativeInput (p n) R T) atTop (𝓝 u) at hn
  let v : ComplexInput T := α⁻¹ • u
  have he : α • v=u := by
    dsimp only [v]
    rw [smul_smul,mul_inv_cancel₀ hα,one_smul]
  have hv : Tendsto (fun n => exitDerivativeInput (p n) R T) atTop (𝓝 v) := by
    simpa only [smul_smul,inv_mul_cancel₀ hα,one_smul] using hn.const_smul α⁻¹
  refine ⟨v,?_,?_,?_⟩
  · exact he ▸ hu
  · exact derivative_input_limit p (deriv f) R R.coe_nonneg T v hv hd
  · exact he ▸ ha

/-- The actual input for this local holomorphic domain, at each finite horizon. -/
def nativeInput (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) : ComplexInput T :=
  Classical.choose (analytic_ito f R S hRS hf T)

theorem nativeInput_actual (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) (T : ℝ≥0) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • nativeInput f R S hRS hf T) =ᵐ[μ] fun w =>
      f (StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)-f 0 :=
  (Classical.choose_spec (analytic_ito f R S hRS hf T)).1

/-- Untruncated analytic exit values have a genuine L2 domain, derived from
actual polynomial exit approximants and the strict neighborhood hypothesis. -/
theorem exit_sample_memLp (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    MemLp (fun w => f (StochasticCauchyExitOccupation.exitValue R w)-f 0) 2 μ := by
  obtain ⟨p,M,hM,hb,hl,hd⟩ := analytic_approximation f R S hRS hf
  have h0 : ‖(0:ℂ)‖≤R := by simpa using R.coe_nonneg
  have hfbound (z : ℂ) (hz : ‖z‖≤R) : ‖f z‖≤M :=
    le_of_tendsto (hl z hz).norm (Eventually.of_forall fun n => hb n z hz)
  have ht : ∀ᵐ w ∂μ,Tendsto (fun n => StochasticCauchyUntruncatedPolynomial.exitIntegral (p n) R R.coe_nonneg w)
      atTop (𝓝 (f (StochasticCauchyExitOccupation.exitValue R w)-f 0)) := by
    filter_upwards [ae_all_iff.mpr (fun n => StochasticCauchyUntruncatedPolynomial.exitIntegral_actual (p n) R R.coe_nonneg),
      StochasticCauchyExitOccupation.exitValue_boundary R R.coe_nonneg] with w hw hz
    simpa only [hw] using (hl _ hz.le).sub (hl 0 h0)
  apply MemLp.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable (StochasticCauchyUntruncatedPolynomial.exitIntegral (p n) R R.coe_nonneg)) ht) (2*M)
  filter_upwards [StochasticCauchyExitOccupation.exitValue_boundary R R.coe_nonneg] with w hw
  exact (norm_sub_le _ _).trans (by linarith [hfbound _ hw.le,hfbound 0 h0])

/-- Actual untruncated analytic exit class on the ORIGINAL source L2. -/
def exitIntegral (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) : JointComplex :=
  (exit_sample_memLp f R S hRS hf).toLp _

theorem exitIntegral_actual (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    exitIntegral f R S hRS hf =ᵐ[μ] fun w => f (StochasticCauchyExitOccupation.exitValue R w)-f 0 :=
  MemLp.coeFn_toLp _

/-- Genuine strong convergence of original finite-horizon native OUTPUTS to
actual analytic exit. No common infinite-horizon INPUT is postulated. -/
theorem native_outputs_tendsto (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    Tendsto (fun n : ℕ => channel n false (((Real.sqrt 2:ℝ):ℂ) • nativeInput f R S hRS hf n)) atTop
      (𝓝 (exitIntegral f R S hRS hf)) := by
  obtain ⟨p,M,hM,hb,hl,hd⟩ := analytic_approximation f R S hRS hf
  have h0 : ‖(0:ℂ)‖≤R := by simpa using R.coe_nonneg
  have hfbound (z : ℂ) (hz : ‖z‖≤R) : ‖f z‖≤M :=
    le_of_tendsto (hl z hz).norm (Eventually.of_forall fun n => hb n z hz)
  let b : JointL2 := (2*M) • StochasticCauchyPastReconstruction.jointOne
  have hb_actual : b =ᵐ[μ] fun _ => 2*M := by
    filter_upwards [Lp.coeFn_smul (2*M) StochasticCauchyPastReconstruction.jointOne,
      StochasticCauchyPastReconstruction.jointOne_ae] with w hs h1
    simp only [b,hs,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [nativeInput_actual f R S hRS hf n,exit_bounded_ae R R.coe_nonneg n,hb_actual] with w hw hz hbw
    rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
    exact (norm_sub_le _ _).trans (by linarith [hfbound _ hz,hfbound 0 h0])
  · filter_upwards [exitIntegral_actual f R S hRS hf,
      StochasticCauchyExitOccupation.exitValue_boundary R R.coe_nonneg,hb_actual] with w hw hz hbw
    rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
    exact (norm_sub_le _ _).trans (by linarith [hfbound _ hz.le,hfbound 0 h0])
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => nativeInput_actual f R S hRS hf n),
      exitIntegral_actual f R S hRS hf,StochasticCauchyExitMoments.exit_clock_eventually R R.coe_nonneg] with w hn he hc
    simp only [hn,he]
    have heq : (fun n : ℕ =>
        f (StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)-f 0)
        =ᶠ[atTop] fun _ => f (StochasticCauchyExitOccupation.exitValue R w)-f 0 := hc.mono fun n h => by
          dsimp only
          rw [h]
          rfl
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

/-- Mean-value identity for this ACTUAL analytic exit, justified by L2
convergence, not by unbounded optional sampling. -/
theorem exitIntegral_mean_zero (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    (∫ w,exitIntegral f R S hRS hf w ∂μ)=0 := by
  have hl := (innerSL ℂ StochasticCauchyMeanResidual.complexOne).continuous.tendsto (exitIntegral f R S hRS hf)
    |>.comp (native_outputs_tendsto f R S hRS hf)
  change Tendsto (fun n : ℕ => inner ℂ StochasticCauchyMeanResidual.complexOne
      (channel n false (((Real.sqrt 2:ℝ):ℂ) • nativeInput f R S hRS hf n))) atTop
      (𝓝 (inner ℂ StochasticCauchyMeanResidual.complexOne (exitIntegral f R S hRS hf))) at hl
  simp only [StochasticCauchyMeanResidual.complexOne_inner,StochasticCauchyMeanResidual.channel_centered] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.StochasticCauchyAnalyticDisk
