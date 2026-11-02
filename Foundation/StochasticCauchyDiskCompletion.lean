import Foundation.StochasticCauchyUntruncatedPolynomial
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyDiskCompletion
open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels StochasticCauchyExponentialInput
open StochasticCauchyExitClock StochasticCauchyExitMoments StochasticCauchyExitOccupation
open StochasticCauchyStoppedPolynomialIto
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Bounded disk polynomial approximation constructs an ACTUAL native stochastic
integral and strong convergence of its original inputs. No global measurability
of f or flat Gaussian derivative premise is inserted. -/
theorem sampled_completion (f : ℂ → ℂ) (p : ℕ → Polynomial ℂ)
    (R : ℝ) (hR : 0≤R) (M : ℝ) (hM : 0≤M)
    (hb : ∀ n z,‖z‖≤R → ‖(p n).eval z‖≤M)
    (hl : ∀ z,‖z‖≤R → Tendsto (fun n => (p n).eval z) atTop (𝓝 (f z))) (T : ℝ≥0) :
    ∃ u : ComplexInput T,
      (channel T false u =ᵐ[μ] fun w =>
        f (StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)-f 0) ∧
      Tendsto (fun n => ((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput (p n) R T) atTop (𝓝 u) ∧
      channelAdjoint T true (channel T false u)=0 := by
  have hf (z : ℂ) (hz : ‖z‖≤R) : ‖f z‖≤M :=
    le_of_tendsto (hl z hz).norm (Eventually.of_forall fun n => hb n z hz)
  have h0 : ‖(0:ℂ)‖≤R := by simpa using hR
  let g : Sample → ℂ := fun w =>
    f (StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)-f 0
  have ht : ∀ᵐ w ∂μ,Tendsto (fun n => sampledPolynomial (p n) R T w) atTop (𝓝 (g w)) := by
    filter_upwards [ae_all_iff.mpr (fun n => sampledPolynomial_actual (p n) R T),exit_bounded_ae R hR T] with w hw hz
    simpa only [hw,g] using (hl _ hz).sub (hl 0 h0)
  have hg : MemLp g 2 μ := MemLp.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable (sampledPolynomial (p n) R T)) ht)
    (2*M) (by
      filter_upwards [exit_bounded_ae R hR T] with w hw
      exact (norm_sub_le _ _).trans (by linarith [hf _ hw,hf 0 h0]))
  let F : JointComplex := hg.toLp g
  have hF : F =ᵐ[μ] g := MemLp.coeFn_toLp _
  let b : JointL2 := (2*M) • jointOne
  have hb_actual : b =ᵐ[μ] fun _ => 2*M := by
    filter_upwards [Lp.coeFn_smul (2*M) jointOne,jointOne_ae] with w hs h1
    simp only [b,hs,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  have hs : Tendsto (fun n => sampledPolynomial (p n) R T) atTop (𝓝 F) := by
    apply BochnerL2Approximation.tendsto_of_dominated _ _ b
    · intro n
      filter_upwards [sampledPolynomial_actual (p n) R T,exit_bounded_ae R hR T,hb_actual] with w hw hz hbw
      rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
      exact (norm_sub_le _ _).trans (by linarith [hb n _ hz,hb n 0 h0])
    · filter_upwards [hF,exit_bounded_ae R hR T,hb_actual] with w hw hz hbw
      rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
      exact (norm_sub_le _ _).trans (by linarith [hf _ hz,hf 0 h0])
    · filter_upwards [ht,hF] with w hw he
      rwa [he]
  have hr : F ∈ (channel T false).toLinearMap.range :=
    (channel_closed_range T false).mem_of_tendsto hs (Eventually.of_forall fun n =>
      ⟨((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput (p n) R T,sampledPolynomial_reconstruction (p n) R T⟩)
  obtain ⟨u,hu⟩ := hr
  change channel T false u=F at hu
  refine ⟨u,?_,?_,?_⟩
  · exact hu ▸ hF
  · have hc := (channelAdjoint T false).continuous.tendsto F |>.comp hs
    simpa only [Function.comp_def,(sampledPolynomial_canonical _ _ _).1,← hu,channelAdjoint_self] using hc
  · exact channelAdjoint_cross T true u

/-- Geometric polynomials are genuinely local approximants to a resolvent. -/
def resolventPolynomial (a : ℂ) (n : ℕ) : Polynomial ℂ :=
  Polynomial.C a⁻¹ * ∑ j ∈ Finset.range n,(Polynomial.C a⁻¹ * Polynomial.X)^j

theorem resolventPolynomial_eval (a z : ℂ) (n : ℕ) :
    (resolventPolynomial a n).eval z=a⁻¹ * ∑ j ∈ Finset.range n,(a⁻¹*z)^j := by
  simp only [resolventPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finsetSum,
    Polynomial.eval_pow,Polynomial.eval_X]

/-- Uniformly bounded geometric approximants on the CLOSED disk, with a strict
exterior pole. The function is only required locally, not globally entire. -/
theorem resolvent_approximation (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    ∃ M : ℝ,0≤M ∧
      (∀ n z,‖z‖≤R → ‖(resolventPolynomial a n).eval z‖≤M) ∧
      (∀ z,‖z‖≤R → Tendsto (fun n => (resolventPolynomial a n).eval z) atTop (𝓝 ((a-z)⁻¹))) := by
  have hap : 0<‖a‖ := lt_of_le_of_lt hR ha
  have ha0 : a≠0 := norm_pos_iff.mp hap
  let q : ℝ := R/‖a‖
  have hq0 : 0≤q := div_nonneg hR (norm_nonneg _)
  have hq1 : q<1 := (div_lt_one hap).mpr ha
  have hzbound (z : ℂ) (hz : ‖z‖≤R) : ‖a⁻¹*z‖≤q := by
    rw [norm_mul,norm_inv]
    exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (norm_nonneg _))).trans_eq (by dsimp only [q];ring)
  refine ⟨‖a‖⁻¹*(1-q)⁻¹,mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (sub_nonneg.mpr hq1.le)),?_,?_⟩
  · intro n z hz
    rw [resolventPolynomial_eval,norm_mul,norm_inv]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
    calc
      ‖∑ j ∈ Finset.range n,(a⁻¹*z)^j‖ ≤ ∑ j ∈ Finset.range n,‖(a⁻¹*z)^j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n,q^j := Finset.sum_le_sum fun j _ => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hzbound z hz) j
      _ ≤ (1-q)⁻¹ := by
        have h := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum (Finset.range n) (fun j _ => pow_nonneg hq0 j)
        simpa only [tsum_geometric_of_lt_one hq0 hq1] using h
  · intro z hz
    have hzz : ‖a⁻¹*z‖<1 := lt_of_le_of_lt (hzbound z hz) hq1
    have ht := (hasSum_geometric_of_norm_lt_one hzz).tendsto_sum_nat.const_mul a⁻¹
    have haz : a-z≠0 := by
      intro he
      have heq : a=z := sub_eq_zero.mp he
      rw [heq] at ha
      exact (not_lt_of_ge hz) ha
    have he : a⁻¹*(1-a⁻¹*z)⁻¹=(a-z)⁻¹ := by
      field_simp
    simpa only [resolventPolynomial_eval,he] using ht

/-- A genuine disk-local nonpolynomial stochastic realization in the ORIGINAL
native domain; its normalized inputs are limits of actual stopped derivatives. -/
theorem resolvent_native (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    ∃ u : ComplexInput T,
      (channel T false u =ᵐ[μ] fun w =>
        (a-StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹) ∧
      Tendsto (fun n => ((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput (resolventPolynomial a n) R T) atTop (𝓝 u) ∧
      channelAdjoint T true (channel T false u)=0 := by
  obtain ⟨M,hM,hb,hl⟩ := resolvent_approximation a R hR ha
  simpa only [sub_zero] using sampled_completion (fun z => (a-z)⁻¹) (resolventPolynomial a) R hR M hM hb hl T

/-- At the boundary pole, these very approximants are unbounded on the closed
disk. This rejects extending the bounded-approximation argument to equality;
it is not a theorem that every alternative stochastic domain is impossible. -/
theorem boundary_pole_unbounded :
    ¬ ∃ M : ℝ,∀ n : ℕ,‖(resolventPolynomial 1 n).eval 1‖≤M := by
  rintro ⟨M,hM⟩
  obtain ⟨n,hn⟩ := exists_nat_gt M
  have h : (n:ℝ)≤M := by simpa [resolventPolynomial_eval] using hM n
  exact (not_le_of_gt hn) h

end OperatorDerivativeRewrite.Foundation.StochasticCauchyDiskCompletion
