import Foundation.IBMCommonClockDual

/-! Full source/clock rectangular summability in the genuine common dual
norm, uniformly for late mollifiers and independently large sector cutoffs. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCrossSectorDualClosure
open InfiniteGaussian GaussianClockValueOperators GaussianClockSourceSpectral IBMCommonClockDual
open IBMRegularizedStochasticIdentity IBMRegularizedTimeLimit GaussianSourceClockIto
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem uniform_joint_tail_of_tendsto {f : ℕ → Field} {c : Field}
    (hc : Tendsto f atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    ∃ M0 N0 n0 : ℕ, ∀ M ≥ M0, ∀ N ≥ N0, ∀ n ≥ n0,
      ‖f n - jointTruncation M N (f n)‖ < ε := by
  obtain ⟨n0,hn⟩ := Metric.tendsto_atTop.mp hc (ε/4) (by positivity)
  obtain ⟨M0,hM⟩ := Metric.tendsto_atTop.mp (sourceTruncation_tendsto c) (ε/4) (by positivity)
  obtain ⟨N0,hN⟩ := Metric.tendsto_atTop.mp (clock_truncation_tendsto c) (ε/4) (by positivity)
  refine ⟨M0,N0,n0,fun M hMM N hNN n hnn => ?_⟩
  have h1 : ‖f n-c‖ < ε/4 := by simpa only [dist_eq_norm] using hn n hnn
  have h2 : ‖c-sourceTruncation M c‖ < ε/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hM M hMM
  have h3 : ‖c-clockLift (GaussianNumberSectors.truncation N) c‖ < ε/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hN N hNN
  have hb := joint_tail_compare M N (f n) c
  linarith

/-- Explicit uniform joint-sector tails of the ORIGINAL full correction,
measured in the actual dense-test dual norm. Both cutoffs are independent. -/
theorem correction_uniform_rectangular_tail {g : SchwartzMap ℝ ℝ} {a : ℝ} {T : ℝ≥0} {c : Field}
    (hc : Tendsto (fun n => correction g a n T) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M0 N0 n0 : ℕ, ∀ M ≥ M0, ∀ N ≥ N0, ∀ n ≥ n0,
      dualNorm (IBMSchwartzBochnerDomain.wholeClass g a n T -
        ∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (N + 1),
          block m k (IBMSchwartzBochnerDomain.wholeClass g a n T)) < ε := by
  obtain ⟨M0,N0,n0,h⟩ := uniform_joint_tail_of_tendsto hc hε
  refine ⟨M0,N0,n0,fun M hMM N hNN n hnn => ?_⟩
  rw [← jointTruncation_eq_sum]
  change ‖smoothing (IBMSchwartzBochnerDomain.wholeClass g a n T -
    jointTruncation M N (IBMSchwartzBochnerDomain.wholeClass g a n T))‖ < ε
  rw [map_sub]
  have he : smoothing (jointTruncation M N (IBMSchwartzBochnerDomain.wholeClass g a n T)) =
      jointTruncation M N (smoothing (IBMSchwartzBochnerDomain.wholeClass g a n T)) :=
    commonSmoothing_joint M N _
  rw [he]
  exact h M hMM N hNN n hnn

theorem smoothed_clock_projection (k : ℕ) (f : Field) :
    clockLift (GaussianNumberSectors.projection k) (smoothing f) =
      GaussianRegularizedSecondDerivative.weight k • clockLift (GaussianNumberSectors.projection k) f := by
  apply eq_of_all_tests
  intro L
  change L.compLpL 2 gaussianProduct (clockLift (GaussianNumberSectors.projection k)
    (clockLift GaussianObservedSecondRegularization.commonSmoothing f)) = _
  rw [clockLift_test,clockLift_test,map_smul,clockLift_test]
  rw [← commonSmoothing_projection]
  exact GaussianObservedSecondRegularization.commonSmoothing_sector k
    ⟨_,GaussianNumberSectors.projection_mem k _⟩

/-- Every fixed clock sector of the ORIGINAL correction converges in native
joint L2, retaining ALL source sectors. This does not assert full raw L2 closure. -/
theorem raw_clock_projection_tendsto {g : SchwartzMap ℝ ℝ} {a : ℝ} {T : ℝ≥0} {c : Field}
    (hc : Tendsto (fun n => correction g a n T) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun n => clockLift (GaussianNumberSectors.projection k)
      (IBMSchwartzBochnerDomain.wholeClass g a n T)) atTop
        (𝓝 ((GaussianRegularizedSecondDerivative.weight k)⁻¹ •
          clockLift (GaussianNumberSectors.projection k) c)) := by
  have hh := (((clockLift (GaussianNumberSectors.projection k)).continuous.tendsto _).comp hc).const_smul
    (GaussianRegularizedSecondDerivative.weight k)⁻¹
  simpa only [Function.comp_def,correction,smoothed_clock_projection,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (GaussianRegularizedSecondDerivative.weight_pos k)),one_smul] using hh

theorem raw_block_tendsto {g : SchwartzMap ℝ ℝ} {a : ℝ} {T : ℝ≥0} {c : Field}
    (hc : Tendsto (fun n => correction g a n T) atTop (𝓝 c)) (m k : ℕ) :
    Tendsto (fun n => block m k (IBMSchwartzBochnerDomain.wholeClass g a n T)) atTop
      (𝓝 ((GaussianRegularizedSecondDerivative.weight k)⁻¹ • block m k c)) := by
  have hh := (sourceLift (GaussianNumberSectors.projection m)).continuous.tendsto _ |>.comp
    (raw_clock_projection_tendsto hc k)
  simpa only [Function.comp_def,block,ContinuousLinearMap.comp_apply,map_smul] using hh

/-- Genuine stochastic reconstruction, strong full-correction dual closure,
uniform rectangular source/clock summability and uniform bounded-test duality.
The mollifier index is the verified concrete normalized bump sequence. -/
theorem exists_cross_sector_dual_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ (u : Domain T) (c : Field),
      Tendsto (fun n => stochasticField g a n T) atTop (𝓝 u) ∧
      Tendsto (fun n => correction g a n T) atTop (𝓝 c) ∧
      smoothing (IBMSchwartzFullReflectedIto.endpointLimitClass g a T) =
        GaussianSourceClockIto.integral T u + c ∧
      (∀ ε > 0, ∃ M0 N0 n0 : ℕ, ∀ M ≥ M0, ∀ N ≥ N0, ∀ n ≥ n0,
        dualNorm (IBMSchwartzBochnerDomain.wholeClass g a n T -
          ∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (N + 1),
            block m k (IBMSchwartzBochnerDomain.wholeClass g a n T)) < ε) ∧
      (∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ ψ : Field, ‖ψ‖ ≤ 1 →
        |inner ℝ (IBMSchwartzBochnerDomain.wholeClass g a n T) (smoothing ψ) - inner ℝ c ψ| < ε) := by
  obtain ⟨u,c,hu,hc,hq,hi⟩ := exists_stochastic_reconstruction g a T
  exact ⟨u,c,hu,hc,hi,fun ε hε => correction_uniform_rectangular_tail hc hε,
    fun ε hε => correction_dual_uniform hc hε⟩

end OperatorDerivativeRewrite.Foundation.IBMCrossSectorDualClosure
