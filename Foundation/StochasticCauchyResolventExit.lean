import Foundation.StochasticCauchyResolventChronological
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyResolventExit
open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyDiskCompletion StochasticCauchyExitOccupation StochasticCauchyExitClock
open StochasticCauchyDiskDerivative StochasticCauchyResolventChronological StochasticCauchyComplexChannels
open StochasticCauchyExponentialInput StochasticCauchyPastReconstruction StochasticCauchyExitMoments
private abbrev α : ℂ := ((Real.sqrt 2:ℝ):ℂ)
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Actual untruncated resolvent exit observable, with its L2 domain DERIVED
from the existing local geometric bound and actual circle boundary. -/
theorem exit_resolvent_memLp (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    MemLp (fun w => (a-exitValue R w)⁻¹-a⁻¹) 2 μ := by
  obtain ⟨M,hM,hb,hl⟩ := resolvent_approximation a R hR ha
  have hf (z : ℂ) (hz : ‖z‖≤R) : ‖(a-z)⁻¹‖≤M :=
    le_of_tendsto (hl z hz).norm (Eventually.of_forall fun n => hb n z hz)
  have h0 : ‖a⁻¹‖≤M := by simpa only [sub_zero] using hf 0 (by simpa using hR)
  have hm : Measurable (fun w => (a-exitValue R w)⁻¹-a⁻¹) :=
    ((measurable_const.sub (exitValue_measurable R)).inv).sub measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable (2*M)
  filter_upwards [exitValue_boundary R hR] with w hw
  exact (norm_sub_le _ _).trans (by linarith [hf _ hw.le])

/-- Genuine original finite-horizon derivative input; no infinite-horizon input
space is presumed when forming limits of its OUTPUTS below. -/
def nativeInput (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) : ComplexInput T :=
  Classical.choose (resolvent_ito a R hR ha T)

theorem nativeInput_actual (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    channel T false (α • nativeInput a R hR ha T) =ᵐ[μ] fun w =>
      (a-StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹ :=
  (Classical.choose_spec (resolvent_ito a R hR ha T)).1

theorem nativeInput_physical (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (StochasticCauchyPhysicalInput.fieldEmbedding T (realInput T (nativeInput a R hR ha T)) ((r,w.1),w.2):ℂ)+
        Complex.I*(StochasticCauchyPhysicalInput.fieldEmbedding T (imagInput T (nativeInput a R hR ha T)) ((r,w.1),w.2):ℂ)=
      {w : SampleSpace × SampleSpace | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => (a-StochasticCauchyBrownianRealization.value r.toNNReal w)⁻¹^2) w :=
  (Classical.choose_spec (resolvent_ito a R hR ha T)).2.1

/-- Actual exit observable, whose stochastic-limit identification is below. -/
def exitIntegral (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) : JointComplex :=
  (exit_resolvent_memLp a R hR ha).toLp _

theorem exitIntegral_actual (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    exitIntegral a R hR ha =ᵐ[μ] fun w => (a-exitValue R w)⁻¹-a⁻¹ := MemLp.coeFn_toLp _

/-- ORIGINAL native outputs converge strongly to the ACTUAL untruncated exit
integral, by actual eventual clock equality and disk bounds, not energy alone. -/
theorem native_outputs_tendsto (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    Tendsto (fun n : ℕ => channel n false (α • nativeInput a R hR ha n)) atTop
      (𝓝 (exitIntegral a R hR ha)) := by
  obtain ⟨M,hM,hbound,hlim⟩ := resolvent_approximation a R hR ha
  have hf (z : ℂ) (hz : ‖z‖≤R) : ‖(a-z)⁻¹‖≤M :=
    le_of_tendsto (hlim z hz).norm (Eventually.of_forall fun n => hbound n z hz)
  have h0 : ‖a⁻¹‖≤M := by simpa only [sub_zero] using hf 0 (by simpa using hR)
  let b : JointL2 := (2*M) • jointOne
  have hb : b =ᵐ[μ] fun _ => 2*M := by
    filter_upwards [Lp.coeFn_smul (2*M) jointOne,jointOne_ae] with w hs h1
    simp only [b,hs,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [nativeInput_actual a R hR ha n,exit_bounded_ae R hR n,hb] with w hw hz hbw
    rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
    exact (norm_sub_le _ _).trans (by linarith [hf _ hz])
  · filter_upwards [exitIntegral_actual a R hR ha,exitValue_boundary R hR,hb] with w hw hz hbw
    rw [hw,hbw,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hM)]
    exact (norm_sub_le _ _).trans (by linarith [hf _ hz.le])
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => nativeInput_actual a R hR ha n),
      exitIntegral_actual a R hR ha,exit_clock_eventually R hR] with w hn he hc
    simp only [hn,he]
    have heq : (fun n : ℕ =>
        (a-StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)⁻¹-a⁻¹)
        =ᶠ[atTop] fun _ => (a-exitValue R w)⁻¹-a⁻¹ := hc.mono fun n h => by dsimp only;rw [h];rfl
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

theorem native_output_limit_unique (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (F : JointComplex)
    (hF : Tendsto (fun n : ℕ => channel n false (α • nativeInput a R hR ha n)) atTop (𝓝 F)) :
    F=exitIntegral a R hR ha := tendsto_nhds_unique hF (native_outputs_tendsto a R hR ha)

theorem exitIntegral_mean_zero (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    (∫ w,exitIntegral a R hR ha w ∂μ)=0 := by
  have hl := (innerSL ℂ StochasticCauchyMeanResidual.complexOne).continuous.tendsto (exitIntegral a R hR ha)
    |>.comp (native_outputs_tendsto a R hR ha)
  change Tendsto (fun n : ℕ => inner ℂ StochasticCauchyMeanResidual.complexOne
      (channel n false (α • nativeInput a R hR ha n))) atTop
      (𝓝 (inner ℂ StochasticCauchyMeanResidual.complexOne (exitIntegral a R hR ha))) at hl
  simp only [StochasticCauchyMeanResidual.complexOne_inner,StochasticCauchyMeanResidual.channel_centered] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

/-- Energies converge as REAL numbers; the inputs still have different horizons. -/
theorem native_energy_tendsto (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    Tendsto (fun n : ℕ => ‖nativeInput a R hR ha n‖^2) atTop
      (𝓝 (‖exitIntegral a R hR ha‖^2/2)) := by
  have hα : ‖α‖^2=2 := by
    simp only [α,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2),Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have he (n : ℕ) : ‖nativeInput a R hR ha n‖^2=‖channel n false (α • nativeInput a R hR ha n)‖^2/2 := by
    rw [(channel n false).norm_map,norm_smul,mul_pow,hα]
    ring
  simp only [he]
  exact ((native_outputs_tendsto a R hR ha).norm.pow 2).div_const 2

/-- Actual finite chronological sums, in the same original sourceL2 space. -/
def chronologicalClass (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) (m : ℕ) : JointComplex :=
  ((chronological_resolvent a R hR ha T).1 m).toLp _

theorem chronologicalClass_actual (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) (m : ℕ) :
    chronologicalClass a R hR ha T m =ᵐ[μ] resolventSum a R T m := MemLp.coeFn_toLp _

theorem chronologicalClass_tendsto (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    Tendsto (chronologicalClass a R hR ha T) atTop (𝓝 (channel T false (α • nativeInput a R hR ha T))) := by
  have he (m : ℕ) : ‖chronologicalClass a R hR ha T m-channel T false (α • nativeInput a R hR ha T)‖^2=
      ∫ w,‖resolventSum a R T m w-((a-StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (chronologicalClass a R hR ha T m) (channel T false (α • nativeInput a R hR ha T)),
      chronologicalClass_actual a R hR ha T m,nativeInput_actual a R hR ha T] with w hs hf hg
    change ‖(chronologicalClass a R hR ha T m-channel T false (α • nativeInput a R hR ha T)) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hf,hg]
  have hn : Tendsto (fun m => ‖chronologicalClass a R hR ha T m-channel T false (α • nativeInput a R hR ha T)‖^2) atTop (𝓝 0) := by
    simpa only [he] using (chronological_resolvent a R hR ha T).2
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

/-- Growing horizons and sufficiently fine actual chronological grids converge
strongly to the actual untruncated resolvent integral. -/
theorem chronological_diagonal_exists (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    ∃ k : ℕ → ℕ,(∀ n,n^2≤k n) ∧
      Tendsto (fun n : ℕ => chronologicalClass a R hR ha n (k n)) atTop (𝓝 (exitIntegral a R hR ha)) := by
  have hrow (n : ℕ) : ∃ N : ℕ,∀ m≥N,
      dist (chronologicalClass a R hR ha n m) (channel n false (α • nativeInput a R hR ha n))<1/((n:ℝ)+1) := by
    have hp : (0:ℝ)<1/((n:ℝ)+1) := by positivity
    have he := (chronologicalClass_tendsto a R hR ha (n:ℝ≥0)).eventually (Metric.ball_mem_nhds _ hp)
    obtain ⟨N,hN⟩ := eventually_atTop.1 he
    exact ⟨N,fun m hm => Metric.mem_ball.mp (hN m hm)⟩
  choose N hN using hrow
  let k : ℕ → ℕ := fun n => max (N n) (n^2)
  refine ⟨k,fun n => le_max_right _ _,?_⟩
  have hb (n : ℕ) : dist (chronologicalClass a R hR ha n (k n))
      (channel n false (α • nativeInput a R hR ha n))≤1/((n:ℝ)+1) := (hN n (k n) (le_max_left _ _)).le
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hd : Tendsto (fun n : ℕ => dist (channel n false (α • nativeInput a R hR ha n)) (exitIntegral a R hR ha)) atTop (𝓝 0) := by
    simpa only [dist_self] using (native_outputs_tendsto a R hR ha).dist (tendsto_const_nhds (x := exitIntegral a R hR ha))
  have ht : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)+dist (channel n false (α • nativeInput a R hR ha n))
      (exitIntegral a R hR ha)) atTop (𝓝 0) := by simpa only [zero_add] using hε.add hd
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) _ ht
  intro n
  exact (dist_triangle _ (channel n false (α • nativeInput a R hR ha n)) _).trans (add_le_add (hb n) le_rfl)

/-- Actual untruncated stochastic identity: horizons grow, the ACTUAL mesh tends
to0, and the rational-derivative sums converge in physical source mean square. -/
theorem untruncated_chronological_mean_square (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) :
    ∃ k : ℕ → ℕ,(∀ n,n^2≤k n) ∧
      Tendsto (fun n : ℕ => (n:ℝ)/((k n:ℝ)+1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ w,‖resolventSum a R n (k n) w-
        ((a-exitValue R w)⁻¹-a⁻¹)‖^2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨k,hk,hl⟩ := chronological_diagonal_exists a R hR ha
  refine ⟨k,hk,StochasticCauchyUntruncatedPolynomial.diagonal_mesh_tendsto k hk,?_⟩
  have hn : Tendsto (fun n : ℕ => ‖chronologicalClass a R hR ha n (k n)-exitIntegral a R hR ha‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using ((hl.sub_const (exitIntegral a R hR ha)).norm.pow 2)
  have he (n : ℕ) : ‖chronologicalClass a R hR ha n (k n)-exitIntegral a R hR ha‖^2=
      ∫ w,‖resolventSum a R n (k n) w-((a-exitValue R w)⁻¹-a⁻¹)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (chronologicalClass a R hR ha n (k n)) (exitIntegral a R hR ha),
      chronologicalClass_actual a R hR ha n (k n),exitIntegral_actual a R hR ha] with w hs hf hg
    change ‖(chronologicalClass a R hR ha n (k n)-exitIntegral a R hR ha) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hf,hg]
  simpa only [he] using hn

end OperatorDerivativeRewrite.Foundation.StochasticCauchyResolventExit
