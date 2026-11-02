import Foundation.StochasticCauchyStoppedPolynomialIto

/-! Actual untruncated polynomial stochastic integrals as L2 limits. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyUntruncatedPolynomial
open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral StochasticCauchyPastReconstruction
open StochasticCauchyComplexChannels StochasticCauchyExponentialInput StochasticCauchyExitClock
open StochasticCauchyExitOccupation StochasticCauchyExitMoments StochasticCauchyStoppedPolynomialIto
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Actual terminal polynomial difference; stochastic-limit identification is proved below. -/
def exitIntegral (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) : JointComplex :=
  ((exit_polynomial_memLp p R hR).sub (memLp_const (p.eval 0))).toLp _

theorem exitIntegral_actual (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    exitIntegral p R hR =ᵐ[μ] fun w => p.eval (exitValue R w)-p.eval 0 := MemLp.coeFn_toLp _

/-- Strong convergence uses actual clock equality and disk bounds, not uniform
energy alone or an unconstructed common infinite-horizon input space. -/
theorem sampledPolynomial_tendsto (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => sampledPolynomial p R n) atTop (𝓝 (exitIntegral p R hR)) := by
  obtain ⟨M,hM,hbound⟩ := polynomial_disk_bound p R
  let C : ℝ := M+‖p.eval 0‖
  have hC : 0≤C := add_nonneg hM (norm_nonneg _)
  let b : JointL2 := C • jointOne
  have hb : b =ᵐ[μ] fun _ => C := by
    filter_upwards [Lp.coeFn_smul C jointOne,jointOne_ae] with w hs h1
    simp only [b,hs,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [sampledPolynomial_actual p R n,exit_bounded_ae R hR n,hb] with w hw hr hb
    rw [hw,hb,Real.norm_eq_abs,abs_of_nonneg hC]
    exact (norm_sub_le _ _).trans (add_le_add (hbound _ hr) le_rfl)
  · filter_upwards [exitIntegral_actual p R hR,exitValue_boundary R hR,hb] with w hw hr hb
    rw [hw,hb,Real.norm_eq_abs,abs_of_nonneg hC]
    exact (norm_sub_le _ _).trans (add_le_add (hbound _ hr.le) le_rfl)
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ => sampledPolynomial_actual p R n),
      exitIntegral_actual p R hR,exit_clock_eventually R hR] with w hn he hc
    simp only [hn,he]
    have heq : (fun n : ℕ => p.eval (StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)-p.eval 0)
        =ᶠ[atTop] fun _ => p.eval (exitValue R w)-p.eval 0 := hc.mono fun n h => by dsimp only;rw [h];rfl
    exact (tendsto_congr' heq).mpr tendsto_const_nhds

/-- These are the ORIGINAL finite-horizon native stochastic outputs. -/
theorem native_outputs_tendsto (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => channel n false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R n))
      atTop (𝓝 (exitIntegral p R hR)) := by
  simp only [sampledPolynomial_reconstruction]
  exact sampledPolynomial_tendsto p R hR

theorem native_output_limit_unique (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) (F : JointComplex)
    (hF : Tendsto (fun n : ℕ => channel n false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R n)) atTop (𝓝 F)) :
    F=exitIntegral p R hR := tendsto_nhds_unique hF (native_outputs_tendsto p R hR)

theorem physical_mean_square (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => ∫ w,‖p.eval (StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)-
      p.eval (exitValue R w)‖^2 ∂μ) atTop (𝓝 0) := by
  have hl := sampledPolynomial_tendsto p R hR
  have hn : Tendsto (fun n : ℕ => ‖sampledPolynomial p R n-exitIntegral p R hR‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hl.sub_const (exitIntegral p R hR)).norm.pow 2)
  have he (n : ℕ) : ‖sampledPolynomial p R n-exitIntegral p R hR‖^2=
      ∫ w,‖p.eval (StochasticCauchyBrownianRealization.value (clippedClock n (exitTime R) w) w)-
        p.eval (exitValue R w)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (sampledPolynomial p R n) (exitIntegral p R hR),
      sampledPolynomial_actual p R n,exitIntegral_actual p R hR] with w hs hn he
    change ‖(sampledPolynomial p R n-exitIntegral p R hR) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hn,he,sub_sub_sub_cancel_right]
  simpa only [he] using hn

theorem exitIntegral_mean_zero (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    (∫ w,exitIntegral p R hR w ∂μ)=0 := by
  rw [integral_congr_ae (exitIntegral_actual p R hR),
    integral_sub ((exit_polynomial_memLp p R hR).integrable (by norm_num)) (integrable_const _),
    exit_polynomial_mean p R hR]
  simp

/-- Finite native derivative energies converge as REAL numbers. This does NOT
claim convergence of their inputs in a common infinite-horizon domain. -/
theorem native_energy_tendsto (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    Tendsto (fun n : ℕ => ‖exitDerivativeInput p R n‖^2) atTop
      (𝓝 (‖exitIntegral p R hR‖^2/2)) := by
  have he (n : ℕ) : ‖exitDerivativeInput p R n‖^2=‖sampledPolynomial p R n‖^2/2 := by
    have h := sampledPolynomial_energy p R n
    linarith
  simp only [he]
  exact ((sampledPolynomial_tendsto p R hR).norm.pow 2).div_const 2

private theorem monomial_actual (R : ℝ) (hR : 0≤R) (m : ℕ) (hm : m≠0) :
    exitIntegral (Polynomial.X^m) R hR =ᵐ[μ] fun w => (exitValue R w)^m := by
  filter_upwards [exitIntegral_actual (Polynomial.X^m) R hR] with w hw
  simpa only [Polynomial.eval_pow,Polynomial.eval_X,zero_pow hm,sub_zero] using hw

/-- Actual untruncated stochastic monomial integrals realize the exact positive
circle-mode Gram kernel; no infinite-horizon input representation is presumed. -/
theorem monomial_gram (R : ℝ) (hR : 0≤R) (m n : ℕ) (hm : m≠0) (hn : n≠0) :
    inner ℂ (exitIntegral (Polynomial.X^m) R hR) (exitIntegral (Polynomial.X^n) R hR)=
      if m=n then (R:ℂ)^(m+n) else 0 := by
  rw [L2.inner_def]
  have he : (∫ w,inner ℂ (exitIntegral (Polynomial.X^m) R hR w) (exitIntegral (Polynomial.X^n) R hR w) ∂μ)=
      ∫ w,(exitValue R w)^n*(starRingEnd ℂ (exitValue R w))^m ∂μ := by
    apply integral_congr_ae
    filter_upwards [monomial_actual R hR m hm,monomial_actual R hR n hn] with w hw hv
    rw [hw,hv]
    simp only [RCLike.inner_apply,map_pow]
  rw [he,mixed_exit_moment R hR n m]
  by_cases hmn : m=n
  · subst n;simp
  · simp only [hmn,Ne.symm hmn,ite_false]

theorem monomial_norm_sq (R : ℝ) (hR : 0≤R) (m : ℕ) (hm : m≠0) :
    ‖exitIntegral (Polynomial.X^m) R hR‖^2=R^(2*m) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ _ : Sample,R^(2*m) ∂μ := by
      apply integral_congr_ae
      filter_upwards [monomial_actual R hR m hm,exitValue_boundary R hR] with w hw hz
      change ‖exitIntegral (Polynomial.X^m) R hR w‖^2=R^(2*m)
      rw [hw,norm_pow,hz,← pow_mul,Nat.mul_comm m 2]
    _ = _ := by simp

/-- Every finite actual derivative sum has its genuine sourceL2 class. -/
def chronologicalClass (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) (m : ℕ) : JointComplex :=
  (exit_derivative_sums_memLp p R T m).toLp _

theorem chronologicalClass_actual (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) (m : ℕ) :
    chronologicalClass p R T m =ᵐ[μ] derivativeSum (clippedClock T (exitTime R)) T p m := MemLp.coeFn_toLp _

theorem chronologicalClass_tendsto (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    Tendsto (chronologicalClass p R T) atTop (𝓝 (sampledPolynomial p R T)) := by
  have he (m : ℕ) : ‖chronologicalClass p R T m-sampledPolynomial p R T‖^2=
      ∫ w,‖derivativeSum (clippedClock T (exitTime R)) T p m w-
        (p.eval (StochasticCauchyBrownianRealization.value (clippedClock T (exitTime R) w) w)-p.eval 0)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (chronologicalClass p R T m) (sampledPolynomial p R T),
      chronologicalClass_actual p R T m,sampledPolynomial_actual p R T] with w hs hf hg
    change ‖(chronologicalClass p R T m-sampledPolynomial p R T) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hf,hg]
  have hn : Tendsto (fun m => ‖chronologicalClass p R T m-sampledPolynomial p R T‖^2) atTop (𝓝 0) := by
    simpa only [he] using exit_derivative_sums_mean_square p R T
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

/-- A real stochastic diagonal: growing horizons and sufficiently fine genuine
finite chronological sums converge strongly to the untruncated integral. -/
theorem chronological_diagonal_exists (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ k : ℕ → ℕ,(∀ n,n^2≤k n) ∧
      Tendsto (fun n : ℕ => chronologicalClass p R n (k n)) atTop (𝓝 (exitIntegral p R hR)) := by
  have ha (n : ℕ) : ∃ N : ℕ,∀ m≥N,dist (chronologicalClass p R n m) (sampledPolynomial p R n)<(1:ℝ)/((n:ℝ)+1) := by
    have hp : (0:ℝ)<1/((n:ℝ)+1) := by positivity
    have he := (chronologicalClass_tendsto p R (n:ℝ≥0)).eventually (Metric.ball_mem_nhds _ hp)
    obtain ⟨N,hN⟩ := eventually_atTop.1 he
    exact ⟨N,fun m hm => Metric.mem_ball.mp (hN m hm)⟩
  choose N hN using ha
  let k : ℕ → ℕ := fun n => max (N n) (n^2)
  refine ⟨k,fun n => le_max_right _ _,?_⟩
  have hb (n : ℕ) : dist (chronologicalClass p R n (k n)) (sampledPolynomial p R n)≤(1:ℝ)/((n:ℝ)+1) :=
    (hN n (k n) (le_max_left _ _)).le
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hd : Tendsto (fun n : ℕ => dist (sampledPolynomial p R n) (exitIntegral p R hR)) atTop (𝓝 0) := by
    simpa only [dist_self] using (sampledPolynomial_tendsto p R hR).dist (tendsto_const_nhds (x := exitIntegral p R hR))
  have ht : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)+dist (sampledPolynomial p R n) (exitIntegral p R hR)) atTop (𝓝 0) := by
    simpa only [zero_add] using hε.add hd
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg) _ ht
  intro n
  exact (dist_triangle _ (sampledPolynomial p R n) _).trans (add_le_add (hb n) le_rfl)

/-- The selected chronological grids have ACTUAL mesh tending to0 while the
horizons grow. No exchange of limits or universal fixed mesh-rate is assumed. -/
theorem diagonal_mesh_tendsto (k : ℕ → ℕ) (hk : ∀ n,n^2≤k n) :
    Tendsto (fun n : ℕ => (n:ℝ)/((k n:ℝ)+1)) atTop (𝓝 0) := by
  have hb (n : ℕ) : (n:ℝ)/((k n:ℝ)+1)≤(2:ℝ)/((n:ℝ)+1) := by
    have hh : (n:ℝ)^2≤(k n:ℝ) := by exact_mod_cast hk n
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(k n:ℝ)+1) (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    nlinarith [sq_nonneg ((n:ℝ)-(1/2:ℝ))]
  exact squeeze_zero (fun n => by positivity) hb
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))

/-- Actual derivative sums along a justified growing-horizon, vanishing-mesh
diagonal converge in PHYSICAL SOURCE MEAN SQUARE to p(exitValue)-p(0). -/
theorem untruncated_chronological_mean_square (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ k : ℕ → ℕ,(∀ n,n^2≤k n) ∧
      Tendsto (fun n : ℕ => ∫ w,‖derivativeSum (clippedClock n (exitTime R)) n p (k n) w-
        (p.eval (exitValue R w)-p.eval 0)‖^2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨k,hk,hl⟩ := chronological_diagonal_exists p R hR
  refine ⟨k,hk,?_⟩
  have hn : Tendsto (fun n : ℕ => ‖chronologicalClass p R n (k n)-exitIntegral p R hR‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using ((hl.sub_const (exitIntegral p R hR)).norm.pow 2)
  have he (n : ℕ) : ‖chronologicalClass p R n (k n)-exitIntegral p R hR‖^2=
      ∫ w,‖derivativeSum (clippedClock n (exitTime R)) n p (k n) w-
        (p.eval (exitValue R w)-p.eval 0)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (chronologicalClass p R n (k n)) (exitIntegral p R hR),
      chronologicalClass_actual p R n (k n),exitIntegral_actual p R hR] with w hs hf hg
    change ‖(chronologicalClass p R n (k n)-exitIntegral p R hR) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hf,hg]
  simpa only [he] using hn

/-- The constant Fourier mode is removed by stochastic centering. -/
theorem exitIntegral_const (c : ℂ) (R : ℝ) (hR : 0≤R) : exitIntegral (Polynomial.C c) R hR=0 := by
  apply Lp.ext
  filter_upwards [exitIntegral_actual (Polynomial.C c) R hR,Lp.coeFn_zero ℂ 2 μ] with w hw hz
  simp only [Pi.zero_apply] at hz
  rw [hw,hz]
  simp only [Polynomial.eval_C,sub_self]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyUntruncatedPolynomial
