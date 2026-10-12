import Foundation.GaussianTaylorRemainder
import Foundation.GaussianLipschitzQuadraticVariation

/-! Scalar Brownian Ito for C3 functions with bounded first three derivatives,
proved from actual stochastic sums, Taylor's theorem and quadratic variation.
This is a restricted smooth theorem, not general C2 or functional Ito. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianContinuousIntegrands GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianBrownianQuadraticVariation GaussianTaylorRemainder

variable {φ : ℝ → ℝ} {K : ℝ≥0}

def driftSum (hφ : LipschitzWith K φ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i : Fin (N + 1), ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) •
    valueL2 hφ (uniformTime T N i.castSucc)

theorem driftSum_coeFn (hφ : LipschitzWith K φ) (T : ℝ≥0) (N : ℕ) :
    driftSum hφ T N =ᵐ[gaussianProduct] fun ω => ∑ i : Fin (N + 1),
      ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) *
        φ (process (uniformTime T N i.castSucc) ω) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N + 1) =>
    ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) •
      valueL2 hφ (uniformTime T N i.castSucc)),
    ae_all_iff.mpr (fun i : Fin (N + 1) => Lp.coeFn_smul
      ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc)
        (valueL2 hφ (uniformTime T N i.castSucc))),
    ae_all_iff.mpr (fun i : Fin (N + 1) => valueL2_coeFn hφ (uniformTime T N i.castSucc))]
      with ω hs hm hv
  change driftSum hφ T N ω = _ at hs
  rw [hs]
  simp only [Finset.sum_apply, hm, Pi.smul_apply, smul_eq_mul, hv]

theorem finite_taylor_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    {K0 K1 K2 : ℝ≥0} (h0 : LipschitzWith K0 f)
    (h1 : LipschitzWith K1 (deriv f)) (h2 : LipschitzWith K2 (deriv (deriv f)))
    (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) (N : ℕ) :
    valueL2 h0 T - valueL2 h0 0 =
      itoIntegral (predictableStep (valueL2 h1) (valueL2_past h1) T N) +
        (1 / 2 : ℝ) • (GaussianLipschitzQuadraticVariation.error h2 T N + driftSum h2 T N) +
        remainderSum f hf M hM T N := by
  let S := itoIntegral (predictableStep (valueL2 h1) (valueL2_past h1) T N)
  let Q := GaussianLipschitzQuadraticVariation.error h2 T N
  let V := driftSum h2 T N
  let R := remainderSum f hf M hM T N
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (valueL2 h0 T) (valueL2 h0 0), valueL2_coeFn h0 T,
    valueL2_coeFn h0 0, Lp.coeFn_add (S + (1 / 2 : ℝ) • (Q + V)) R,
    Lp.coeFn_add S ((1 / 2 : ℝ) • (Q + V)), Lp.coeFn_smul (1 / 2 : ℝ) (Q + V),
    Lp.coeFn_add Q V, stochastic_sum_coeFn h1 T N,
    GaussianLipschitzQuadraticVariation.error_coeFn h2 T N, driftSum_coeFn h2 T N,
    remainderSum_coeFn f hf M hM T N] with ω hsub ht hzero hadd hadd2 hsmul hqv hs hq hv hr
  change (valueL2 h0 T - valueL2 h0 0) ω = (S + (1 / 2 : ℝ) • (Q + V) + R) ω
  rw [hsub, hadd]
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [ht, hzero, hadd2]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hqv]
  simp only [Pi.add_apply]
  change S ω = _ at hs
  change Q ω = _ at hq
  change V ω = _ at hv
  change R ω = _ at hr
  rw [hs, hq, hv, hr]
  have htel := sum_fin_differences (fun i : Fin (N + 2) => f (process (uniformTime T N i) ω))
  rw [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2] at htel
  rw [← htel]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [remainder]
  ring

/-- The smooth Ito identity is obtained by taking the limit of the finite
Taylor identities, not by importing a stochastic chain rule. -/
theorem ito_of_lipschitz_derivatives (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    {K0 K1 K2 : ℝ≥0} (h0 : LipschitzWith K0 f)
    (h1 : LipschitzWith K1 (deriv f)) (h2 : LipschitzWith K2 (deriv (deriv f)))
    (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) :
    valueL2 h0 T - valueL2 h0 0 = itoIntegral (integrand h1 T) +
      (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), valueL2 h2 t.toNNReal) := by
  have ht := ((stochastic_sum_tendsto h1 T).add
    (((GaussianLipschitzQuadraticVariation.error_tendsto h2 T).add
      (GaussianLipschitzIntegrands.drift_sum_tendsto h2 T)).const_smul (1 / 2 : ℝ))).add
        (remainderSum_tendsto f hf M hM T)
  have he := ht.congr' (Eventually.of_forall fun N =>
    (finite_taylor_identity f hf h0 h1 h2 M hM T N).symm)
  simpa only [zero_add, add_zero] using (tendsto_nhds_unique tendsto_const_nhds he)

/-- Explicit smooth core: C3 and bounded ACTUAL first, second and third
spatial derivatives. The function itself need not be bounded. -/
theorem bounded_derivatives_ito (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (K0 K1 K2 : ℝ≥0) (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0)
    (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)
    (h2 : ∀ x, ‖deriv (deriv (deriv f)) x‖₊ ≤ K2) (T : ℝ≥0) :
    ∃ (l0 : LipschitzWith K0 f) (l1 : LipschitzWith K1 (deriv f))
      (l2 : LipschitzWith K2 (deriv (deriv f))),
      valueL2 l0 T - valueL2 l0 0 = itoIntegral (integrand l1 T) +
        (1 / 2 : ℝ) • (∫ t in 0..(T : ℝ), valueL2 l2 t.toNNReal) := by
  have d0 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have d1 : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have d2 : Differentiable ℝ (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hf.differentiable_iteratedDeriv 2 (by norm_num)
  let l0 := lipschitzWith_of_nnnorm_deriv_le d0 h0
  let l1 := lipschitzWith_of_nnnorm_deriv_le d1 h1
  let l2 := lipschitzWith_of_nnnorm_deriv_le d2 h2
  refine ⟨l0, l1, l2, ito_of_lipschitz_derivatives f hf l0 l1 l2 K2 ?_ T⟩
  intro x
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (show ‖deriv (deriv (deriv f)) x‖ ≤ (K2 : ℝ) from h2 x)

/-- The initial random variable is the correct deterministic initial value. -/
theorem valueL2_zero (hφ : LipschitzWith K φ) : valueL2 hφ 0 = φ 0 • gaussianOne := by
  apply Lp.ext
  filter_upwards [valueL2_coeFn hφ 0, process_zero_ae,
    Lp.coeFn_smul (φ 0) gaussianOne, gaussianOne_coeFn] with ω hv h0 hs h1
  rw [hv, h0, hs]
  simp only [Pi.smul_apply, smul_eq_mul, h1, mul_one]

theorem drift_integrable (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    IntervalIntegrable (fun t : ℝ => valueL2 hφ t.toNNReal) volume 0 T :=
  ((valueL2_continuous hφ).comp continuous_real_toNNReal).intervalIntegrable _ _

/-- Almost-everywhere random-variable form, with actual f(B_T), actual J,
and an integrable Gaussian-L2 Bochner drift identified by `valueL2_coeFn`. -/
theorem smooth_ito_ae (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    {K0 K1 K2 : ℝ≥0} (h0 : LipschitzWith K0 f)
    (h1 : LipschitzWith K1 (deriv f)) (h2 : LipschitzWith K2 (deriv (deriv f)))
    (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) :
    (fun ω => f (process T ω) - f 0) =ᵐ[gaussianProduct] fun ω =>
      itoIntegral (integrand h1 T) ω + (1 / 2 : ℝ) *
        ((∫ t in 0..(T : ℝ), valueL2 h2 t.toNNReal) : GaussianL2) ω := by
  have he := ito_of_lipschitz_derivatives f hf h0 h1 h2 M hM T
  let V : GaussianL2 := ∫ t in 0..(T : ℝ), valueL2 h2 t.toNNReal
  filter_upwards [Lp.coeFn_sub (valueL2 h0 T) (valueL2 h0 0), valueL2_coeFn h0 T,
    valueL2_coeFn h0 0, process_zero_ae,
    Lp.coeFn_add (itoIntegral (integrand h1 T)) ((1 / 2 : ℝ) • V),
    Lp.coeFn_smul (1 / 2 : ℝ) V] with ω hsub ht hz hzero hadd hs
  have heω := congrArg (fun A : GaussianL2 => A ω) he
  change (valueL2 h0 T - valueL2 h0 0) ω = (itoIntegral (integrand h1 T) + (1 / 2 : ℝ) • V) ω at heω
  rw [hsub, hadd] at heω
  simp only [Pi.sub_apply, Pi.add_apply] at heω
  rw [ht, hz, hzero, hs] at heω
  exact heω

end OperatorDerivativeRewrite.Foundation.GaussianSmoothIto

