import Foundation.FiniteTaylorRemainder
import Foundation.GaussianStoppedQuadraticVariation

/-! Genuine Gaussian L2 control of multivariate Taylor remainders on cells
aligned with all stopped-coordinate horizons. No independence of the remainders
is used; a norm-sum estimate supplies mesh convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianStoppedTaylor
open InfiniteGaussian GaussianTimeProcess GaussianStoppedComposition
open GaussianStoppedQuadraticVariation GaussianTaylorRemainder GaussianBrownianQuadraticVariation
open FiniteCovarianceHessian
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def activeVector (r : ι → ℝ≥0) (t : ℝ≥0) : ι → ℝ := fun i => active t (r i)

theorem activeVector_norm_le (r : ι → ℝ≥0) (t : ℝ≥0) : ‖activeVector r t‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  by_cases hi : t ≤ r i <;> simp [activeVector, active, hi]

theorem vector_increment (r : ι → ℝ≥0) (s t : ℝ≥0) (hst : s ≤ t)
    (hr : ∀ i, r i ≤ s ∨ t ≤ r i) (ω : SampleSpace) :
    coordinates r t ω - coordinates r s ω = (process t ω-process s ω) • activeVector r t := by
  funext i
  change process (min t (r i)) ω - process (min s (r i)) ω =
    (process t ω-process s ω)*active t (r i)
  rw [stopped_increment s t (r i) hst (hr i), mul_comm]

theorem vector_increment_norm_le (r : ι → ℝ≥0) (s t : ℝ≥0) (hst : s ≤ t)
    (hr : ∀ i, r i ≤ s ∨ t ≤ r i) (ω : SampleSpace) :
    ‖coordinates r t ω-coordinates r s ω‖ ≤ |process t ω-process s ω| := by
  rw [vector_increment r s t hst hr, norm_smul]
  simpa only [Real.norm_eq_abs, mul_one] using
    mul_le_mul_of_nonneg_left (activeVector_norm_le r t) (norm_nonneg (process t ω-process s ω))

variable (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ) (M : ℝ≥0)
  (hM : ∀ z v w u, ‖FiniteTaylorRemainder.thirdDerivative Φ z v w u‖ ≤ (M:ℝ)*‖v‖*‖w‖*‖u‖)
  (r : ι → ℝ≥0) (s t : ℝ≥0) (hst : s ≤ t) (hr : ∀ i, r i ≤ s ∨ t ≤ r i)

def rawRemainder (ω : SampleSpace) : ℝ :=
  FiniteTaylorRemainder.remainder Φ (coordinates r s ω) (coordinates r t ω-coordinates r s ω)

include hΦ in
theorem rawRemainder_measurable : Measurable (rawRemainder Φ r s t) :=
  (FiniteTaylorRemainder.remainder_continuous Φ hΦ).measurable.comp
    ((coordinates_stronglyMeasurable r s).measurable.prodMk
      ((coordinates_stronglyMeasurable r t).measurable.sub (coordinates_stronglyMeasurable r s).measurable))

include hΦ hM hst hr in
theorem rawRemainder_bound (ω : SampleSpace) :
    ‖rawRemainder Φ r s t ω‖ ≤ ((M:ℝ)/6)*|process t ω-process s ω|^3 := by
  exact (FiniteTaylorRemainder.remainder_bound Φ hΦ M hM _ _).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (vector_increment_norm_le r s t hst hr ω) 3) (by positivity))

include hΦ M hM hst hr in
theorem rawRemainder_memLp : MemLp (rawRemainder Φ r s t) 2 gaussianProduct := by
  apply (Lp.memLp (incrementCube s t)).of_le_mul (rawRemainder_measurable Φ hΦ r s t).aestronglyMeasurable
    (c := (M:ℝ)/6)
  filter_upwards [incrementCube_coeFn s t hst] with ω hc
  simpa only [hc, norm_pow, Real.norm_eq_abs] using rawRemainder_bound Φ hΦ M hM r s t hst hr ω

def remainderL2 : GaussianL2 := (rawRemainder_memLp Φ hΦ M hM r s t hst hr).toLp _

theorem remainderL2_coeFn : remainderL2 Φ hΦ M hM r s t hst hr =ᵐ[gaussianProduct]
    rawRemainder Φ r s t := MemLp.coeFn_toLp _

theorem remainderL2_norm_sq :
    ‖remainderL2 Φ hΦ M hM r s t hst hr‖^2 ≤ ((M:ℝ)/6)^2*15*((t:ℝ)-s)^3 := by
  have hb : ‖remainderL2 Φ hΦ M hM r s t hst hr‖ ≤ ((M:ℝ)/6)*‖incrementCube s t‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [remainderL2_coeFn Φ hΦ M hM r s t hst hr, incrementCube_coeFn s t hst] with ω he hc
    simpa only [he, hc, norm_pow, Real.norm_eq_abs] using rawRemainder_bound Φ hΦ M hM r s t hst hr ω
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow, incrementCube_norm_sq s t hst, mul_assoc] using hs

theorem remainderL2_mesh_bound (ε : ℝ) (hε : 0 ≤ ε) (ht : (t:ℝ)-s ≤ ε) :
    ‖remainderL2 Φ hΦ M hM r s t hst hr‖ ≤ ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt ε*((t:ℝ)-s) := by
  have hd : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr hst
  have he : (((M:ℝ)/6)*Real.sqrt 15*Real.sqrt ε*((t:ℝ)-s))^2 =
      ((M:ℝ)/6)^2*15*ε*((t:ℝ)-s)^2 := by
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15), Real.sq_sqrt hε]
  have hb := remainderL2_norm_sq Φ hΦ M hM r s t hst hr
  have hstep := mul_le_mul_of_nonneg_left ht
    (mul_nonneg (mul_nonneg (sq_nonneg ((M:ℝ)/6)) (by norm_num : (0:ℝ) ≤ 15)) (sq_nonneg ((t:ℝ)-s)))
  have hnonneg : 0 ≤ ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt ε*((t:ℝ)-s) := by positivity
  nlinarith [norm_nonneg (remainderL2 Φ hΦ M hM r s t hst hr)]

omit s t hst hr in
def remainderSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (halign : ∀ (k : Fin n) i, r i ≤ τ k.castSucc ∨ τ k.succ ≤ r i) : GaussianL2 :=
  ∑ k : Fin n, remainderL2 Φ hΦ M hM r _ _ (hτ (Fin.castSucc_le_succ k)) (halign k)

omit s t hst hr in
theorem remainderSum_coeFn {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (halign : ∀ (k : Fin n) i, r i ≤ τ k.castSucc ∨ τ k.succ ≤ r i) :
    remainderSum Φ hΦ M hM r τ hτ halign =ᵐ[gaussianProduct]
      fun ω => ∑ k : Fin n, rawRemainder Φ r (τ k.castSucc) (τ k.succ) ω := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k : Fin n =>
    remainderL2 Φ hΦ M hM r _ _ (hτ (Fin.castSucc_le_succ k)) (halign k)),
    ae_all_iff.mpr (fun k : Fin n =>
      remainderL2_coeFn Φ hΦ M hM r _ _ (hτ (Fin.castSucc_le_succ k)) (halign k))] with ω hs hc
  change (∑ k : Fin n, remainderL2 Φ hΦ M hM r _ _
    (hτ (Fin.castSucc_le_succ k)) (halign k)) ω = _
  rw [hs]
  simp only [Finset.sum_apply, hc]

omit s t hst hr in
theorem remainderSum_mesh_bound {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ)
    (halign : ∀ (k : Fin n) i, r i ≤ τ k.castSucc ∨ τ k.succ ≤ r i)
    (ε : ℝ) (hε : 0 ≤ ε) (hmesh : ∀ k : Fin n, (τ k.succ:ℝ)-τ k.castSucc ≤ ε) :
    ‖remainderSum Φ hΦ M hM r τ hτ halign‖ ≤
      ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt ε*((τ (Fin.last n):ℝ)-τ 0) := by
  calc
    _ ≤ ∑ k : Fin n, ‖remainderL2 Φ hΦ M hM r _ _ (hτ (Fin.castSucc_le_succ k)) (halign k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin n, ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt ε*((τ k.succ:ℝ)-τ k.castSucc) :=
      Finset.sum_le_sum (fun k _ => remainderL2_mesh_bound Φ hΦ M hM r _ _
        (hτ (Fin.castSucc_le_succ k)) (halign k) ε hε (hmesh k))
    _ = _ := by rw [← Finset.mul_sum, sum_fin_differences (fun k => (τ k : ℝ))]

omit s t hst hr in
theorem remainderSum_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N))
    (halign : ∀ N (k : Fin (m N)) i, r i ≤ τ N k.castSucc ∨ τ N k.succ ≤ r i)
    (L : ℝ) (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N)
    (hlength : ∀ N, (τ N (Fin.last (m N)):ℝ)-τ N 0 ≤ L) :
    Tendsto (fun N => remainderSum Φ hΦ M hM r (τ N) (hτ N) (halign N)) atTop (𝓝 0) := by
  have hb (N : ℕ) : ‖remainderSum Φ hΦ M hM r (τ N) (hτ N) (halign N)‖ ≤
      ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt (ε N)*L :=
    (remainderSum_mesh_bound Φ hΦ M hM r (τ N) (hτ N) (halign N) (ε N) (hε N) (hmesh N)).trans
      (mul_le_mul_of_nonneg_left (hlength N) (by positivity))
  have hz : Tendsto (fun N => ((M:ℝ)/6)*Real.sqrt 15*Real.sqrt (ε N)*L) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul] using
      ((Real.continuous_sqrt.continuousAt.tendsto.comp hlim).const_mul (((M:ℝ)/6)*Real.sqrt 15)).mul_const L
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun N => norm_nonneg _) hb hz

end OperatorDerivativeRewrite.Foundation.GaussianStoppedTaylor
