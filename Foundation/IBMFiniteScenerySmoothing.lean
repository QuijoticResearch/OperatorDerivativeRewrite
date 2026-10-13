import Foundation.IBMSourceMoments
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite positive spatial smoothing of the genuine Gaussian scenery source.
The estimate is proved in source L² before constructing continuous paths or
pathwise convolution, following the integration-first order of development. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OperatorDerivativeRewrite.Foundation.IBMFiniteScenerySmoothing
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMSourceLaws
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def direction (r : ℝ) : SpectralSpace :=
  normalized (1/2) (by norm_num) (by norm_num) r

/-- A finite positive spatial average at the Hilbert-coordinate level. -/
def smoothDirection (I : Finset ℝ) (w : ℝ → ℝ) : SpectralSpace :=
  ∑ r ∈ I, w r • direction r

/-- The corresponding genuine Gaussian L² random variable. -/
def smoothScenery (I : Finset ℝ) (w : ℝ → ℝ) : GaussianL2 :=
  isonormalEmbedding SpectralSpace (smoothDirection I w)

/-- The literal finite weighted sum of verified Brownian scenery coordinates. -/
def finiteSceneryValue (I : Finset ℝ) (w : ℝ → ℝ) (ω : SampleSpace) : ℝ :=
  ∑ r ∈ I, w r * sceneryBase r ω

/-- The Gaussian L² smoothing construction agrees almost everywhere with
the literal finite weighted sum of source coordinates. -/
theorem smoothScenery_ae_eq_finiteValue (I : Finset ℝ) (w : ℝ → ℝ) :
    (smoothScenery I w : SampleSpace → ℝ) =ᵐ[gaussianProduct]
      finiteSceneryValue I w := by
  have heq : smoothScenery I w =
      ∑ r ∈ I, w r • isonormalEmbedding SpectralSpace (direction r) := by
    unfold smoothScenery smoothDirection
    rw [map_sum]
    simp_rw [map_smul]
  rw [heq]
  have hs := Lp.coeFn_finsetSum I
    (fun r => w r • isonormalEmbedding SpectralSpace (direction r))
  have ht : (∑ r ∈ I, ((w r • isonormalEmbedding SpectralSpace (direction r)) : GaussianL2) :
      SampleSpace → ℝ) =ᵐ[gaussianProduct] finiteSceneryValue I w := by
    have hsum := eventuallyEq_sum (s := I) (fun r hr =>
      Lp.coeFn_smul (w r) (isonormalEmbedding SpectralSpace (direction r)))
    have hv : (∑ r ∈ I,
        w r • (isonormalEmbedding SpectralSpace (direction r) : SampleSpace → ℝ)) =
        finiteSceneryValue I w := by
      funext ω
      simp [finiteSceneryValue, sceneryBase, isonormal, direction,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hv] at hsum
    exact hsum
  exact hs.trans ht

/-- The actual finite random-variable smoothing error has the exact second
moment of its spectral Hilbert direction. -/
theorem finiteScenery_error_second (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) :
    (∫ ω, (finiteSceneryValue I w ω - sceneryBase x ω)^2 ∂gaussianProduct) =
      ‖smoothDirection I w - direction x‖ ^ 2 := by
  let v := smoothDirection I w - direction x
  have he : (fun ω => (finiteSceneryValue I w ω - sceneryBase x ω)^2) =ᵐ[gaussianProduct]
      (fun ω => (isonormal SpectralSpace v ω)^2) := by
    filter_upwards [(smoothScenery_ae_eq_finiteValue I w).symm,
      isonormal_sub_ae (smoothDirection I w) (direction x)] with ω hval hsub
    change finiteSceneryValue I w ω = isonormal SpectralSpace (smoothDirection I w) ω at hval
    change isonormal SpectralSpace v ω =
      isonormal SpectralSpace (smoothDirection I w) ω - sceneryBase x ω at hsub
    rw [hval, hsub]
  rw [integral_congr_ae he]
  have h := isonormal_product_integral v v
  simpa [v, pow_two, real_inner_self_eq_norm_sq] using h

/-- Brownian scenery increments have exactly the square-mean spatial distance. -/
theorem direction_increment_sq (x r : ℝ) :
    ‖direction r - direction x‖ ^ 2 = |r - x| := by
  simpa [direction] using
    (normalized_sub_norm_sq (1/2) (by norm_num) (by norm_num) x r)

private theorem direction_zero : direction 0 = 0 := by
  have h := normalized_norm_sq (1/2) (by norm_num) (by norm_num) (0 : ℝ)
  have hn : ‖direction 0‖ ^ 2 = 0 := by simpa [direction] using h
  have hn0 : ‖direction 0‖ = 0 := by nlinarith [norm_nonneg (direction 0)]
  exact norm_eq_zero.mp hn0

/-- Finite Jensen form of the paper's uniform spatial mollifier estimate:
the squared error is bounded by the kernel's first absolute moment. -/
theorem smoothDirection_error_sq_le_weighted
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    ‖smoothDirection I w - direction x‖ ^ 2 ≤
      ∑ r ∈ I, w r * |r - x| := by
  have heq : smoothDirection I w - direction x =
      ∑ r ∈ I, w r • (direction r - direction x) := by
    simp only [smoothDirection, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hmass, one_smul]
  have htri : ‖smoothDirection I w - direction x‖ ≤
      ∑ r ∈ I, w r * ‖direction r - direction x‖ := by
    rw [heq]
    calc
      _ ≤ ∑ r ∈ I, ‖w r • (direction r - direction x)‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw r hr)]
  have hcs : (∑ r ∈ I, w r * ‖direction r - direction x‖) ^ 2 ≤
      ∑ r ∈ I, w r * ‖direction r - direction x‖ ^ 2 := by
    have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul I
      (r := fun r => w r * ‖direction r - direction x‖)
      (f := w)
      (g := fun r => w r * ‖direction r - direction x‖ ^ 2)
      hw
      (fun r hr => mul_nonneg (hw r hr) (sq_nonneg _))
      (fun r hr => by ring_nf; exact le_rfl)
    simpa only [hmass, one_mul] using hc
  have hnonneg : 0 ≤ ∑ r ∈ I, w r * ‖direction r - direction x‖ := by
    apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hw r hr) (norm_nonneg _)
  calc
    ‖smoothDirection I w - direction x‖ ^ 2 ≤
        (∑ r ∈ I, w r * ‖direction r - direction x‖) ^ 2 := by
      nlinarith [norm_nonneg (smoothDirection I w - direction x)]
    _ ≤ ∑ r ∈ I, w r * ‖direction r - direction x‖ ^ 2 := hcs
    _ = ∑ r ∈ I, w r * |r - x| := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [direction_increment_sq]

/-- Literal expectation form of the paper's scenery mollifier estimate for
arbitrary finite positive mass-one spatial kernels. -/
theorem finiteScenery_error_second_le_weighted
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    (∫ ω, (finiteSceneryValue I w ω - sceneryBase x ω)^2 ∂gaussianProduct) ≤
      ∑ r ∈ I, w r * |r - x| := by
  rw [finiteScenery_error_second]
  exact smoothDirection_error_sq_le_weighted I w x hw hmass

/-- The paper's first-absolute-moment estimate for finite positive kernels,
now stated for the genuine Gaussian L² scenery realization. -/
theorem smoothScenery_error_sq_le_weighted
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    ‖smoothScenery I w - isonormalEmbedding SpectralSpace (direction x)‖ ^ 2 ≤
      ∑ r ∈ I, w r * |r - x| := by
  simpa only [smoothScenery, ← (isonormalEmbedding SpectralSpace).map_sub,
    (isonormalEmbedding SpectralSpace).norm_map] using
    smoothDirection_error_sq_le_weighted I w x hw hmass

/-- The finite-kernel Cameron–Martin energy is bounded by the basepoint
distance plus the kernel's first absolute moment, paralleling Lemma 2.2(a). -/
theorem smoothDirection_energy_le
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    ‖smoothDirection I w‖ ^ 2 ≤ |x| + ∑ r ∈ I, w r * |r - x| := by
  have hzero := smoothDirection_error_sq_le_weighted I w 0 hw hmass
  simp only [direction_zero, sub_zero, sub_zero] at hzero
  calc
    ‖smoothDirection I w‖ ^ 2 ≤ ∑ r ∈ I, w r * |r| := hzero
    _ ≤ ∑ r ∈ I, w r * (|x| + |r - x|) := by
      apply Finset.sum_le_sum
      intro r hr
      have htri : |r| ≤ |x| + |r - x| := by
        have h := abs_add_le x (r - x)
        simpa [add_sub_cancel_left] using h
      exact mul_le_mul_of_nonneg_left htri (hw r hr)
    _ = |x| + ∑ r ∈ I, w r * |r - x| := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hmass, one_mul]

/-- The energy estimate holds for the actual Gaussian L² variable. -/
theorem smoothScenery_energy_le
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    ‖smoothScenery I w‖ ^ 2 ≤ |x| + ∑ r ∈ I, w r * |r - x| := by
  simpa only [smoothScenery, (isonormalEmbedding SpectralSpace).norm_map] using
    smoothDirection_energy_le I w x hw hmass

/-- Every finitely supported positive averaging kernel of mass one and radius
`δ` approximates the Brownian scenery Hilbert direction with error at most
`√δ`. No continuous modification is assumed. -/
theorem smoothDirection_error_le
    (I : Finset ℝ) (w : ℝ → ℝ) (x δ : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1)
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ I, |r - x| ≤ δ) :
    ‖smoothDirection I w - direction x‖ ≤ Real.sqrt δ := by
  have hpoint (r : ℝ) (hr : r ∈ I) :
      ‖direction r - direction x‖ ≤ Real.sqrt δ := by
    have hs := direction_increment_sq x r
    have hrad := hradius r hr
    have hroot := Real.sq_sqrt hδ
    have hn := norm_nonneg (direction r - direction x)
    have hsqr := Real.sqrt_nonneg δ
    nlinarith
  have heq : smoothDirection I w - direction x =
      ∑ r ∈ I, w r • (direction r - direction x) := by
    simp only [smoothDirection, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul]
    rw [hmass, one_smul]
  rw [heq]
  calc
    ‖∑ r ∈ I, w r • (direction r - direction x)‖ ≤
        ∑ r ∈ I, ‖w r • (direction r - direction x)‖ := norm_sum_le _ _
    _ = ∑ r ∈ I, w r * ‖direction r - direction x‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw r hr)]
    _ ≤ ∑ r ∈ I, w r * Real.sqrt δ := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hpoint r hr) (hw r hr)
    _ = Real.sqrt δ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- The finite positive spatial average approximates the actual isonormal
Brownian scenery in Gaussian L², with squared error at most its radius. -/
theorem smoothScenery_error_sq_le
    (I : Finset ℝ) (w : ℝ → ℝ) (x δ : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1)
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ I, |r - x| ≤ δ) :
    ‖smoothScenery I w - isonormalEmbedding SpectralSpace (direction x)‖ ^ 2 ≤ δ := by
  have hnorm := smoothDirection_error_le I w x δ hw hmass hδ hradius
  have hiso : ‖smoothScenery I w - isonormalEmbedding SpectralSpace (direction x)‖ =
      ‖smoothDirection I w - direction x‖ := by
    rw [smoothScenery, ← (isonormalEmbedding SpectralSpace).map_sub]
    exact (isonormalEmbedding SpectralSpace).norm_map _
  rw [hiso]
  nlinarith [Real.sq_sqrt hδ, norm_nonneg (smoothDirection I w - direction x),
    Real.sqrt_nonneg δ]

/-- The finite smoothing error has the exact Gaussian fourth moment, so the
same source-first construction also provides fourth-order control. -/
theorem smoothScenery_error_fourth
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) :
    (∫ ω, (isonormal SpectralSpace (smoothDirection I w - direction x) ω)^4
      ∂gaussianProduct) =
      3 * (‖smoothDirection I w - direction x‖ ^ 2)^2 := by
  change (∫ ω, (firstChaosEmbedding
    (SeparableHilbertEmbedding.hilbertEmbedding SpectralSpace
      (smoothDirection I w - direction x)) ω)^4 ∂gaussianProduct) = _
  rw [IBMSourceMoments.firstChaos_fourth]
  rw [(SeparableHilbertEmbedding.hilbertEmbedding SpectralSpace).norm_map]

/-- The literal finite scenery sum has the exact fourth error moment of its
Gaussian Hilbert direction. -/
theorem finiteScenery_error_fourth (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) :
    (∫ ω, (finiteSceneryValue I w ω - sceneryBase x ω)^4 ∂gaussianProduct) =
      3 * (‖smoothDirection I w - direction x‖ ^ 2)^2 := by
  let v := smoothDirection I w - direction x
  have he : (fun ω => (finiteSceneryValue I w ω - sceneryBase x ω)^4) =ᵐ[gaussianProduct]
      (fun ω => (isonormal SpectralSpace v ω)^4) := by
    filter_upwards [(smoothScenery_ae_eq_finiteValue I w).symm,
      isonormal_sub_ae (smoothDirection I w) (direction x)] with ω hval hsub
    change finiteSceneryValue I w ω = isonormal SpectralSpace (smoothDirection I w) ω at hval
    change isonormal SpectralSpace v ω =
      isonormal SpectralSpace (smoothDirection I w) ω - sceneryBase x ω at hsub
    rw [hval, hsub]
  rw [integral_congr_ae he]
  exact smoothScenery_error_fourth I w x

/-- The genuine Gaussian fourth moment is controlled by the square of the
finite kernel's first absolute spatial moment. -/
theorem smoothScenery_error_fourth_le_weighted
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    (∫ ω, (isonormal SpectralSpace (smoothDirection I w - direction x) ω)^4
      ∂gaussianProduct) ≤
      3 * (∑ r ∈ I, w r * |r - x|)^2 := by
  rw [smoothScenery_error_fourth]
  have hsq := smoothDirection_error_sq_le_weighted I w x hw hmass
  have hmoment : 0 ≤ ∑ r ∈ I, w r * |r - x| := by
    apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hw r hr) (abs_nonneg _)
  nlinarith [sq_nonneg (‖smoothDirection I w - direction x‖ ^ 2 -
    ∑ r ∈ I, w r * |r - x|)]

/-- The literal fourth moment is bounded by three times the squared first
absolute moment of any finite positive mass-one smoothing kernel. -/
theorem finiteScenery_error_fourth_le_weighted
    (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1) :
    (∫ ω, (finiteSceneryValue I w ω - sceneryBase x ω)^4 ∂gaussianProduct) ≤
      3 * (∑ r ∈ I, w r * |r - x|)^2 := by
  rw [finiteScenery_error_fourth]
  simpa only [smoothScenery_error_fourth] using
    smoothScenery_error_fourth_le_weighted I w x hw hmass

/-- A radius-`δ` positive finite smoothing kernel has fourth error moment
at most `3δ²`, using the genuine source Gaussian law. -/
theorem smoothScenery_error_fourth_le
    (I : Finset ℝ) (w : ℝ → ℝ) (x δ : ℝ)
    (hw : ∀ r ∈ I, 0 ≤ w r) (hmass : ∑ r ∈ I, w r = 1)
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ I, |r - x| ≤ δ) :
    (∫ ω, (isonormal SpectralSpace (smoothDirection I w - direction x) ω)^4
      ∂gaussianProduct) ≤ 3 * δ ^ 2 := by
  rw [smoothScenery_error_fourth]
  have hsq : ‖smoothDirection I w - direction x‖ ^ 2 ≤ δ := by
    simpa only [smoothScenery, ← (isonormalEmbedding SpectralSpace).map_sub,
      (isonormalEmbedding SpectralSpace).norm_map] using
      smoothScenery_error_sq_le I w x δ hw hmass hδ hradius
  nlinarith [sq_nonneg (‖smoothDirection I w - direction x‖ ^ 2 - δ)]

/-- Shrinking positive finite spatial kernels converge in genuine Gaussian L²
to the scenery coordinate, before any pathwise Brownian modification exists. -/
theorem smoothScenery_tendsto
    (I : ℕ → Finset ℝ) (w : ℕ → ℝ → ℝ) (x : ℝ) (δ : ℕ → ℝ)
    (hw : ∀ n r, r ∈ I n → 0 ≤ w n r)
    (hmass : ∀ n, ∑ r ∈ I n, w n r = 1)
    (hδ : ∀ n, 0 ≤ δ n)
    (hradius : ∀ n r, r ∈ I n → |r - x| ≤ δ n)
    (hδlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => smoothScenery (I n) (w n)) Filter.atTop
      (nhds (isonormalEmbedding SpectralSpace (direction x))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hroot : Filter.Tendsto (fun n => Real.sqrt (δ n)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hδlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hroot
    (fun n => norm_nonneg _)
    (fun n => by
      have hn := smoothDirection_error_le (I n) (w n) x (δ n)
        (hw n) (hmass n) (hδ n) (hradius n)
      simpa only [smoothScenery, ← (isonormalEmbedding SpectralSpace).map_sub,
        (isonormalEmbedding SpectralSpace).norm_map] using hn)

/-- Two literal finite scenery averages have the exact spectral cross moment. -/
theorem finiteScenery_cross_moment
    (I J : Finset ℝ) (w v : ℝ → ℝ) :
    (∫ ω, finiteSceneryValue I w ω * finiteSceneryValue J v ω
      ∂gaussianProduct) =
      inner ℝ (smoothDirection I w) (smoothDirection J v) := by
  have he : (fun ω => finiteSceneryValue I w ω * finiteSceneryValue J v ω) =ᵐ[gaussianProduct]
      (fun ω => isonormal SpectralSpace (smoothDirection I w) ω *
        isonormal SpectralSpace (smoothDirection J v) ω) := by
    filter_upwards [(smoothScenery_ae_eq_finiteValue I w).symm,
      (smoothScenery_ae_eq_finiteValue J v).symm] with ω hw hv
    change finiteSceneryValue I w ω = isonormal SpectralSpace (smoothDirection I w) ω at hw
    change finiteSceneryValue J v ω = isonormal SpectralSpace (smoothDirection J v) ω at hv
    rw [hw, hv]
  rw [integral_congr_ae he]
  exact isonormal_product_integral _ _

/-- Every finite scenery average is centered, with no normalization or
positivity assumption on its deterministic weights. -/
theorem finiteScenery_mean_zero (I : Finset ℝ) (w : ℝ → ℝ) :
    (∫ ω, finiteSceneryValue I w ω ∂gaussianProduct) = 0 := by
  rw [integral_congr_ae (smoothScenery_ae_eq_finiteValue I w).symm]
  exact isonormal_integral _

/-- The cross moment expands into the exact Brownian covariance matrix of
the finite spatial support points. This is the finite-kernel covariance
calculus underlying the paper's mollified scenery estimates. -/
theorem finiteScenery_cross_moment_covariance
    (I J : Finset ℝ) (w v : ℝ → ℝ) :
    (∫ ω, finiteSceneryValue I w ω * finiteSceneryValue J v ω
      ∂gaussianProduct) =
      ∑ r ∈ I, ∑ s ∈ J, w r * v s *
        FractionalSpectralGeometry.covariance (1/2) r s := by
  rw [finiteScenery_cross_moment]
  simp [smoothDirection, direction, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, normalized_inner,
    mul_assoc, mul_left_comm]
  rw [Finset.sum_comm]

/-- Exact covariance of two finite spatial averages, including signed
weights and overlapping supports. -/
theorem finiteScenery_covariance
    (I J : Finset ℝ) (w v : ℝ → ℝ) :
    cov[finiteSceneryValue I w, finiteSceneryValue J v; gaussianProduct] =
      ∑ r ∈ I, ∑ s ∈ J, w r * v s *
        FractionalSpectralGeometry.covariance (1/2) r s := by
  unfold ProbabilityTheory.covariance
  rw [finiteScenery_mean_zero I w, finiteScenery_mean_zero J v]
  simp only [sub_zero]
  exact finiteScenery_cross_moment_covariance I J w v

end OperatorDerivativeRewrite.Foundation.IBMFiniteScenerySmoothing
