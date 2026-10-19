import Foundation.IBMPhysicalDiracDifference
import Foundation.IBMPhysicalDerivativeKernel
import Foundation.IBMDeltaBoundary

/-! Actual translated Dirac masses in physical H^-1, reusing the verified
Fourier construction at zero and the physical distributional derivative. -/
noncomputable section
open MeasureTheory TemperedDistribution Filter
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalDirac
open GaussianTimeHilbert IBMPhysicalNoiseVectors IBMPhysicalNoiseCalculus
open IBMPhysicalNoiseClock IBMPhysicalDiracDifference IBMPhysicalDerivativeKernel
open IBMDeltaBoundary InfiniteGaussian

def l2Value (u : TimeHilbert) : H^{(-1 : ℝ)}(ℝ) :=
  (TemperedDistribution.MemSobolev.mono (by norm_num : (-1 : ℝ) ≤ 0)
    (memSobolev_zero_iff.mpr ⟨complexify u, rfl⟩)).toBesselPotentialSpace

theorem l2Value_toDistr (u : TimeHilbert) :
    (l2Value u).toDistr = (complexify u : Lp ℂ 2 volume) := rfl

def test (g : 𝓢(ℝ,ℂ)) : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℂ :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ g).comp
    IBMNegativeSobolevBounded.hminusOneToDistrCLM).restrictScalars ℝ

theorem test_apply (g : 𝓢(ℝ,ℂ)) (u : H^{(-1 : ℝ)}(ℝ)) :
    test g u = u.toDistr g := by
  change IBMNegativeSobolevBounded.hminusOneToDistrCLM u g = _
  rw [IBMNegativeSobolevBounded.hminusOneToDistrCLM_apply]

theorem derivative_convolution_test {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) (g : 𝓢(ℝ,ℂ)) :
    (physicalDerivative (convolutionKernel ρ x)).toDistr g =
      ∫ r, ρ (x-r) • (g 0-g r) := by
  let L := (test g).comp physicalDerivative
  have he : L (convolutionKernel ρ x) = ∫ r, L (ρ (x-r) • vector r) :=
    (L.integral_comp_comm (convolutionKernel_integrable hc hs x)).symm
  rw [← test_apply]
  change L (convolutionKernel ρ x) = _
  rw [he]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    change L (ρ (x-r) • vector r) = ρ (x-r) • (g 0-g r)
    rw [map_smul]
    change ρ (x-r) • (test g (physicalDerivative (vector r))) = _
    rw [test_apply]
    rw [physicalDerivative_vector_toDistr]
    rfl

def translated (n : ℕ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  l2Value (translatedClass (IBMMollifier.kernel n) (IBMMollifier.kernel_smooth n).continuous
    (IBMMollifier.kernel_compactSupport n) r)

theorem translated_test (n : ℕ) (r : ℝ) (g : 𝓢(ℝ,ℂ)) :
    (translated n r).toDistr g = ∫ w, g w*(IBMMollifier.kernel n (r-w) : ℂ) := by
  rw [translated, l2Value_toDistr, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
      (translatedClass (IBMMollifier.kernel n) (IBMMollifier.kernel_smooth n).continuous
        (IBMMollifier.kernel_compactSupport n) r),
    translatedClass_coeFn (IBMMollifier.kernel n) (IBMMollifier.kernel_smooth n).continuous
      (IBMMollifier.kernel_compactSupport n) r] with w hc ht
  change complexify _ w = Complex.ofReal _ at hc
  rw [hc, ht, smul_eq_mul]
  simp

theorem translated_plus_derivative (n : ℕ) (r : ℝ) :
    (translated n r+physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r)).toDistr =
      delta (0 : ℝ) := by
  ext g
  rw [BesselPotentialSpace.toDistr_add]
  change (translated n r).toDistr g+
    (physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r)).toDistr g = g 0
  rw [translated_test, derivative_convolution_test (IBMMollifier.kernel_smooth n).continuous
    (IBMMollifier.kernel_compactSupport n)]
  let k : ℝ → ℝ := fun w => IBMMollifier.kernel n (r-w)
  have hk : Continuous k := (IBMMollifier.kernel_smooth n).continuous.comp
    (continuous_const.sub continuous_id)
  have hks : HasCompactSupport k := (IBMMollifier.kernel_compactSupport n).comp_homeomorph
    (Homeomorph.subLeft r)
  have h1 : Integrable (fun w => g w*(k w : ℂ)) volume :=
    (g.continuous.mul (Complex.continuous_ofReal.comp hk)).integrable_of_hasCompactSupport
      (hks.comp_left (by simp)).mul_left
  have h2 : Integrable (fun w => (k w : ℝ) • (g 0-g w)) volume :=
    (hk.smul (continuous_const.sub g.continuous)).integrable_of_hasCompactSupport hks.smul_right
  change (∫ w, g w*(k w : ℂ))+(∫ w, (k w : ℝ) • (g 0-g w)) = _
  rw [← integral_add h1 h2]
  have he : (fun w => g w*(k w : ℂ)+(k w : ℝ) • (g 0-g w)) =
      fun w => (k w : ℂ)*g 0 := by
    funext w
    simp only [Complex.real_smul]
    ring
  rw [he, integral_mul_const, integral_complex_ofReal]
  have hm : ∫ w, k w = 1 := by
    rw [show k = fun w => IBMMollifier.kernel n (r-w) from rfl,
      integral_sub_left_eq_self _ volume r, IBMMollifier.kernel_integral]
  rw [hm]
  simp

def dirac (r : ℝ) : H^{(-1 : ℝ)}(ℝ) := deltaZeroHminusOne-physicalDerivative (vector r)

theorem dirac_toDistr (r : ℝ) : (dirac r).toDistr = delta r := by
  rw [dirac, BesselPotentialSpace.toDistr_sub, deltaZeroHminusOne_toDistr,
    physicalDerivative_vector_toDistr]
  abel

theorem translated_eq (n : ℕ) (r : ℝ) :
    translated n r = deltaZeroHminusOne-
      physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r) := by
  have he : translated n r+physicalDerivative (convolutionKernel (IBMMollifier.kernel n) r) =
      deltaZeroHminusOne := by
    apply BesselPotentialSpace.ext
    rw [translated_plus_derivative, deltaZeroHminusOne_toDistr]
  exact eq_sub_of_add_eq he

theorem translated_tendsto (r : ℝ) :
    Tendsto (fun n => translated n r) atTop (𝓝 (dirac r)) := by
  simp_rw [translated_eq]
  exact tendsto_const_nhds.sub
    (physicalDerivative.continuous.tendsto _ |>.comp (mollifier_kernel_tendsto r))

theorem dirac_continuous : Continuous dirac :=
  continuous_const.sub (physicalDerivative.continuous.comp vector_continuous)

theorem dirac_difference_bound (r s : ℝ) :
    ‖dirac r-dirac s‖ ≤ ‖physicalDerivative‖*Real.sqrt |s-r| := by
  have he : dirac r-dirac s = difference r s := by
    simp only [dirac, difference, map_sub]
    abel
  rw [he]
  exact difference_bound r s

def mollifiedDirac (n : ℕ) (T : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  Lp.const 2 gaussianProduct deltaZeroHminusOne-mollifiedDerivative n T

def diracClass (T : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  Lp.const 2 gaussianProduct deltaZeroHminusOne-sourceDerivative T

theorem mollifiedDirac_ae (n : ℕ) (T : ℝ≥0) : mollifiedDirac n T =ᵐ[gaussianProduct]
    fun ω => translated n |IBMConstructedSources.clockPath ω T| := by
  filter_upwards [Lp.coeFn_sub (Lp.const 2 gaussianProduct deltaZeroHminusOne)
      (mollifiedDerivative n T),
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := deltaZeroHminusOne),
    mollifiedDerivative_ae n T] with ω hs hc hd
  change mollifiedDirac n T ω = _ at hs
  rw [hs, Pi.sub_apply, hc, hd, translated_eq]
  rfl

theorem diracClass_ae (T : ℝ≥0) : diracClass T =ᵐ[gaussianProduct]
    fun ω => dirac |IBMConstructedSources.clockPath ω T| := by
  filter_upwards [Lp.coeFn_sub (Lp.const 2 gaussianProduct deltaZeroHminusOne)
      (sourceDerivative T),
    Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := deltaZeroHminusOne),
    sourceDerivative_ae T] with ω hs hc hd
  change diracClass T ω = _ at hs
  rw [hs, Pi.sub_apply, hc, hd]
  rfl

/-- Strong L2(clock;H^-1(physical space)) convergence of actual translated
mollifier functions to actual Dirac masses at the constructed clock. -/
theorem mollifiedDirac_tendsto (T : ℝ≥0) :
    Tendsto (fun n => mollifiedDirac n T) atTop (𝓝 (diracClass T)) :=
  tendsto_const_nhds.sub (mollifiedDerivative_tendsto T)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalDirac
