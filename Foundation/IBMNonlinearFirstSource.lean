import Foundation.IBMFirstChaosMixedStein
import Foundation.IBMUnmollifiedSourceDerivative
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Exact first-source projections of bounded smooth Gaussian tests, and the
actual sine of the original Brownian scenery. No derivative-domain claim is
inferred from boundedness or smoothness of the scalar test. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearFirstSource
open InfiniteGaussian IBMFirstChaosMixedStein IBMFirstChaosDiagonalStein
open IBMContinuousScenery SeparableHilbertEmbedding FractionalSpectralKernel
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  spectralSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem first_adjoint (u : CoefficientSpace) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) {A B : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A)
    (hB : ∀ x, ‖deriv φ x‖ ≤ B) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (testClass u hφ.continuous hA) =
      (∫ ω, deriv φ (firstChaosEmbedding u ω) ∂gaussianProduct) • u := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  change inner ℝ (firstChaosEmbedding v) (testClass u hφ.continuous hA) = _
  rw [first_pairing u v hφ.continuous hA, first_pairing_integral u u hφ.continuous hA,
    first_diagonal hφ hA hB u, real_inner_smul_left]
  calc
    _ = (regression u v * ‖u‖^2) *
        ∫ ω, deriv φ (firstChaosEmbedding u ω) ∂gaussianProduct := by ring
    _ = _ := by rw [regression_energy]; ring

theorem cosine_mean (u : CoefficientSpace) :
    (∫ ω, Real.cos (firstChaosEmbedding u ω) ∂gaussianProduct) = Real.exp (-‖u‖^2/2) := by
  let z : SampleSpace → ℂ := fun ω => Complex.exp ((firstChaosEmbedding u ω : ℂ) * Complex.I)
  have hc0 : Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) := by fun_prop
  have hzm : AEStronglyMeasurable z gaussianProduct :=
    hc0.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (firstChaosEmbedding u))
  have hz : Integrable z gaussianProduct :=
    Integrable.of_bound hzm 1
        (Filter.Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le)
  have hm := integral_map (μ := gaussianProduct)
    (Lp.stronglyMeasurable (firstChaosEmbedding u)).aemeasurable
    (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) (by fun_prop)
  have hc := firstChaos_charFun u 1
  rw [charFun_apply_real] at hc
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at hc
  have he : (∫ ω, z ω ∂gaussianProduct) = (Real.exp (-‖u‖^2/2) : ℂ) := by
    calc
      _ = ∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
          ∂gaussianProduct.map (firstChaosEmbedding u) := hm.symm
      _ = _ := by simpa only [Complex.ofReal_exp, Complex.ofReal_div,
        Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat] using hc
  have hr := congrArg Complex.re he
  have hi := integral_re hz
  change (∫ ω, (z ω).re ∂gaussianProduct) = (∫ ω, z ω ∂gaussianProduct).re at hi
  calc
    _ = ∫ ω, (z ω).re ∂gaussianProduct := integral_congr_ae
      (Filter.Eventually.of_forall fun ω => (Complex.exp_ofReal_mul_I_re _).symm)
    _ = _ := hi
    _ = _ := by simpa only [Complex.ofReal_re] using hr

def sineClass (u : CoefficientSpace) : GaussianL2 :=
  testClass u Real.continuous_sin (fun x => Real.abs_sin_le_one x)

theorem sineClass_ae (u : CoefficientSpace) :
    sineClass u =ᵐ[gaussianProduct] fun ω => Real.sin (firstChaosEmbedding u ω) :=
  testClass_coeFn _ _ _

theorem sine_adjoint (u : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (sineClass u) =
      Real.exp (-‖u‖^2/2) • u := by
  have h := first_adjoint u Real.contDiff_sin (fun x => Real.abs_sin_le_one x)
    (B := 1) (fun x => by simpa only [Real.deriv_sin, Real.norm_eq_abs] using Real.abs_cos_le_one x)
  simpa only [sineClass, Real.deriv_sin, cosine_mean] using h

def projection : GaussianL2 →L[ℝ] GaussianL2 :=
  firstChaosEmbedding.toContinuousLinearMap.comp firstChaosEmbedding.toContinuousLinearMap.adjoint

theorem sine_projection (u : CoefficientSpace) :
    projection (sineClass u) = Real.exp (-‖u‖^2/2) • firstChaosEmbedding u := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint (sineClass u)) = _
  rw [sine_adjoint, map_smul]

theorem sineClass_lipschitz : LipschitzWith 1 sineClass := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro u v
  have hb : ‖sineClass u - sineClass v‖ ≤ 1 * ‖firstChaosEmbedding u - firstChaosEmbedding v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul (c := 1)
    filter_upwards [sineClass_ae u, sineClass_ae v,
      Lp.coeFn_sub (sineClass u) (sineClass v),
      Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hu hv hs hd
    simp only [hs, Pi.sub_apply, hu, hv, hd]
    exact Real.lipschitzWith_sin.norm_sub_le _ _
  simpa only [← map_sub, firstChaosEmbedding.norm_map, NNReal.coe_one, one_mul] using hb

theorem sineClass_norm_le (u : CoefficientSpace) : ‖sineClass u‖ ≤ 1 := by
  have hb : ∀ᵐ ω ∂gaussianProduct, ‖sineClass u ω‖ ≤ (1 : ℝ) := by
    filter_upwards [sineClass_ae u] with ω hw
    rw [hw]
    exact Real.abs_sin_le_one _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (f := sineClass u) (by norm_num) hb

def sceneryDirection (r : ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (IBMFiniteScenerySmoothing.direction r)

theorem sourceScenery_first (r : ℝ) : sourceScenery r = firstChaosEmbedding (sceneryDirection r) := rfl

theorem sceneryDirection_norm_sq (r : ℝ) : ‖sceneryDirection r‖^2 = |r| := by
  rw [← firstChaosEmbedding.norm_map]
  exact IBMRandomTimeHilbert.sourceScenery_norm_sq r

def scenerySine (r : ℝ) : GaussianL2 := sineClass (sceneryDirection r)

theorem scenerySine_ae (r : ℝ) :
    scenerySine r =ᵐ[gaussianProduct] fun ω => Real.sin (sourceScenery r ω) := sineClass_ae _

theorem scenerySine_projection (r : ℝ) :
    projection (scenerySine r) = Real.exp (-|r|/2) • sourceScenery r := by
  rw [scenerySine, sine_projection, sceneryDirection_norm_sq, ← sourceScenery_first]

theorem scenerySine_continuous : Continuous scenerySine :=
  sineClass_lipschitz.continuous.comp
    ((hilbertEmbedding SpectralSpace).continuous.comp direction_continuous)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearFirstSource
