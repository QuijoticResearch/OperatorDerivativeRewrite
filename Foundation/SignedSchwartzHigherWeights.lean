import Foundation.SignedSchwartzLogDerivative
import Foundation.QuarticAppellDualDensity

/-! Measurable L1 coordinate weights relative to actual sign-changing heat laws. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzHigherWeights
open SignedAbsoluteIntegration

def realJet : ℕ → 𝓢(ℝ,ℝ) → 𝓢(ℝ,ℝ)
  | 0, K => K
  | n+1, K => SchwartzMap.derivCLM ℝ ℝ (realJet n K)

theorem realJet_zero_ae (n : ℕ) (K : 𝓢(ℝ,ℝ)) :
    ∀ᵐ x : ℝ, K x=0 → realJet n K x=0 := by
  induction n with
  | zero => exact Eventually.of_forall fun x => id
  | succ n ih =>
    have hd := DifferentiableZeroSet.derivative_zero_on_zero_ae (realJet n K)
      (fun x => deriv (realJet n K) x) (fun x => (realJet n K).hasDerivAt x)
    filter_upwards [ih, hd] with x hx hh
    intro hz
    change (SchwartzMap.derivCLM ℝ ℝ (realJet n K)) x=0
    rw [SchwartzMap.derivCLM_apply]
    exact hh (hx hz)

def numerator (n : ℕ) (K : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℝ) :=
  ((-1:ℝ)^n / (n.factorial:ℝ)) • realJet n K

def weight (n : ℕ) (K : 𝓢(ℝ,ℝ)) (x : ℝ) : ℝ := numerator n K x / K x

theorem weight_measurable (n : ℕ) (K : 𝓢(ℝ,ℝ)) : Measurable (weight n K) :=
  (numerator n K).continuous.measurable.div K.continuous.measurable

theorem weight_cancel (n : ℕ) (K : 𝓢(ℝ,ℝ)) :
    (fun x : ℝ => K x*weight n K x) =ᵐ[volume] (numerator n K : ℝ → ℝ) := by
  filter_upwards [realJet_zero_ae n K] with x hx
  by_cases hz : K x=0
  · simp [weight, numerator, hz, hx hz]
  · unfold weight
    field_simp

theorem polynomial_weight_absolute_integrable (n : ℕ) (K : 𝓢(ℝ,ℝ)) (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ)*(weight n K x:ℂ))
      (absoluteDensity volume K) := by
  apply (absolute_integrable_iff volume K K.continuous.measurable _).mpr
  have hi : Integrable (fun x : ℝ => |P.eval x*numerator n K x|) := by
    simpa only [SchwartzPolynomialSeparation.polynomialKernel_apply, Real.norm_eq_abs] using
      (SchwartzPolynomialSeparation.polynomialKernel P (numerator n K)).integrable.norm
  refine hi.mono' ?_ ?_
  · have hmabs : Measurable (fun x : ℝ => |K x|) := by
      simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
    exact (hmabs.smul ((Complex.measurable_ofReal.comp P.continuous.measurable).mul
      (Complex.measurable_ofReal.comp (weight_measurable n K)))).aestronglyMeasurable
  · filter_upwards [weight_cancel n K] with x hx
    simp only [norm_smul, Real.norm_eq_abs, abs_abs, norm_mul, Complex.norm_real]
    calc
      _ = |P.eval x| * |K x*weight n K x| := by rw [abs_mul]; ring
      _ ≤ |P.eval x*numerator n K x| := by rw [hx, abs_mul]

theorem polynomial_weight_integral (n : ℕ) (K : 𝓢(ℝ,ℝ)) (P : Polynomial ℝ) :
    (∫ᵛ x : ℝ, ((P.eval x:ℝ):ℂ)*(weight n K x:ℂ)
      ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) =
      (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*(numerator n K x:ℂ)) := by
  rw [integral_density volume K K.integrable K.continuous.measurable _
    (polynomial_weight_absolute_integrable n K P)]
  apply integral_congr_ae
  filter_upwards [weight_cancel n K] with x hx
  simp only [Complex.real_smul]
  calc
    _ = ((P.eval x:ℝ):ℂ)*((K x:ℂ)*(weight n K x:ℂ)) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, hx]

theorem realJet_complexify (n : ℕ) (K : 𝓢(ℝ,ℝ)) (x : ℝ) :
    (realJet n K x:ℂ) = HigherHeatSpatialGenerator.jet n (K.postcompCLM Complex.ofRealCLM) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have he : (HigherHeatSpatialGenerator.jet n (K.postcompCLM Complex.ofRealCLM) : ℝ → ℂ) =
        (fun y : ℝ => (realJet n K y:ℂ)) := funext fun y => (ih y).symm
    change ((SchwartzMap.derivCLM ℝ ℝ (realJet n K)) x:ℂ) =
      (SchwartzMap.derivCLM ℂ ℂ
        (HigherHeatSpatialGenerator.jet n (K.postcompCLM Complex.ofRealCLM))) x
    rw [SchwartzMap.derivCLM_apply, SchwartzMap.derivCLM_apply, he]
    exact ((realJet n K).hasDerivAt x).ofReal_comp.deriv.symm

theorem actual_numerator (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (x : ℝ) :
    (numerator n (HigherHeatSignedLaws.realKernel 2 (by norm_num) t ht) x:ℂ) =
      QuarticAppellDualDensity.density t ht n x := by
  have he : (HigherHeatSignedLaws.realKernel 2 (by norm_num) t ht).postcompCLM Complex.ofRealCLM =
      GaussianSchwartzKernel.evenKernel 2 (by norm_num) t ht := by
    ext y
    exact HigherHeatSignedLaws.realKernel_coe 2 (by norm_num) t ht y
  simp only [numerator, QuarticAppellDualDensity.density, SchwartzMap.smul_apply, smul_eq_mul]
  push_cast
  rw [realJet_complexify, he]

theorem actual_coordinate_integral (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (P : Polynomial ℝ) :
    (∫ᵛ x : ℝ, ((P.eval x:ℝ):ℂ)*
      (weight n (HigherHeatSignedLaws.realKernel 2 (by norm_num) t ht) x:ℂ)
      ∂<•HigherHeatSignedLaws.law 2 (by norm_num) t ht) =
      (((QuarticAppellExpansion.basis (-(t:ℝ))).repr P n:ℝ):ℂ) := by
  rw [HigherHeatSignedLaws.law, polynomial_weight_integral]
  simp_rw [actual_numerator]
  exact QuarticAppellDualDensity.density_coordinate t ht n P

theorem actual_biorthogonal (t : ℝ≥0) (ht : 0 < t) (n k : ℕ) :
    (∫ᵛ x : ℝ, (((QuarticAppellCalculus.appell (-(t:ℝ)) k).eval x:ℝ):ℂ)*
      (weight n (HigherHeatSignedLaws.realKernel 2 (by norm_num) t ht) x:ℂ)
      ∂<•HigherHeatSignedLaws.law 2 (by norm_num) t ht) = if k=n then 1 else 0 := by
  rw [actual_coordinate_integral, ← Module.Basis.coord_apply,
    ← QuarticAppellExpansion.coordinate_eq_basis_coord, QuarticAppellExpansion.coordinate_appell]
  split_ifs <;> norm_num

end OperatorDerivativeRewrite.Foundation.SignedSchwartzHigherWeights
