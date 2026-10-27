import Foundation.CauchyPoissonForwardDensity
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Calculus.ContDiff.Operations
/-! Positive-time supremum-norm smoothness of the actual forward density.
Banach-algebra inversion and bounded initial-law integration give a genuine
continuous-function-valued derivative and the full generator transpose pairing.
No time-zero extension, maximal density domain or entropy-rate claim is made. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDensitySmooth
open CauchyPoissonFlow CauchyPoissonCoreGenerator

-- Banach-algebra inversion agrees with pointwise inversion at a unit.
theorem inverse_apply {X : Type*} [TopologicalSpace X] (f : C(X,ℂ))
    (hf : IsUnit f) (x : X) : (Ring.inverse f) x = (f x)⁻¹ := by
  rcases hf with ⟨u,rfl⟩
  rw [Ring.inverse_unit]
  have hx : (u : C(X,ℂ)) x ≠ 0 :=
    ((u : C(X,ℂ)).isUnit_iff_forall_ne_zero.mp u.isUnit) x
  apply mul_left_cancel₀ hx
  rw [mul_inv_cancel₀ hx]
  exact congrArg (fun F : C(X,ℂ) => F x) u.val_inv

def numeratorCurve (q t : ℝ) : C(Circle,ℂ) :=
  ((q:ℂ)*(1-(decay q t:ℂ))) • 1 + ((q:ℂ)^2+(decay q t:ℂ)) • coordinate

def denominatorCurve (q t : ℝ) : C(Circle,ℂ) :=
  (1+(q:ℂ)^2*(decay q t:ℂ)) • 1 + ((q:ℂ)*(1-(decay q t:ℂ))) • coordinate

theorem numeratorCurve_smooth (q : ℝ) : ContDiff ℝ ∞ (numeratorCurve q) := by
  have hd : ContDiff ℝ ∞ (decay q) := by unfold decay; fun_prop
  have hc : ContDiff ℝ ∞ (fun t => (decay q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hd
  unfold numeratorCurve
  fun_prop

theorem denominatorCurve_smooth (q : ℝ) : ContDiff ℝ ∞ (denominatorCurve q) := by
  have hd : ContDiff ℝ ∞ (decay q) := by unfold decay; fun_prop
  have hc : ContDiff ℝ ∞ (fun t => (decay q t : ℂ)) := Complex.ofRealCLM.contDiff.comp hd
  unfold denominatorCurve
  fun_prop

theorem denominatorCurve_unit (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    IsUnit (denominatorCurve q t) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro z
  have hz : coordinate z = (z:ℂ) := rfl
  simpa [denominatorCurve,denominator,hz,smul_eq_mul] using
    denominator_ne_zero q _ hq (decay_range q t hq ht).1 (decay_range q t hq ht).2 z (by simp)

def flowCurve (q t : ℝ) : C(Circle,ℂ) := numeratorCurve q t * Ring.inverse (denominatorCurve q t)

theorem flowCurve_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (z : Circle) :
    flowCurve q t z = evolution q t z := by
  rw [flowCurve,ContinuousMap.mul_apply,inverse_apply _ (denominatorCurve_unit q t hq ht)]
  have hz : coordinate z = (z:ℂ) := rfl
  simp [numeratorCurve,denominatorCurve,hz,evolution,flow,numerator,denominator,smul_eq_mul,div_eq_mul_inv]

theorem flowCurve_smooth (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (flowCurve q) t := by
  have hu := denominatorCurve_unit q t hq ht
  have hi : ContDiffAt ℝ ∞ Ring.inverse (denominatorCurve q t) := by
    simpa only [IsUnit.unit_spec] using (contDiffAt_ringInverse ℝ (n := ∞) hu.unit)
  exact (numeratorCurve_smooth q).contDiffAt.mul
    (hi.comp t (denominatorCurve_smooth q).contDiffAt)


def liftFirst : C(Circle,ℂ) →L[ℂ] C(Circle × Circle,ℂ) :=
  { toLinearMap := (ContinuousMap.compRightAlgHom ℂ ℂ ⟨Prod.fst,continuous_fst⟩).toLinearMap
    cont := ContinuousMap.compRightAlgHom_continuous ℂ ℂ ⟨Prod.fst,continuous_fst⟩ }

def secondCoordinate : C(Circle × Circle,ℂ) := ⟨fun p => (p.2:ℂ),by fun_prop⟩

def jointFlow (q t : ℝ) : C(Circle × Circle,ℂ) := liftFirst (flowCurve q t)

theorem jointFlow_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) (p : Circle × Circle) :
    jointFlow q t p = evolution q t p.1 := flowCurve_apply q t hq ht p.1

theorem jointFlow_smooth (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    ContDiffAt ℝ ∞ (jointFlow q) t :=
  (liftFirst.restrictScalars ℝ).contDiff.contDiffAt.comp t (flowCurve_smooth q t hq ht)

def poleDifference (q t : ℝ) : C(Circle × Circle,ℂ) := secondCoordinate - jointFlow q t

theorem poleDifference_unit (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    IsUnit (poleDifference q t) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  intro p
  change (p.2:ℂ) - jointFlow q t p ≠ 0
  rw [jointFlow_apply q t hq ht.le p]
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  simp only [Circle.norm_coe] at hn
  exact (ne_of_lt (evolution_strict_disk q t hq ht p.1 (by simp))) hn.symm

def poissonCurve (q t : ℝ) : C(Circle × Circle,ℂ) :=
  (1-star (jointFlow q t)*jointFlow q t) *
    (star (Ring.inverse (poleDifference q t))*Ring.inverse (poleDifference q t))

theorem poissonCurve_smooth (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (poissonCurve q) t := by
  have he := jointFlow_smooth q t hq ht.le
  have hd : ContDiffAt ℝ ∞ (poleDifference q) t := contDiffAt_const.sub he
  have hu := poleDifference_unit q t hq ht
  have hi : ContDiffAt ℝ ∞ Ring.inverse (poleDifference q t) := by
    simpa only [IsUnit.unit_spec] using (contDiffAt_ringInverse ℝ (n := ∞) hu.unit)
  have hinv := hi.comp t hd
  have hstar : ContDiff ℝ ∞ (star : C(Circle × Circle,ℂ) → C(Circle × Circle,ℂ)) :=
    (starL' ℝ : C(Circle × Circle,ℂ) ≃L[ℝ] C(Circle × Circle,ℂ)).toContinuousLinearMap.contDiff
  exact (contDiffAt_const.sub ((hstar.contDiffAt.comp t he).mul he)).mul
    ((hstar.contDiffAt.comp t hinv).mul hinv)


theorem normsq_complex (z : ℂ) : (‖z‖:ℂ)^2 = star z*z := by
  rw [← Complex.ofReal_pow,Complex.sq_norm]
  apply Complex.ext <;> simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem poissonCurve_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (p : Circle × Circle) :
    poissonCurve q t p = (poissonKernel 0 (evolution q t p.1) p.2 : ℂ) := by
  have hi := inverse_apply _ (poleDifference_unit q t hq ht) p
  have he := jointFlow_apply q t hq ht.le p
  have hd : poleDifference q t p = (p.2:ℂ)-evolution q t p.1 := by
    change (p.2:ℂ)-jointFlow q t p = _
    rw [he]
  simp only [poissonCurve,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
    ContinuousMap.one_apply,ContinuousMap.star_apply,hi,hd,he,poissonKernel,sub_zero,
    Circle.norm_coe,one_pow]
  simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one]
  rw [normsq_complex,normsq_complex]
  simp only [div_eq_mul_inv,star_inv₀,mul_inv_rev]
  ring


open CauchyPoissonForwardDensity

def referenceFactor (q : ℝ) (hq : |q| < 1) : C(Circle × Circle,ℂ) :=
  ⟨fun p => (((2*Real.pi)⁻¹:ℝ):ℂ) / (circleWeight q p.2:ℂ),by
    apply continuous_const.div
    · exact continuous_ofReal.comp ((circleWeight_continuous q (by simpa using hq)).comp continuous_snd)
    · intro p
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (circleWeight_positive q (by simpa using hq) p.2))⟩

def ratioCurve (q : ℝ) (hq : |q| < 1) (t : ℝ) : C(Circle × Circle,ℂ) :=
  poissonCurve q t * referenceFactor q hq

theorem ratioCurve_smooth (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ContDiffAt ℝ ∞ (ratioCurve q hq) t :=
  (poissonCurve_smooth q t hq ht).mul contDiffAt_const

theorem ratioCurve_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (p : Circle × Circle) :
    ratioCurve q hq t p = (ratio q t p.1 p.2:ℂ) := by
  rw [ratioCurve,ContinuousMap.mul_apply,poissonCurve_apply q t hq ht p]
  change (poissonKernel 0 (evolution q t p.1) p.2:ℂ)*
    ((((2*Real.pi)⁻¹:ℝ):ℂ)/(circleWeight q p.2:ℂ)) = _
  unfold ratio circleWeight
  push_cast
  ring


theorem integrateKernel_continuous (μ : Measure Circle) [IsProbabilityMeasure μ]
    (F : C(Circle × Circle,ℂ)) : Continuous (fun w => ∫ z, F (z,w) ∂μ) := by
  have hc : Continuous (Function.uncurry (fun w z : Circle => F (z,w))) :=
    Continuous.comp (g := F) (f := fun p : Circle × Circle => (p.2,p.1))
      F.continuous (continuous_snd.prodMk continuous_fst)
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := μ) hc isCompact_univ

def integrateKernel (μ : Measure Circle) [IsProbabilityMeasure μ] :
    C(Circle × Circle,ℂ) →L[ℂ] C(Circle,ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun F => ⟨fun w => ∫ z, F (z,w) ∂μ,integrateKernel_continuous μ F⟩
      map_add' := by
        intro F G
        ext w
        exact integral_add
          ((F.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          ((G.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c F
        ext w
        exact integral_smul c (fun z => F (z,w)) }
    1 (fun F => by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro w
      change ‖∫ z, F (z,w) ∂μ‖ ≤ 1*‖F‖
      simpa using norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall (fun z => F.norm_coe_le_norm (z,w))))

def densityCurve (q : ℝ) (hq : |q| < 1) (μ : Measure Circle) [IsProbabilityMeasure μ]
    (t : ℝ) : C(Circle,ℂ) := integrateKernel μ (ratioCurve q hq t)

theorem densityCurve_smooth (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ContDiffAt ℝ ∞ (densityCurve q hq μ) t :=
  ((integrateKernel μ).restrictScalars ℝ).contDiff.contDiffAt.comp t (ratioCurve_smooth q t hq ht)

theorem densityCurve_apply (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (w : Circle) :
    densityCurve q hq μ t w = (density q t μ w:ℂ) := by
  change (∫ z, ratioCurve q hq t (z,w) ∂μ) = (density q t μ w:ℂ)
  simp_rw [ratioCurve_apply q t hq ht]
  exact Complex.ofRealCLM.integral_comp_comm (ratio_integrable q t hq ht μ w)

theorem densityCurve_hasDerivAt (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    HasDerivAt (densityCurve q hq μ) (deriv (densityCurve q hq μ) t) t :=
  ((densityCurve_smooth q t hq ht μ).differentiableAt (by simp)).hasDerivAt


open CauchyPoissonForwardDual CauchyPoissonGeneratorDomain CauchyPoissonMarkovKernel

theorem density_adjoint_pairing (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) :
    (∫ w, deriv (densityCurve q hq μ) t w * f w ∂invariantLaw q) =
      ∫ w, density q t μ w • g w ∂invariantLaw q := by
  let := invariantLaw_probability q hq
  have hd := ((lawFunctional (invariantLaw q)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((densityCurve_hasDerivAt q t hq ht μ).mul_const f)
  have he : (fun u => ∫ w, f w ∂(kernel q u) ∘ₘ μ) =ᶠ[𝓝 t]
      fun u => lawFunctional (invariantLaw q) (densityCurve q hq μ u * f) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [density_integral_pairing q u hq hu μ f]
    change (∫ w, density q u μ w • f w ∂invariantLaw q) =
      ∫ w, densityCurve q hq μ u w * f w ∂invariantLaw q
    apply integral_congr_ae
    filter_upwards with w
    rw [densityCurve_apply q u hq hu μ w]
    rfl
  have hh := (hd.congr_of_eventuallyEq he).unique (weak_forward_derivative q hq μ f g h t ht)
  change (∫ w, deriv (densityCurve q hq μ) t w * f w ∂invariantLaw q) = _ at hh
  rw [density_integral_pairing q t hq ht μ g] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.CauchyPoissonDensitySmooth
