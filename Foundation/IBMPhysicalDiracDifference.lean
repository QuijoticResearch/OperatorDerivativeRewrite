import Foundation.IBMPhysicalNoiseClock

/-! Anchored Dirac differences in the actual physical H^-1 space. The
construction uses the already realized Brownian indicator, not an abstract
coefficient-space negative norm. It does not yet construct a single Dirac. -/
noncomputable section
open MeasureTheory Set TemperedDistribution
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalDiracDifference
open GaussianTimeHilbert IBMPhysicalNoiseVectors IBMPhysicalNoiseClock

theorem vector_pairing (g : ℝ → ℂ) (hg : Continuous g) (r : ℝ) :
    (∫ x, g x * complexify (vector r) x) = ∫ x in 0..r, g x := by
  have he : (fun x => g x * complexify (vector r) x) =ᵐ[volume]
      fun x => (Ioc 0 r).indicator g x-(Ioc r 0).indicator g x := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (vector r),
      Lp.coeFn_sub (intervalVector 0 r) (intervalVector r 0),
      GaussianTimeHilbert.intervalVector_coeFn 0 r,
      GaussianTimeHilbert.intervalVector_coeFn r 0] with x hc hs hp hn
    change complexify (vector r) x = Complex.ofReal (vector r x) at hc
    change vector r x = _ at hs
    rw [hc, hs, Pi.sub_apply, hp, hn]
    by_cases h : x ∈ Ioc 0 r <;> by_cases h' : x ∈ Ioc r 0 <;> simp [h,h']
  rw [integral_congr_ae he,
    integral_sub ((hg.intervalIntegrable 0 r).1.integrable_indicator measurableSet_Ioc)
      ((hg.intervalIntegrable 0 r).2.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

theorem physicalDerivative_vector_toDistr (r : ℝ) :
    (physicalDerivative (vector r)).toDistr = delta (0 : ℝ)-delta r := by
  rw [physicalDerivative_toDistr]
  ext g
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply]
  change (∫ x, (-LineDeriv.lineDerivOp (1 : ℝ) g) x * complexify (vector r) x) = _
  rw [vector_pairing _ (SchwartzMap.continuous _)]
  have he : (fun x => (-LineDeriv.lineDerivOp (1 : ℝ) g) x) = fun x => -deriv g x := by
    funext x
    simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      fderiv_apply_one_eq_deriv]
  rw [he, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => g.differentiableAt.hasDerivAt)
      (((g.smooth 1).deriv' (n := 0)).continuous.intervalIntegrable 0 r)]
  change -(g r-g 0) = g 0-g r
  ring

def difference (r s : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  physicalDerivative (vector s-vector r)

theorem difference_toDistr (r s : ℝ) :
    (difference r s).toDistr = delta r-delta s := by
  change (physicalDerivative (vector s-vector r)).toDistr = _
  rw [map_sub, BesselPotentialSpace.toDistr_sub,
    physicalDerivative_vector_toDistr, physicalDerivative_vector_toDistr]
  abel

theorem difference_bound (r s : ℝ) :
    ‖difference r s‖ ≤ ‖physicalDerivative‖*Real.sqrt |s-r| := by
  have hv : ‖vector s-vector r‖ = Real.sqrt |s-r| := by
    rw [← vector_increment_sq r s, Real.sqrt_sq (norm_nonneg _)]
  exact (physicalDerivative.le_opNorm _).trans_eq (by rw [hv])

theorem difference_continuous : Continuous (fun p : ℝ × ℝ => difference p.1 p.2) :=
  physicalDerivative.continuous.comp
    ((IBMPhysicalNoiseCalculus.vector_continuous.comp continuous_snd).sub
      (IBMPhysicalNoiseCalculus.vector_continuous.comp continuous_fst))

end OperatorDerivativeRewrite.Foundation.IBMPhysicalDiracDifference
