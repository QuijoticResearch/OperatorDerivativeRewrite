import Foundation.HigherHeatBackwardSchwartz

/-! Genuine joint time-position continuity and continuous-path lifts of the Schwartz evolution. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzContinuity
open HigherHeatL2 HigherHeatCylinderFourier HigherHeatBackwardSchwartz HigherHeatSchwartzSemigroup

def integrand (m : ℕ) (f : 𝓢(ℝ,ℂ)) (p : ℝ≥0 × ℝ) (ξ : ℝ) : ℂ :=
  𝓕 f ξ*symbol m p.1 ξ*phase (-ξ) p.2

theorem integrand_bound (m : ℕ) (f : 𝓢(ℝ,ℂ)) (p : ℝ≥0 × ℝ) (ξ : ℝ) :
    ‖integrand m f p ξ‖ ≤ ‖𝓕 f ξ‖ := by
  rw [integrand,norm_mul,phase_norm,mul_one,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (symbol_norm_le m p.1 ξ)

theorem integrand_measurable (m : ℕ) (f : 𝓢(ℝ,ℂ)) (p : ℝ≥0 × ℝ) :
    Measurable (integrand m f p) := by
  apply Continuous.measurable
  unfold integrand symbol phase
  fun_prop

theorem integrand_parameter_continuous (m : ℕ) (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    Continuous (fun p : ℝ≥0 × ℝ => integrand m f p ξ) := by
  unfold integrand symbol phase
  fun_prop

theorem evolve_eq_integral (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) (p : ℝ≥0 × ℝ) :
    evolve m hm p.1 f p.2=∫ ξ : ℝ, integrand m f p ξ := by
  rw [← HigherHeatSchwartzCalculus.inverse_phase (evolve m hm p.1 f) p.2]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only
    rw [evolve_fourier]
    unfold integrand
    ring

theorem evolve_joint_continuous (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) :
    Continuous (fun p : ℝ≥0 × ℝ => evolve m hm p.1 f p.2) := by
  have h : Continuous (fun p : ℝ≥0 × ℝ => ∫ ξ : ℝ, integrand m f p ξ) :=
    continuous_of_dominated (fun p => (integrand_measurable m f p).aestronglyMeasurable)
      (fun p => Eventually.of_forall (integrand_bound m f p))
      (𝓕 f).integrable.norm (Eventually.of_forall (integrand_parameter_continuous m f))
  have he : (fun p : ℝ≥0 × ℝ => evolve m hm p.1 f p.2)=
      (fun p : ℝ≥0 × ℝ => ∫ ξ : ℝ, integrand m f p ξ) := by
    funext p
    exact evolve_eq_integral m hm f p
  rw [he]
  exact h

theorem backward_joint_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    Continuous (fun p : ℝ≥0 × ℝ => backward m hm T p.1 f p.2) := by
  exact (evolve_joint_continuous m hm f).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

def pathObservable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (ω : C(ℝ≥0,ℝ)) : C(ℝ≥0,ℂ) :=
  ⟨fun t => backward m hm T t f (ω t),
    (backward_joint_continuous m hm T f).comp (continuous_id.prodMk ω.continuous)⟩

theorem pathObservable_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    Continuous (pathObservable m hm T f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(ℝ≥0,ℝ) × ℝ≥0 => backward m hm T p.2 f (p.1 p.2))
  exact (backward_joint_continuous m hm T f).comp (continuous_snd.prodMk continuous_eval)

theorem pathObservable_measurable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    Measurable (pathObservable m hm T f) := (pathObservable_continuous m hm T f).measurable

theorem pathObservable_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) (ω : C(ℝ≥0,ℝ)) :
    pathObservable m hm T f ω T=f (ω T) := by
  change backward m hm T T f (ω T)=_
  rw [backward_terminal]

theorem pathObservable_initial (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℂ)) (ω : C(ℝ≥0,ℝ)) (hω : ω 0=0) :
    pathObservable m hm T f ω 0=HigherHeatSchwartzCalculus.mean m T f := by
  change backward m hm T 0 f (ω 0)=_
  rw [hω,backward_initial m hm T hT]

theorem pathObservable_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ))
    (ω : C(ℝ≥0,ℝ)) (t : ℝ≥0) :
    ‖pathObservable m hm T f ω t‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := backward_bound m hm T t f (ω t)

theorem mean_continuous (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) :
    Continuous (fun t : ℝ≥0 => HigherHeatSchwartzCalculus.mean m t f) := by
  have he (t : ℝ≥0) : HigherHeatSchwartzCalculus.mean m t f=evolve m hm t f 0 := by
    calc
      _ = ∫ ξ : ℝ, integrand m f (t,0) ξ := by
        simp only [HigherHeatSchwartzCalculus.mean,integrand,
          HigherHeatSchwartzTransition.symbol_even,HigherHeatBackwardFourier.phase_zero,mul_one]
      _ = _ := (evolve_eq_integral m hm f (t,0)).symm
  have heq : (fun t : ℝ≥0 => HigherHeatSchwartzCalculus.mean m t f)=
      (fun t : ℝ≥0 => evolve m hm t f 0) := funext he
  rw [heq]
  exact (evolve_joint_continuous m hm f).comp (continuous_id.prodMk continuous_const)

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzContinuity
