import Foundation.IBMNonlinearClockField

/-! Uniform energy of the genuine averaged nonlinear clock-field candidates.
All Bochner integrability and product Fubini hypotheses precede the estimate.
Membership in the old closed derivative graph is a separate obligation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockEnergy
open InfiniteGaussian IBMClockOverlapEnergy IBMNonlinearClockField
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def average (n : ℕ) (T : ℝ) : IBMClockAverageCandidate.Target := ∫ t, field n t ∂window T

theorem inner_kernel_integrable (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : ℝ × ℝ => inner ℝ (field n p.1) (field m p.2))
      ((window T).prod (window T)) := by
  have hi := (field_integrable n hT).norm.mul_prod (field_integrable m hT).norm
  apply hi.mono'
    (((field_stronglyMeasurable n).comp_measurable measurable_fst).inner
      ((field_stronglyMeasurable m).comp_measurable measurable_snd)).aestronglyMeasurable
  exact ae_of_all _ fun p => norm_inner_le_norm (field n p.1) (field m p.2)

theorem average_inner (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    inner ℝ (average n T) (average m T) =
      ∫ p : ℝ × ℝ, inner ℝ (field n p.1) (field m p.2) ∂(window T).prod (window T) := by
  rw [average,average,real_inner_comm,← integral_inner (field_integrable n hT),
    integral_prod _ (inner_kernel_integrable n m hT)]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    change inner ℝ (∫ t, field m t ∂window T) (field n s) =
      ∫ t, inner ℝ (field n s) (field m t) ∂window T
    rw [real_inner_comm,← integral_inner (field_integrable m hT)]

theorem window_mass {T : ℝ} (hT : 0 ≤ T) : (window T).real univ = T := by
  simp only [window,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,Real.volume_Ioc,sub_zero]
  exact ENNReal.toReal_ofReal hT

theorem constant_energy_integral {T : ℝ} (hT : 0 ≤ T) :
    (∫ _p : ℝ × ℝ, 4*T ∂(window T).prod (window T)) = 4*T^3 := by
  have hm : ((window T).prod (window T)).real univ = T*T := by
    simpa only [univ_prod_univ,window_mass hT] using
      (measureReal_prod_prod (μ := window T) (ν := window T) univ univ)
  rw [integral_const]
  change ((window T).prod (window T)).real univ*(4*T) = _
  rw [hm]
  ring

/-- The old linear overlap energy plus a finite nonlinear correction, with
NO smoothing-dependent constant and NO independence hypothesis. -/
theorem average_uniform_energy (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖average n T‖^2 ≤ 8*IBMFoldedTransitionBound.peak 1*T^2*Real.sqrt T+4*T^3 := by
  rw [← real_inner_self_eq_norm_sq,average_inner n n hT]
  calc
    _ ≤ ∫ p : ℝ × ℝ, weightedCovariance n n p.1 p.2+4*T
        ∂(window T).prod (window T) := by
      apply integral_mono_ae (inner_kernel_integrable n n hT)
        ((weightedCovariance_integrable n n hT).add (integrable_const (4*T)))
      filter_upwards [window_pair_mem T] with p hp
      have hb := field_inner_bound n n hp.1.1.le hp.2.1.le
      have hm : min p.1 p.2 ≤ T := (min_le_left _ _).trans hp.1.2
      have hi := (le_abs_self (inner ℝ (field n p.1) (field n p.2))).trans hb
      dsimp [weightedCovariance]
      nlinarith
    _ = (∫ p : ℝ × ℝ, weightedCovariance n n p.1 p.2 ∂(window T).prod (window T))+4*T^3 := by
      rw [integral_add (weightedCovariance_integrable n n hT) (integrable_const (4*T)),
        constant_energy_integral hT]
    _ ≤ _ := by linarith [weightedCovariance_integral_bound n n hT]

theorem average_norm_bound (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖average n T‖ ≤ Real.sqrt (8*IBMFoldedTransitionBound.peak 1*T^2*Real.sqrt T+4*T^3) := by
  have hb := average_uniform_energy n hT
  have h0 := (sq_nonneg ‖average n T‖).trans hb
  nlinarith [Real.sq_sqrt h0,Real.sqrt_nonneg
    (8*IBMFoldedTransitionBound.peak 1*T^2*Real.sqrt T+4*T^3)]

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockEnergy
