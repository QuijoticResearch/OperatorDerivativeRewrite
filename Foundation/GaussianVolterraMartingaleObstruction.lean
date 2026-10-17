import Foundation.GaussianExponentialMarkovPrediction
import Mathlib.Probability.Martingale.Basic

/-! The actual exponentially weighted Brownian convolution is Markov-predictable
but is not a martingale in its own natural filtration when the rate is positive. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianVolterraMartingaleObstruction
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianExponentialMarkovPrediction GaussianConditionalGraph
open SPDEExponentialForcing SeparableHilbertEmbedding
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def process (rate t : ℝ≥0) : SampleSpace → ℝ := value rate t

theorem process_stronglyMeasurable (rate t : ℝ≥0) : StronglyMeasurable (process rate t) :=
  Lp.stronglyMeasurable _

def history (rate : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural (process rate) (process_stronglyMeasurable rate)

theorem process_adapted (rate : ℝ≥0) : StronglyAdapted (history rate) (process rate) :=
  Filtration.stronglyAdapted_natural (process_stronglyMeasurable rate)

theorem history_eq (rate s : ℝ≥0) : history rate s =
    MeasurableSpace.comap (firstChaosFamily (pastDirections rate s)) inferInstance := by
  rw [history, Filtration.natural_eq_comap]
  rfl

theorem process_condExp (rate s t : ℝ≥0) (hst : s ≤ t) :
    gaussianProduct[process rate t | history rate s] =ᵐ[gaussianProduct]
      fun ω => decay rate s t*process rate s ω := by
  rw [history_eq]
  have h := (conditionalProjection_ae_condExp (pastDirections rate s) (value rate t)).symm
  rw [linear_prediction rate s t hst] at h
  apply h.trans
  filter_upwards [Lp.coeFn_smul (decay rate s t) (value rate s)] with ω hω
  exact hω

theorem value_norm_sq (rate t : ℝ≥0) (hr : 0 < rate) :
    ‖value rate t‖^2 = (1-Real.exp (-2*(rate : ℝ)*(t : ℝ)))/(2*(rate : ℝ)) := by
  rw [value, firstChaosEmbedding.norm_map, direction, (hilbertEmbedding GaussianTimeHilbert.TimeHilbert).norm_map,
    responseVector_energy_exact rate t hr]

theorem prediction_defect_exact (rate s t : ℝ≥0) (hr : 0 < rate) (hst : s ≤ t) :
    ‖conditionalProjection (pastDirections rate s) (value rate t)-value rate s‖^2 =
      (decay rate s t-1)^2*(1-Real.exp (-2*(rate : ℝ)*(s : ℝ)))/(2*(rate : ℝ)) := by
  rw [linear_prediction rate s t hst]
  have he : decay rate s t • value rate s-value rate s = (decay rate s t-1) • value rate s := by
    rw [sub_smul, one_smul]
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, value_norm_sq rate s hr]
  ring

theorem decay_lt_one (rate s t : ℝ≥0) (hr : 0 < rate) (hst : s < t) : decay rate s t < 1 := by
  rw [decay, Real.exp_lt_one_iff]
  have hr' : 0 < (rate : ℝ) := hr
  have hst' : (s : ℝ) < t := hst
  nlinarith

theorem prediction_defect_positive (rate s t : ℝ≥0) (hr : 0 < rate) (hs : 0 < s) (hst : s < t) :
    0 < ‖conditionalProjection (pastDirections rate s) (value rate t)-value rate s‖^2 := by
  rw [prediction_defect_exact rate s t hr hst.le]
  have hd : 0 < (decay rate s t-1)^2 := sq_pos_of_ne_zero (by linarith [decay_lt_one rate s t hr hst])
  have he : Real.exp (-2*(rate : ℝ)*(s : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by
    have hr' : 0 < (rate : ℝ) := hr
    have hs' : 0 < (s : ℝ) := hs
    nlinarith)
  apply div_pos (mul_pos hd (sub_pos.mpr he))
  have hr' : 0 < (rate : ℝ) := hr
  positivity

theorem no_condExp_equality (rate s t : ℝ≥0) (hr : 0 < rate) (hs : 0 < s) (hst : s < t) :
    ¬ gaussianProduct[process rate t | history rate s] =ᵐ[gaussianProduct] process rate s := by
  intro h
  have hp := conditionalProjection_ae_condExp (pastDirections rate s) (value rate t)
  have he : conditionalProjection (pastDirections rate s) (value rate t) = value rate s := by
    apply Lp.ext
    rw [history_eq] at h
    exact hp.trans h
  have hd := prediction_defect_positive rate s t hr hs hst
  rw [he, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hd
  exact lt_irrefl _ hd

theorem not_martingale (rate : ℝ≥0) (hr : 0 < rate) :
    ¬ Martingale (process rate) (history rate) gaussianProduct := by
  intro h
  exact no_condExp_equality rate 1 2 hr (by norm_num) (by norm_num)
    (h.condExp_ae_eq (by norm_num : (1 : ℝ≥0) ≤ 2))

end OperatorDerivativeRewrite.Foundation.GaussianVolterraMartingaleObstruction
