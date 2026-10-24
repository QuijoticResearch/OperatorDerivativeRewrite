import Foundation.IBMSchwartzConditionalIncrement
import Foundation.IBMSchwartzHeatPredictable
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Genuine time-clock integrability and step duality for the full-source
nonlinear IBM heat-score field. Fubini follows from its verified L2 energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatTimePairing
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open BrownianClockWeightedEnergy IBMSchwartzHalfHolderHeat IBMSchwartzHeatPredictable
open IBMSchwartzConditionalIncrement
attribute [local irreducible] curve heatScore GaussianHalfHolderScore.score
  GaussianBoundedHeatDerivative.mean

theorem weighted_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (V : GaussianL2) :
    Integrable (fun z : ℝ × SampleSpace => V z.2 • raw g a T z) (base T) := by
  have hV : MemLp (fun z : ℝ × SampleSpace => V z.2) 2 (base T) := by
    rw [base,PredictableRealL2.horizonMeasure_eq_product]
    exact (Lp.memLp V).comp_snd (volume.restrict (Ioc 0 (T : ℝ)))
  have hp := hV.norm.integrable_mul (raw_memLp g a T).norm
  apply hp.mono' (hV.aestronglyMeasurable.smul (raw_stronglyMeasurable g a T).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    change ‖V z.2 • raw g a T z‖ ≤ ‖V z.2‖*‖raw g a T z‖
    rw [norm_smul]

theorem step_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hRT : R ≤ T) (V : GaussianL2) :
    Integrable (fun z : ℝ × SampleSpace => V z.2 • raw g a T z)
      ((volume.restrict (Ioc (S : ℝ) R)).prod gaussianProduct) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  have hi : IntegrableOn (fun z : ℝ × SampleSpace => V z.2 • raw g a T z)
      (PredictableRealL2.horizon T) GaussianTimeProductL2.timeProbability :=
    weighted_integrable g a T V
  apply hi.mono_set
  intro z hz
  exact ⟨⟨lt_of_le_of_lt S.coe_nonneg hz.1.1,
    hz.1.2.trans (show (R : ℝ) ≤ T from hRT)⟩,hz.2⟩

theorem row_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0)
    (s : ℝ) (hSs : (S : ℝ) ≤ s) (hsT : s < T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, V Y • raw g a T (s,Y) ∂gaussianProduct) =
      ∫ Y, V Y • heatScore g a (process S Y) ((T : ℝ)-S) ∂gaussianProduct := by
  have hsn : 0 ≤ s := S.coe_nonneg.trans hSs
  have hS' : S ≤ s.toNNReal := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal s hsn]
    exact hSs
  have hT' : s.toNNReal < T := by
    rw [← NNReal.coe_lt_coe,Real.coe_toNNReal s hsn]
    exact hsT
  have he : (s.toNNReal-S)+(T-s.toNNReal) = T-S := by
    rw [add_comm]
    exact tsub_add_tsub_cancel hT'.le hS'
  calc
    _ = ∫ Y, V Y • heatScore g a (process s.toNNReal Y) ((T : ℝ)-s) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [clockPath_coordinate_ae s.toNNReal] with Y hY
      simp only [raw,sigma,hY]
    _ = _ := by
      have h := weighted_score g a S s.toNNReal (T-s.toNNReal) hS'
        (tsub_pos_iff_lt.mpr hT') V hV
      simpa only [he,NNReal.coe_sub hT'.le,NNReal.coe_sub (hS'.trans hT'.le),
        Real.coe_toNNReal s hsn] using h

theorem time_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R ≤ T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ z : ℝ × SampleSpace, V z.2 • raw g a T z
      ∂((volume.restrict (Ioc (S : ℝ) R)).prod gaussianProduct)) =
      ((R : ℝ)-S) • ∫ Y, V Y • heatScore g a (process S Y) ((T : ℝ)-S)
        ∂gaussianProduct := by
  rw [integral_prod _ (step_integrable g a S R T hRT V)]
  calc
    _ = ∫ _ in Ioc (S : ℝ) R, ∫ Y, V Y • heatScore g a (process S Y) ((T : ℝ)-S)
        ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne (T : ℝ))] with s hs hne
      exact row_pairing g a S T s hs.1.le
        (lt_of_le_of_ne (hs.2.trans (show (R : ℝ) ≤ T from hRT)) hne) V hV
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (show (S : ℝ) ≤ R from hSR))]

theorem step_duality (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R ≤ T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ z : ℝ × SampleSpace, V z.2 • raw g a T z
      ∂((volume.restrict (Ioc (S : ℝ) R)).prod gaussianProduct)) =
      ∫ Y, (V Y*(process R Y-process S Y)) • curve g a (process T Y)
        ∂gaussianProduct := by
  rw [time_pairing g a S R T hSR hRT V hV,
    terminal_step_closed g a S R T hSR hRT V hV,NNReal.coe_sub hSR]

theorem column_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R ≤ T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, (∫ s in Ioc (S : ℝ) R, V Y • raw g a T (s,Y) ∂volume) ∂gaussianProduct) =
      ∫ Y, (V Y*(process R Y-process S Y)) • curve g a (process T Y)
        ∂gaussianProduct := by
  rw [← integral_integral_swap (step_integrable g a S R T hRT V),
    ← integral_prod _ (step_integrable g a S R T hRT V)]
  exact step_duality g a S R T hSR hRT V hV

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatTimePairing
