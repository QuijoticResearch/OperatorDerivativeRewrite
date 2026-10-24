import Foundation.IBMSchwartzHalfHolderHeat
import Foundation.IBMSchwartzNativeJointIto
import Foundation.IBMFoldedHeatPredictable

/-! A genuine finite-energy nonlinear Gaussian-score field in the ORIGINAL
predictable clock domain, with actual scalar native Ito and ambient adjoint
realizations. Terminal reconstruction is NOT presumed from energy alone. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatPredictable
open InfiniteGaussian GaussianTimeProcess BrownianClockWeightedEnergy
open GaussianTimeProductL2 GaussianPredictableFull GaussianHermiteIntegrand
open GaussianHermiteRepresentation GaussianComplexHorizonIto IBMIntrinsicOperators
open IBMSchwartzHalfHolderHeat
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local irreducible] heatScore curve GaussianHalfHolderScore.score

private theorem nnTime_predictable :
    @Measurable (ℝ × SampleSpace) ℝ≥0 (PredictableRealL2.predictable naturalFiltration)
      inferInstance (fun z => z.1.toNNReal) := by
  apply measurable_of_Ioi
  intro a
  have hp : @Measurable (ℝ × SampleSpace) (ℝ≥0 × SampleSpace)
      (PredictableRealL2.predictable naturalFiltration) naturalFiltration.predictable
      PredictableRealL2.toNonnegative := Measurable.of_comap_le le_rfl
  have hs := (measurableSet_predictable_Ioi_prod
    (𝓕 := naturalFiltration) (i := a) MeasurableSet.univ).preimage hp
  have he : (fun z : ℝ × SampleSpace => z.1.toNNReal) ⁻¹' Ioi a =
      PredictableRealL2.toNonnegative ⁻¹' (Ioi a ×ˢ (univ : Set SampleSpace)) := by
    ext z
    simp [PredictableRealL2.toNonnegative]
  rw [he]
  exact hs

def raw (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (z : ℝ × SampleSpace) : GaussianL2 :=
  heatScore g a (sigma z) ((T : ℝ)-z.1)

theorem raw_stronglyMeasurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    StronglyMeasurable (raw g a T) :=
  (heatScore_stronglyMeasurable g a).comp_measurable
    (sigma_measurable.prodMk (measurable_const.sub measurable_fst))

theorem raw_energy_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (z : ℝ × SampleSpace) (hs : z.1 ≤ T) :
    ‖raw g a T z‖^2 ≤ (constant g*GaussianHalfHolderScore.mass)^2*
      ((T : ℝ)-z.1)^(-(1/2 : ℝ)) := by
  rw [Real.rpow_neg (sub_nonneg.mpr hs),← Real.sqrt_eq_rpow]
  exact heatScore_energy_nonneg g a _ _ (sub_nonneg.mpr hs)

theorem raw_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    MemLp (raw g a T) 2 (base T) := by
  have hi : Integrable (fun z : ℝ × SampleSpace =>
      (constant g*GaussianHalfHolderScore.mass)^2*((T : ℝ)-z.1)^(-(1/2 : ℝ))) (base T) := by
    rw [base,PredictableRealL2.horizonMeasure_eq_product]
    have ht : Integrable (fun s => (constant g*GaussianHalfHolderScore.mass)^2*
        ((T : ℝ)-s)^(-(1/2 : ℝ))) (volume.restrict (Ioc 0 (T : ℝ))) := by
      simpa only [IntegrableOn,intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg]
        using energy_envelope_integrable g (T : ℝ)
    simpa only [mul_one] using ht.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : SampleSpace => (1 : ℝ)) gaussianProduct)
  apply (memLp_two_iff_integrable_sq_norm (raw_stronglyMeasurable g a T).aestronglyMeasurable).mpr
  apply hi.mono' ((raw_stronglyMeasurable g a T).norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hz
  change ‖‖raw g a T z‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact raw_energy_bound g a T z hz.1.2

theorem raw_predictable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (raw g a T) (base T) := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  have ht : @Measurable (ℝ × SampleSpace) ℝ (PredictableRealL2.predictable naturalFiltration)
      inferInstance (fun z => (z.1.toNNReal : ℝ)) :=
    NNReal.continuous_coe.measurable.comp nnTime_predictable
  refine ⟨fun z => heatScore g a (b z) ((T : ℝ)-(z.1.toNNReal : ℝ)),
    (heatScore_stronglyMeasurable g a).comp_measurable
      (hb.measurable.prodMk (measurable_const.sub ht)), ?_⟩
  filter_upwards [ae_restrict_of_ae he,
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hb hB hz
  change heatScore g a (sigma z) ((T : ℝ)-z.1) = _
  rw [← hb,hB,indicator_of_mem hz,Real.coe_toNNReal z.1 hz.1.1.le]

def input (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : GaussianSourceClockIto.Domain T :=
  ⟨(raw_memLp g a T).toLp _,(raw_predictable g a T).congr (raw_memLp g a T).coeFn_toLp.symm⟩

theorem input_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (input g a T).val =ᵐ[base T] raw g a T := (raw_memLp g a T).coeFn_toLp

def scalarInput (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :=
  IBMSchwartzNativeJointIto.flatten T (input g a T)

def nativeField (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : FieldSpace :=
  IBMSceneryNativeAdjoint.field T (scalarInput g a T)

def value (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : IBMTimeAveragedObservable.JointL2 :=
  IBMSceneryClockIto.jointIntegral T (scalarInput g a T)

theorem native_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ hi : nativeField g a T ∈ clockDerivative.adjoint.domain,
      clockDerivative.adjoint ⟨nativeField g a T,hi⟩ = value g a T :=
  ⟨IBMSceneryNativeAdjoint.clock_mem T _,IBMSceneryNativeAdjoint.clock_value T _⟩

theorem native_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ X ∂gaussianProduct, (fun Y => value g a T (X,Y)) =ᵐ[gaussianProduct]
      GaussianPredictableHorizon.itoIntegral T
        (IBMSceneryClockIto.sectionPredictable T (scalarInput g a T) X) :=
  IBMSceneryClockIto.joint_sections_native T _

theorem value_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ‖value g a T‖^2 = ∫ z, ‖raw g a T z‖^2 ∂base T := by
  rw [value,(IBMSceneryClockIto.jointIntegral T).norm_map,scalarInput,
    (IBMSchwartzNativeJointIto.flatten T).norm_map]
  change ‖(input g a T).val‖^2 = _
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [input_ae g a T] with z hz
  rw [hz]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatPredictable
