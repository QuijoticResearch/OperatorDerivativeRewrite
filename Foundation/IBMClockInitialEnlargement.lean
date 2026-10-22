import Foundation.IndependentInitialConditioning
import Foundation.IBMEvenClockProjection
import Foundation.AmbientMartingaleModification

/-! An auxiliary clock filtration with independent scenery known initially.
Ambient null augmentation handles the ACTUAL continuous process versions. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockInitialEnlargement
open InfiniteGaussian IBMConstructedSources
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ibmValue clockPath

def rawEnlargement : Filtration ℝ≥0
    (inferInstance : MeasurableSpace IBMSourceLaws.JointSample) where
  seq t := (inferInstance : MeasurableSpace SampleSpace).prod (GaussianTimeProcess.naturalFiltration t)
  mono' s t h := sup_le_sup le_rfl (MeasurableSpace.comap_mono (GaussianTimeProcess.naturalFiltration.mono h))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono (GaussianTimeProcess.naturalFiltration.le t))

def enlargement := AmbientNullAugmentation.filtration IBMSourceLaws.jointMeasure rawEnlargement

def rawQuadratic (t : ℝ≥0) (ω : IBMSourceLaws.JointSample) : ℝ :=
  GaussianTimeSpaceHermite.value 2 (GaussianTimeProcess.process t ω.2) t

theorem rawQuadratic_martingale :
    Martingale rawQuadratic rawEnlargement IBMSourceLaws.jointMeasure := by
  have hM := GaussianHermiteMartingale.hermite_martingale 2
  refine ⟨?_, ?_⟩
  · intro t
    have hs : @Measurable IBMSourceLaws.JointSample SampleSpace (rawEnlargement t)
        (GaussianTimeProcess.naturalFiltration t) Prod.snd := measurable_snd
    exact (hM.stronglyAdapted t).comp_measurable hs
  · intro s t hst
    exact IndependentInitialConditioning.conditional_snd gaussianProduct gaussianProduct
      (GaussianTimeProcess.naturalFiltration s) (GaussianTimeProcess.naturalFiltration.le s)
      _ _ (hM.integrable t) (hM.integrable s) (hM.stronglyAdapted s) (hM.condExp_ae_eq hst)

def actualQuadratic (t : ℝ≥0) (ω : IBMSourceLaws.JointSample) : ℝ :=
  (clockPath ω.2 t) ^ 2 - t

theorem actualQuadratic_measurable (t : ℝ≥0) : Measurable (actualQuadratic t) :=
  (((ContinuousMap.measurable_eval t).comp (clockPath_measurable.comp measurable_snd)).pow_const 2).sub_const t

theorem actualQuadratic_ae (t : ℝ≥0) :
    actualQuadratic t =ᵐ[IBMSourceLaws.jointMeasure] rawQuadratic t := by
  filter_upwards [(measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (clockPath_coordinate_ae t)] with ω hω
  change (clockPath ω.2 t) ^ 2 - t = GaussianTimeSpaceHermite.value 2 (GaussianTimeProcess.process t ω.2) t
  simp only [Function.comp_def] at hω
  rw [hω, GaussianTimeSpaceHermite.value_two]

theorem actualQuadratic_martingale :
    Martingale actualQuadratic enlargement IBMSourceLaws.jointMeasure :=
  AmbientMartingaleModification.martingale_modification _ _ _ _ rawQuadratic_martingale
    actualQuadratic_measurable actualQuadratic_ae

theorem ibm_raw_aestronglyMeasurable (t : ℝ≥0) :
    AEStronglyMeasurable[rawEnlargement t] (ibmValue t) IBMSourceLaws.jointMeasure := by
  have hs : @Measurable IBMSourceLaws.JointSample SampleSpace (rawEnlargement t)
      (GaussianTimeProcess.naturalFiltration t) Prod.snd := measurable_snd
  have hx : Measurable[rawEnlargement t] (fun ω => sceneryPath ω.1) :=
    sceneryPath_measurable.comp measurable_fst
  have hy : Measurable[rawEnlargement t] (fun ω => |GaussianTimeProcess.process t ω.2|) :=
    continuous_abs.measurable.comp ((GaussianTimeProcess.process_stronglyAdapted t).measurable.comp hs)
  have hm : Measurable[rawEnlargement t]
      (fun ω => sceneryPath ω.1 |GaussianTimeProcess.process t ω.2|) :=
    continuous_eval.measurable.comp (hx.prodMk hy)
  apply hm.stronglyMeasurable.aestronglyMeasurable.congr
  filter_upwards [(measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (clockPath_coordinate_ae t)] with ω hω
  simp only [Function.comp_def] at hω
  change sceneryPath ω.1 |GaussianTimeProcess.process t ω.2| = ibmValue t ω
  rw [ibmValue_eq, hω]

theorem ibm_enlargement_adapted : StronglyAdapted enlargement ibmValue := by
  intro t
  exact (AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable (rawEnlargement t)
    IBMSourceLaws.jointMeasure (IBMNaturalFiltrationObstruction.point_stronglyMeasurable t).measurable
    (ibm_raw_aestronglyMeasurable t)).stronglyMeasurable

theorem natural_le_enlargement (T : ℝ≥0) :
    IBMNaturalFiltrationObstruction.naturalFiltration T ≤ enlargement T := by
  change (⨆ s ≤ T, MeasurableSpace.comap (ibmValue s) inferInstance) ≤ _
  exact iSup₂_le fun s hs => (ibm_enlargement_adapted s).measurable.comap_le.trans (enlargement.mono hs)

end OperatorDerivativeRewrite.Foundation.IBMClockInitialEnlargement
