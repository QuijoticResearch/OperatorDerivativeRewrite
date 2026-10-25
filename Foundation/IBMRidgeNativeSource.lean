import Foundation.IBMMixedClockLimit
import Foundation.IBMClockCylinderChain
import Foundation.IBMSchwartzSourceDerivative

/-! Actual bounded Schwartz ridge observables and their original source tests.
The source-2 projection is reused, not postulated for nonlinear cylinders. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRidgeNativeSource
open InfiniteGaussian IBMTimeAveragedObservable IBMRawStepSources
open IBMSchwartzSourceDerivative IBMCorrectionStein IBMShiftedJetMoments
open IBMRawGridSecondChaos IBMRawGridObservableTests IBMQuarticSecondChaos
open GaussianTimeSpaceHermite GaussianNumberSectors IBMScalarSecondProjection
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
variable {d : ℕ}

def coefficient (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (Y : SampleSpace) : CoefficientSpace :=
  ∑ j, c j • clockDirection (τ j) Y

theorem coefficient_stronglyMeasurable (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    StronglyMeasurable (coefficient c τ) := by
  have he : (∑ j, c j • clockDirection (τ j)) = coefficient c τ := by
    funext Y
    simp only [coefficient,Finset.sum_apply,Pi.smul_apply]
  rw [← he]
  exact Finset.stronglyMeasurable_sum Finset.univ
    (fun j _ => (direction_stronglyMeasurable (τ j)).const_smul (c j))

def ridgeSource (g : SchwartzMap ℝ ℝ) (a : ℝ) (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) : ValueSpace :=
  (MemLp.of_bound ((observable_continuous g a 0).comp_stronglyMeasurable
    (coefficient_stronglyMeasurable c τ)).aestronglyMeasurable
      (SchwartzMap.seminorm ℝ 0 0 (jet g 0))
        (ae_of_all _ fun Y => observable_bound g a 0 (coefficient c τ Y))).toLp _

theorem ridgeSource_actual (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    ridgeSource g a c τ =ᵐ[gaussianProduct] fun Y => observable g a 0 (coefficient c τ Y) :=
  MemLp.coeFn_toLp _

theorem coefficient_embedding (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (Y : SampleSpace) :
    firstChaosEmbedding (coefficient c τ Y) =
      ∑ j, c j • IBMRandomTimeHilbert.randomSourceClass (τ j) Y := by
  simp only [coefficient,map_sum,map_smul]
  rfl

theorem embedding_actual (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, firstChaosEmbedding (coefficient c τ Y) =ᵐ[gaussianProduct]
      fun X => IBMClockCylinderChain.actualValue c τ (X,Y) := by
  filter_upwards [ae_all_iff.mpr fun j => IBMUnmollifiedSourceDerivative.actual_section_ae (τ j)]
    with Y hy
  rw [coefficient_embedding]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j =>
      c j • IBMRandomTimeHilbert.randomSourceClass (τ j) Y),
    ae_all_iff.mpr fun j => Lp.coeFn_smul (c j) (IBMRandomTimeHilbert.randomSourceClass (τ j) Y),
    ae_all_iff.mpr fun j => (hy j).symm] with X hs hm ha
  rw [hs]
  simp only [IBMClockCylinderChain.actualValue,hm,Pi.smul_apply,smul_eq_mul,ha]

theorem ridge_actual (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    jointRealization (ridgeSource g a c τ) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => g (a+IBMClockCylinderChain.actualValue c τ p) := by
  have hm : Measurable (IBMClockCylinderChain.actualValue c τ) := by
    unfold IBMClockCylinderChain.actualValue
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.mul
      (IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))
  apply jointRealization_ae_of_sections _ _ (g.continuous.measurable.comp (measurable_const.add hm))
  filter_upwards [ridgeSource_actual g a c τ,embedding_actual c τ] with Y hr he
  rw [hr]
  filter_upwards [observable_coeFn g a 0 (coefficient c τ Y),he] with X ho hx
  rw [ho,hx]
  rfl

theorem ridge_intrinsic (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) : jointRealization (ridgeSource g a c τ) ∈ IntrinsicSpace := by
  apply IBMIntrinsicChainRule.composition_observable
    ⟨IBMClockCylinderChain.value c τ,IBMClockCylinderChain.value_intrinsic c τ⟩ _
    (fun x => g (a+x)) (g.continuous.comp (continuous_const.add continuous_id))
  filter_upwards [ridge_actual g a c τ,IBMClockCylinderChain.value_actual_ae c τ] with p hr hv
  rw [hr,hv]

def ridgeObservation (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) : IntrinsicSpace :=
  ⟨jointRealization (ridgeSource g a c τ),ridge_intrinsic g a c τ⟩

def curvature (g : SchwartzMap ℝ ℝ) (a : ℝ) (c : Fin d → ℝ) (τ : Fin d → ℝ≥0)
    (Y : SampleSpace) : ℝ :=
  inner ℝ (gaussianOne:GaussianL2) (observable g a 2 (coefficient c τ Y))

theorem curvature_actual (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (Y : SampleSpace) :
    curvature g a c τ Y = M g a (coefficient c τ Y) 2 0 := by
  rw [curvature,L2_inner_eq_integral,moment_zero]
  apply integral_congr_ae
  filter_upwards [gaussianOne_coeFn,observable_coeFn g a 2 (coefficient c τ Y)] with X h1 ho
  simp only [h1,ho,Real.inner_apply,mul_one,one_mul]

theorem curvature_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) : Measurable (curvature g a c τ) :=
  ((innerSL ℝ (gaussianOne:GaussianL2)).continuous.comp_stronglyMeasurable
    ((observable_continuous g a 2).comp_stronglyMeasurable
      (coefficient_stronglyMeasurable c τ))).measurable

theorem curvature_bound (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (Y : SampleSpace) :
    ‖curvature g a c τ Y‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 2) := by
  have h1 : ‖(gaussianOne:GaussianL2)‖ = 1 := by
    have he := GaussianDeterministicGraphCore.gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg (gaussianOne:GaussianL2)]
  exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by
    rw [h1,one_mul]
    exact observable_bound g a 2 _)

theorem source_ridge_test (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : ℕ → CoefficientSpace) (n : ℕ) (k : CoefficientSpace) :
    inner ℝ (sourceSum u n) (observable g a 0 k) =
      (M g a k 2 0/2)*((inner ℝ (u n) k)^2-(inner ℝ (u 0) k)^2-
        ∑ i ∈ Finset.range n, (inner ℝ (u (i+1)) k-inner ℝ (u i) k)^2) := by
  have hp := (sector 2).starProjection_inner_eq_zero (observable g a 0 k)
    (sourceSum u n) (source_mem_sector u n)
  change inner ℝ (observable g a 0 k-projection 2 (observable g a 0 k)) (sourceSum u n) = 0 at hp
  rw [inner_sub_left] at hp
  simp only [real_inner_comm] at hp
  have he := shiftedJet_projection_two g a 0 k
  change projection 2 (observable g a 0 k) = _ at he
  rw [he,inner_smul_right] at hp
  have ht := raw_square_test u n k
  rw [IBMSourceProductBounds.rawProduct_eq_cross,inner_add_right,inner_smul_right,
    source_mean_zero,mul_zero,add_zero,cross_self] at ht
  rw [ht] at hp
  rw [← moment_zero] at hp
  linarith

end OperatorDerivativeRewrite.Foundation.IBMRidgeNativeSource
