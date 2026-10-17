import Foundation.HigherHeatPathCylinderAlgebra
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-! Exact position-law variation and the finite signed dyadic path-law obstruction. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPositionVariation
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatKernelScaling HigherHeatKernelMoments
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatPathObstruction

theorem cumulative_zeta (n : ℕ) (i j : Fin n) :
    cumulativeMatrix n i j=IncidenceAlgebra.zeta ℝ j i := rfl

def cumulativeArray (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (cumulativeMatrix n)

theorem cumulative_lower (n : ℕ) : Matrix.IsLowerTriangular (cumulativeArray n) := by
  intro i j h
  change i < j at h
  simp [cumulativeArray,cumulativeMatrix,not_le.mpr h]

theorem cumulative_det (n : ℕ) : Matrix.det (cumulativeArray n)=1 := by
  rw [Matrix.det_of_isLowerTriangular _ (cumulative_lower n)]
  simp [cumulativeArray,cumulativeMatrix]

def cumulativeEquiv (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) (cumulativeArray n) (by rw [cumulative_det]; exact isUnit_one)

set_option backward.isDefEq.respectTransparency false in
theorem cumulativeEquiv_apply (n : ℕ) (x : Fin n → ℝ) :
    cumulativeEquiv n x=linearImage (cumulativeMatrix n) x := by
  change Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) (cumulativeArray n) x = _
  rw [Matrix.toLin_eq_toLin',Matrix.toLin'_apply]
  rfl

def cumulativeMeasEquiv (n : ℕ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (cumulativeEquiv n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem cumulative_embedding (n : ℕ) : MeasurableEmbedding (linearImage (cumulativeMatrix n)) := by
  have he : (cumulativeMeasEquiv n : (Fin n → ℝ) → (Fin n → ℝ))=linearImage (cumulativeMatrix n) :=
    funext (cumulativeEquiv_apply n)
  rw [← he]
  exact (cumulativeMeasEquiv n).measurableEmbedding

theorem position_variation (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j) :
    (positionLaw n m hm t ht).variation =
      (incrementLaw m hm t ht).variation.map (linearImage (cumulativeMatrix n)) := by
  exact (cumulative_embedding n).variation_map

theorem position_variation_mass (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j) :
    ((positionLaw n m hm t ht).variation Set.univ).toReal =
      ∏ j, ∫ x : ℝ, ‖realKernel m hm (t j) (ht j) x‖ := by
  rw [position_variation,Measure.map_apply (linearImage_measurable _) MeasurableSet.univ,
    Set.preimage_univ,incrementLaw_variation_mass]

theorem norm_integral_time_independent (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (∫ x : ℝ, ‖realKernel m hm s hs x‖) = ∫ x : ℝ, ‖realKernel m hm t ht x‖ := by
  let c : ℝ≥0 := (s/t)^((2*m : ℕ)⁻¹ : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : c^(2*m)=s/t := NNReal.rpow_inv_natCast_pow _ (by omega)
  have he : t*c^(2*m)=s := by rw [hp]; field_simp
  have h := norm_integral_scaling m hm t c ht hc
  simpa only [he] using h

theorem dyadic_variation_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ((HigherHeatDyadicLaws.law m hm T hT n).variation Set.univ).toReal =
      (∫ x : ℝ, ‖realKernel m hm T hT x‖)^(gridSize n) := by
  rw [HigherHeatDyadicLaws.law,position_variation_mass]
  simp_rw [norm_integral_time_independent m hm (duration T n) T (duration_pos T hT n) hT]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem level_le_size (n : ℕ) : n ≤ gridSize n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    change n+1 ≤ 2*gridSize n
    have hp := gridSize_pos n
    omega

theorem no_signed_dyadic_marginals {Ω : Type*} [MeasurableSpace Ω]
    (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (μ : SignedMeasure Ω)
    (observation : (n : ℕ) → Ω → Grid n) (hobs : ∀ n, Measurable (observation n))
    (hlaw : ∀ n, μ.map (observation n)=HigherHeatDyadicLaws.law m (by omega) T hT n) : False := by
  let C : ℝ := ∫ x : ℝ, ‖realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := norm_integral_gt_one m hm T hT
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (μ.variation Set.univ).toReal hC
  have hb := variation_mass_map_le μ (observation k) (hobs k)
  rw [hlaw k,dyadic_variation_mass] at hb
  have hp : C^k ≤ C^(gridSize k) := pow_le_pow_right₀ hC.le (level_le_size k)
  exact (not_lt_of_ge (hp.trans hb)) hk

theorem no_signed_continuous_path_marginals (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T)
    (μ : SignedMeasure Path)
    (hlaw : ∀ n, μ.map (sample n)=HigherHeatDyadicLaws.law m (by omega) T hT n) : False :=
  no_signed_dyadic_marginals m hm T hT μ sample (fun n => (sample_continuous n).measurable) hlaw

end OperatorDerivativeRewrite.Foundation.HigherHeatPositionVariation
