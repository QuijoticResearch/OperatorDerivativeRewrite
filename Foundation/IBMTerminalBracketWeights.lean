import Foundation.GaussianTerminalWeightedBracket

/-! Actual bounded Borel current/terminal weights, including the random-cap
boundary indicators needed for IBM observable bracket tests. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalBracketWeights
open InfiniteGaussian GaussianTimeProcess GaussianConditionalGraph
open GaussianTerminalBracketPrediction GaussianTerminalWeightedBracket
open GaussianBrownianQuadraticVariation

def value (φ : ℝ × ℝ → ℝ) (s T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  φ (process s Y,process T Y)

theorem value_memLp (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (s T : ℝ≥0) : MemLp (value φ s T) 2 gaussianProduct :=
  MemLp.of_bound (hφ.comp ((process_stronglyMeasurable s).measurable.prodMk
    (process_stronglyMeasurable T).measurable)).aestronglyMeasurable M
      (ae_of_all _ fun Y => hM (process s Y,process T Y))

def coefficient (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (s T : ℝ≥0) : GaussianL2 :=
  (value_memLp φ hφ M hM s T).toLp _

theorem coefficient_actual (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (s T : ℝ≥0) :
    coefficient φ hφ M hM s T =ᵐ[gaussianProduct] value φ s T :=
  (value_memLp φ hφ M hM s T).coeFn_toLp

theorem coefficient_generated (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (s T : ℝ≥0) :
    coefficient φ hφ M hM s T ∈ generated (observation s T) := by
  let m := MeasurableSpace.comap (firstChaosFamily (observation s T)) inferInstance
  have hj (i : Option (Iic s)) : Measurable[m]
      (fun Y => firstChaosFamily (observation s T) Y i) :=
    (measurable_pi_apply i).comp (comap_measurable (firstChaosFamily (observation s T)))
  have hv : Measurable[m] (value φ s T) := by
    change Measurable[m] (fun Y => φ
      (firstChaosFamily (observation s T) Y (some ⟨s,by simp⟩),
        firstChaosFamily (observation s T) Y none))
    exact hφ.comp ((hj _).prodMk (hj _))
  exact ⟨value φ s T,hv.stronglyMeasurable,coefficient_actual φ hφ M hM s T⟩

theorem coefficient_norm_le (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (s T : ℝ≥0) : ‖coefficient φ hφ M hM s T‖ ≤ M := by
  have hp : 0 ≤ M := (norm_nonneg (φ (0,0))).trans (hM _)
  apply GaussianBoundedApproximation.gaussian_norm_le hp
  filter_upwards [coefficient_actual φ hφ M hM s T] with Y hY
  rw [hY]
  exact hM _

def error (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) (N : ℕ) : ℝ :=
  meanError T N (fun i => coefficient φ hφ M hM (uniformTime T N i.castSucc) T)

theorem error_actual (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) (N : ℕ) :
    error φ hφ M hM T N = ∫ Y, ∑ i : Fin (N+1),
      ((process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2-
        ((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc))*
          φ (process (uniformTime T N i.castSucc) Y,process T Y) ∂gaussianProduct := by
  rw [error,meanError_actual]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N+1) =>
    coefficient_actual φ hφ M hM (uniformTime T N i.castSucc) T)] with Y hY
  apply Finset.sum_congr rfl
  intro i hi
  rw [hY i]
  rfl

theorem error_bound (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (M : ℝ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    |error φ hφ M hM T N| ≤ 4*M*(T:ℝ)/Real.sqrt (N+1) :=
  meanError_bound T hT N _ (fun i => coefficient_generated φ hφ M hM _ T) M
    ((norm_nonneg (φ (0,0))).trans (hM _)) (fun i => coefficient_norm_le φ hφ M hM _ T)

theorem varying_error_tendsto (φ : ℕ → ℝ × ℝ → ℝ) (hφ : ∀ N, Measurable (φ N))
    (M : ℝ) (hM : ∀ N x, ‖φ N x‖ ≤ M) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => error (φ N) (hφ N) M (hM N) T N) atTop (𝓝 0) :=
  meanError_tendsto T hT _ (fun N i => coefficient_generated (φ N) (hφ N) M (hM N) _ T)
    M ((norm_nonneg (φ 0 (0,0))).trans (hM 0 _))
      (fun N i => coefficient_norm_le (φ N) (hφ N) M (hM N) _ T)

def outerBand (δ : ℝ) (x : ℝ × ℝ) : ℝ := if abs (abs x.1-abs x.2) ≤ δ then 1 else 0

theorem outerBand_measurable (δ : ℝ) : Measurable (outerBand δ) :=
  Measurable.ite (measurableSet_le
    (continuous_abs.measurable.comp ((continuous_abs.measurable.comp measurable_fst).sub
      (continuous_abs.measurable.comp measurable_snd))) measurable_const) measurable_const measurable_const

theorem outerBand_bound (δ : ℝ) (x : ℝ × ℝ) : ‖outerBand δ x‖ ≤ 1 := by
  unfold outerBand
  split_ifs <;> norm_num

theorem outerBand_error_tendsto (δ : ℕ → ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => error (outerBand (δ N)) (outerBand_measurable (δ N)) 1
      (outerBand_bound (δ N)) T N) atTop (𝓝 0) :=
  varying_error_tendsto (fun N => outerBand (δ N)) (fun N => outerBand_measurable (δ N))
    1 (fun N => outerBand_bound (δ N)) T hT

def interior (x : ℝ × ℝ) : ℝ := if abs x.1 < abs x.2 then 1 else 0

theorem interior_measurable : Measurable interior :=
  Measurable.ite (measurableSet_lt (continuous_abs.measurable.comp measurable_fst)
    (continuous_abs.measurable.comp measurable_snd)) measurable_const measurable_const

theorem interior_bound (x : ℝ × ℝ) : ‖interior x‖ ≤ 1 := by
  unfold interior
  split_ifs <;> norm_num

theorem interior_error_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (error interior interior_measurable 1 interior_bound T) atTop (𝓝 0) :=
  varying_error_tendsto (fun _ => interior) (fun _ => interior_measurable)
    1 (fun _ => interior_bound) T hT

end OperatorDerivativeRewrite.Foundation.IBMTerminalBracketWeights
