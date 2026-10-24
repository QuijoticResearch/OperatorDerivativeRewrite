import Foundation.IBMSpatialPredictableSteps

/-! Genuine ordinary spatial parameter-Ito sums of the mollified sign field:
native identity and fourth moments, without a Gaussian-law assumption. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialNativeFourth
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert IBMSpatialPredictableSteps

theorem coefficient_memLp (r : ℕ) (a : ℝ≥0) :
    MemLp (fun Y => IBMSpatialPointClockEnergy.spatial r (process a Y)) 2 gaussianProduct := by
  apply MemLp.of_bound
    ((IBMSpatialPointClockEnergy.spatial_stronglyMeasurable r).comp_measurable
      (process_stronglyAdapted a).measurable |>.mono (naturalFiltration.le a)).aestronglyMeasurable
    ‖IBMPhysicalWhiteNoiseObstruction.profile r‖
  exact Filter.Eventually.of_forall (fun Y =>
    IBMSpatialPointClockEnergy.spatial_bound r (process a Y))

def coefficient (r : ℕ) (a : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  (coefficient_memLp r a).toLp (fun Y => IBMSpatialPointClockEnergy.spatial r (process a Y))

theorem coefficient_ae (r : ℕ) (a : ℝ≥0) : coefficient r a =ᵐ[gaussianProduct]
    fun Y => IBMSpatialPointClockEnergy.spatial r (process a Y) :=
  (coefficient_memLp r a).coeFn_toLp

theorem coefficient_past (r : ℕ) (a : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration a] (coefficient r a) gaussianProduct :=
  (((IBMSpatialPointClockEnergy.spatial_stronglyMeasurable r).comp_measurable
    (process_stronglyAdapted a).measurable).aestronglyMeasurable).congr (coefficient_ae r a).symm

def nativeInput (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (n : ℕ) : Domain T :=
  ∑ j ∈ Finset.range n, input (τ j) (τ (j+1)) T (coefficient r (τ j))
    (coefficient_past r (τ j))

theorem nativeInput_ae (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (n : ℕ) :
    (nativeInput r T τ n).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => ∑ j ∈ Finset.range n,
        (Set.Ioc (τ j : ℝ) (τ (j+1) : ℝ)).indicator
          (fun _ => IBMSpatialPointClockEnergy.spatial r (process (τ j) z.2)) z.1 := by
  have hc := ae_all_iff.mpr (fun j : ℕ =>
    ae_restrict_of_ae (s := PredictableRealL2.horizon T)
    ((Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
        (coefficient_ae r (τ j))))
  filter_upwards [Lp.coeFn_finsetSum (Finset.range n) (fun j =>
    (input (τ j) (τ (j+1)) T (coefficient r (τ j)) (coefficient_past r (τ j))).val),
    ae_all_iff.mpr (fun j : ℕ => input_ae (τ j) (τ (j+1)) T
      (coefficient r (τ j)) (coefficient_past r (τ j))), hc] with z hs hi hc
  simp only [nativeInput, Submodule.coe_sum]
  rw [hs, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hi j]
  by_cases hz : z.1 ∈ Set.Ioc (τ j : ℝ) (τ (j+1) : ℝ)
  · simp only [Set.indicator_of_mem hz]
    exact hc j
  · simp only [Set.indicator_of_notMem hz]

theorem integral_add (T : ℝ≥0) (u v : Domain T) :
    integral T (u+v) = integral T u+integral T v := by
  simp only [IBMSpatialPredictableSteps.integral, map_add]

theorem native_integral_actual (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (n : ℕ) (hend : τ n ≤ T) : integral T (nativeInput r T τ n) =ᵐ[gaussianProduct]
      IBMSpatialFourthSums.sumProcess τ
        (fun j Y => IBMSpatialPointClockEnergy.spatial r (process (τ j) Y)) n := by
  induction n with
  | zero =>
    simp only [nativeInput, Finset.range_zero, Finset.sum_empty,
      IBMSpatialPredictableSteps.integral, map_zero,
      IBMSpatialFourthSums.sumProcess]
    exact Lp.coeFn_zero _ _ _
  | succ n ih =>
    have ih := ih ((hτ (Nat.le_succ n)).trans hend)
    have hs : nativeInput r T τ (n+1) = nativeInput r T τ n+
        input (τ n) (τ (n+1)) T (coefficient r (τ n)) (coefficient_past r (τ n)) := by
      simp only [nativeInput, Finset.sum_range_succ]
    rw [hs, integral_add, integral_input _ _ _ (hτ (Nat.le_succ n)) hend]
    filter_upwards [Lp.coeFn_add (integral T (nativeInput r T τ n))
      (product (τ n) (τ (n+1)) (hτ (Nat.le_succ n))
        (coefficient r (τ n)) (coefficient_past r (τ n))), ih,
      product_ae (τ n) (τ (n+1)) (hτ (Nat.le_succ n))
        (coefficient r (τ n)) (coefficient_past r (τ n)), coefficient_ae r (τ n)]
      with Y ha hi hp hc
    rw [ha]
    simp only [Pi.add_apply]
    rw [hi, hp, hc]
    rfl

theorem native_integral_memLp_four (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (n : ℕ) (hend : τ n ≤ T) :
    MemLp (integral T (nativeInput r T τ n)) 4 gaussianProduct := by
  apply (IBMSpatialFourthSums.partial_memLp τ hτ
    ‖IBMPhysicalWhiteNoiseObstruction.profile r‖ (norm_nonneg _)
    (fun j Y => IBMSpatialPointClockEnergy.spatial r (process (τ j) Y))
    (fun j => (IBMSpatialPointClockEnergy.spatial_stronglyMeasurable r).comp_measurable
      (process_stronglyAdapted (τ j)).measurable)
    (fun j Y => IBMSpatialPointClockEnergy.spatial_bound r (process (τ j) Y)) n).ae_eq
  exact (native_integral_actual r T τ hτ n hend).symm

theorem native_integral_fourth (r : ℕ) (T : ℝ≥0) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (n : ℕ) (hend : τ n ≤ T) :
    (∫ Y, ‖integral T (nativeInput r T τ n) Y‖^4 ∂gaussianProduct) ≤
      3*((τ n : ℝ)-τ 0)^2*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^4 := by
  calc
    _ = ∫ Y, ‖IBMSpatialFourthSums.sumProcess τ
        (fun j Y => IBMSpatialPointClockEnergy.spatial r (process (τ j) Y)) n Y‖^4
          ∂gaussianProduct := integral_congr_ae
      ((native_integral_actual r T τ hτ n hend).fun_comp (fun v => ‖v‖^4))
    _ ≤ _ := IBMSpatialFourthSums.mollifier_partial_fourth r τ hτ n

end OperatorDerivativeRewrite.Foundation.IBMSpatialNativeFourth
