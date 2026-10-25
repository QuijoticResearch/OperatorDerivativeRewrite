import Foundation.IBMFoldedClockQuadraticVariation
import Foundation.IBMPhysicalNoiseRealization

/-! The actual finite spatial increment-square kernel: mass is folded-clock
quadratic variation, and squared norm is the finite squared interval Gram sum. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialIncrementKernel
open GaussianTimeHilbert IBMPhysicalNoiseVectors

def interval (r : ℕ → ℝ) (i : ℕ) : Set ℝ := Ioc (min (r i) (r (i+1))) (max (r i) (r (i+1)))

def rectangle (s : Set ℝ) (z : ℝ × ℝ) : ℝ := (s ×ˢ s).indicator (fun _ => 1) z

def kernel (r : ℕ → ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, rectangle (interval r i) z

theorem interval_measurable (r : ℕ → ℝ) (i : ℕ) : MeasurableSet (interval r i) := measurableSet_Ioc

theorem interval_finite (r : ℕ → ℝ) (i : ℕ) : volume (interval r i) ≠ ∞ := by
  simp only [interval,Real.volume_Ioc]
  finiteness

theorem rectangle_memLp (r : ℕ → ℝ) (i : ℕ) :
    MemLp (rectangle (interval r i)) 2 (volume.prod volume) :=
  memLp_indicator_const 2 ((interval_measurable r i).prod (interval_measurable r i)) 1
    (Or.inr (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (interval_finite r i) (interval_finite r i)))

theorem kernel_memLp (r : ℕ → ℝ) (n : ℕ) : MemLp (kernel r n) 2 (volume.prod volume) :=
  memLp_finsetSum (Finset.range n) fun i _ => rectangle_memLp r i

theorem rectangle_integrable (r : ℕ → ℝ) (i : ℕ) :
    Integrable (rectangle (interval r i)) (volume.prod volume) := by
  apply (integrableOn_const (μ:=volume.prod volume) (C:=(1:ℝ)) (s:=interval r i ×ˢ interval r i) ?_).integrable_indicator
    ((interval_measurable r i).prod (interval_measurable r i))
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top (interval_finite r i) (interval_finite r i)

theorem kernel_integrable (r : ℕ → ℝ) (n : ℕ) : Integrable (kernel r n) (volume.prod volume) :=
  integrable_finset_sum _ fun i _ => rectangle_integrable r i

theorem rectangle_integral (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ z, rectangle s z ∂(volume.prod volume)) = (volume.real s)^2 := by
  unfold rectangle
  rw [integral_indicator_const 1 (hs.prod hs),smul_eq_mul,mul_one,measureReal_prod_prod,pow_two]

theorem interval_measure (r : ℕ → ℝ) (i : ℕ) :
    volume.real (interval r i) = |r (i+1)-r i| := by
  have he : max (r i) (r (i+1))-min (r i) (r (i+1)) = |r (i+1)-r i| := by
    rcases le_total (r i) (r (i+1)) with h | h
    · simp only [max_eq_right h,min_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    · simp only [max_eq_left h,min_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  rw [interval,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max),he]

theorem kernel_mass (r : ℕ → ℝ) (n : ℕ) :
    (∫ z, kernel r n z ∂(volume.prod volume)) = ∑ i ∈ Finset.range n, (r (i+1)-r i)^2 := by
  unfold kernel
  rw [integral_finset_sum _ (fun i _ => rectangle_integrable r i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rectangle_integral _ (interval_measurable r i),interval_measure,sq_abs]

theorem rectangle_product (s t : Set ℝ) (z : ℝ × ℝ) :
    rectangle s z*rectangle t z = rectangle (s ∩ t) z := by
  unfold rectangle
  rw [← prod_inter_prod]
  by_cases hs : z ∈ s ×ˢ s <;> by_cases ht : z ∈ t ×ˢ t <;> simp [indicator,hs,ht]

theorem kernel_sq_integral (r : ℕ → ℝ) (n : ℕ) :
    (∫ z, (kernel r n z)^2 ∂(volume.prod volume)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (volume.real (interval r i ∩ interval r j))^2 := by
  have he : (fun z => (kernel r n z)^2) = fun z => ∑ i ∈ Finset.range n,
      ∑ j ∈ Finset.range n, rectangle (interval r i ∩ interval r j) z := by
    funext z
    unfold kernel
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum,rectangle_product]
  rw [he]
  have hi (i j : ℕ) : Integrable (rectangle (interval r i ∩ interval r j)) (volume.prod volume) := by
    have hm := (rectangle_memLp r i).integrable_mul (rectangle_memLp r j)
    change Integrable (fun z => rectangle (interval r i) z*rectangle (interval r j) z) (volume.prod volume) at hm
    simpa only [rectangle_product] using hm
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro i himem
  rw [integral_finset_sum _ (fun j _ => hi i j)]
  exact Finset.sum_congr rfl fun j _ => rectangle_integral _ ((interval_measurable r i).inter (interval_measurable r j))

def intervalDirection (r : ℕ → ℝ) (i : ℕ) : TimeHilbert :=
  intervalVector (min (r i) (r (i+1))) (max (r i) (r (i+1)))

theorem increment_vector (r : ℕ → ℝ) (i : ℕ) :
    vector (r (i+1))-vector (r i) =
      if r i ≤ r (i+1) then intervalDirection r i else -intervalDirection r i := by
  split_ifs with h
  · simpa only [intervalDirection,min_eq_left h,max_eq_right h] using vector_sub h
  · have hh := le_of_not_ge h
    have he := vector_sub hh
    simp only [intervalDirection,min_eq_right hh,max_eq_left hh]
    rw [← he]
    abel

theorem increment_gram_sq (r : ℕ → ℝ) (i j : ℕ) :
    (inner ℝ (vector (r (i+1))-vector (r i)) (vector (r (j+1))-vector (r j)))^2 =
      (volume.real (interval r i ∩ interval r j))^2 := by
  rw [increment_vector,increment_vector]
  split_ifs <;> simp only [inner_neg_left,inner_neg_right,neg_neg,neg_sq,intervalDirection,
    intervalVector_inner,interval]

theorem kernel_sq_eq_physical_gram (r : ℕ → ℝ) (n : ℕ) :
    (∫ z, (kernel r n z)^2 ∂(volume.prod volume)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (inner ℝ (vector (r (i+1))-vector (r i)) (vector (r (j+1))-vector (r j)))^2 := by
  rw [kernel_sq_integral]
  simp only [increment_gram_sq]

end OperatorDerivativeRewrite.Foundation.IBMSpatialIncrementKernel
