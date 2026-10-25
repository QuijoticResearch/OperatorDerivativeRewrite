import Foundation.IBMAllSchwartzSourceReconstruction

/-! Literal spatial increment-square kernels tested against bounded
Lipschitz two-variable functions; diagonal replacement has cubic error. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialKernelTesting
open IBMSpatialIncrementKernel

def cellSet (x y : ℝ) : Set ℝ := Ioc (min x y) (max x y)
def cellPair (F : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ z, rectangle (cellSet x y) z*F z ∂(volume.prod volume)

theorem cell_rectangle_integrable (x y : ℝ) :
    Integrable (rectangle (cellSet x y)) (volume.prod volume) := by
  have he : cellSet x y = interval (fun i : ℕ => if i=0 then x else y) 0 := by
    simp [cellSet,interval]
  rw [he]
  exact rectangle_integrable _ _

theorem cell_pair_integrable (F : ℝ × ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ z, ‖F z‖ ≤ C) (x y : ℝ) :
    Integrable (fun z => rectangle (cellSet x y) z*F z) (volume.prod volume) := by
  apply ((cell_rectangle_integrable x y).const_mul C).mono'
    ((measurable_const.indicator (measurableSet_Ioc.prod measurableSet_Ioc)).mul hF).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖rectangle (cellSet x y) z*F z‖ ≤ C*rectangle (cellSet x y) z
    by_cases hz : z ∈ cellSet x y ×ˢ cellSet x y
    · simpa only [rectangle,indicator_of_mem hz,one_mul,mul_one] using hC z
    · simp only [rectangle,indicator_of_notMem hz,zero_mul,norm_zero,mul_zero,le_refl]

theorem cell_area (x y : ℝ) :
    (∫ z, rectangle (cellSet x y) z ∂(volume.prod volume)) = (y-x)^2 := by
  have hm : MeasurableSet (cellSet x y) := measurableSet_Ioc
  rw [rectangle_integral _ hm]
  have he := interval_measure (fun i : ℕ => if i=0 then x else y) 0
  simp only [interval,ite_true,Nat.reduceAdd,one_ne_zero,ite_false] at he
  rw [show cellSet x y = Ioc (min x y) (max x y) from rfl,he,sq_abs]

theorem cell_distance (x y : ℝ) {z : ℝ × ℝ} (hz : z ∈ cellSet x y ×ˢ cellSet x y) :
    dist z (x,x) ≤ |y-x| := by
  have hc (a : ℝ) (ha : a ∈ cellSet x y) : |a-x| ≤ |y-x| := by
    change min x y < a ∧ a ≤ max x y at ha
    rcases le_total x y with h | h
    · rw [min_eq_left h,max_eq_right h] at ha
      rw [abs_of_nonneg (sub_nonneg.mpr h),abs_le]
      constructor <;> linarith [ha.1,ha.2]
    · rw [min_eq_right h,max_eq_left h] at ha
      rw [abs_of_nonpos (sub_nonpos.mpr h),abs_le]
      constructor <;> linarith [ha.1,ha.2]
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le (hc z.1 hz.1) (hc z.2 hz.2)

theorem cell_diagonal_error (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (x y : ℝ) :
    ‖cellPair F x y-F (x,x)*(y-x)^2‖ ≤ (K:ℝ)*|y-x|^3 := by
  have hr := cell_rectangle_integrable x y
  have hi := cell_pair_integrable F hF.continuous.measurable C hC x y
  have hd : Integrable (fun z => rectangle (cellSet x y) z*(F z-F (x,x))) (volume.prod volume) := by
    convert hi.sub (hr.mul_const (F (x,x))) using 1
    funext z
    simp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have he : cellPair F x y-F (x,x)*(y-x)^2 =
      ∫ z, rectangle (cellSet x y) z*(F z-F (x,x)) ∂(volume.prod volume) := by
    rw [show (fun z => rectangle (cellSet x y) z*(F z-F (x,x))) =
      (fun z => rectangle (cellSet x y) z*F z-rectangle (cellSet x y) z*F (x,x)) by funext z; ring]
    rw [integral_sub hi (hr.mul_const _),integral_mul_const,cell_area]
    unfold cellPair
    ring
  rw [he]
  calc
    _ ≤ ∫ z, ‖rectangle (cellSet x y) z*(F z-F (x,x))‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ((K:ℝ)*|y-x|)*rectangle (cellSet x y) z ∂(volume.prod volume) := by
      apply integral_mono hd.norm (hr.const_mul _)
      intro z
      by_cases hz : z ∈ cellSet x y ×ˢ cellSet x y
      · have hf := (hF.norm_sub_le z (x,x)).trans
          (mul_le_mul_of_nonneg_left (cell_distance x y hz) K.coe_nonneg)
        simpa only [rectangle,indicator_of_mem hz,one_mul,mul_one] using hf
      · simp only [rectangle,indicator_of_notMem hz,zero_mul,norm_zero,mul_zero,le_refl]
    _ = _ := by rw [integral_const_mul,cell_area]; rw [← sq_abs (y-x)]; ring

end OperatorDerivativeRewrite.Foundation.IBMSpatialKernelTesting
