import Foundation.IBMClockOccupationConvolution
import Foundation.BochnerL2Dominated

/-! L2 contraction for the actual positive normalized spatial mollifiers.
The input and output are genuine spatial L2 classes; signs of the input are unrestricted. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PositiveMollifierL2Contraction
open GaussianTimeHilbert IBMMollifier IBMClockOccupationConvolution IBMFoldedTransitionBound

theorem square_integrable (u : TimeHilbert) : Integrable (fun r : ℝ => (u r) ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using (Lp.memLp u).norm.integrable_sq

theorem weighted_integrable (n : ℕ) (x : ℝ) (u : TimeHilbert) :
    Integrable (fun r : ℝ => u r * kernel n (x - r)) := by
  have hi := (Lp.memLp u).integrable_mul (Lp.memLp (profileClass n x))
  apply hi.congr
  filter_upwards [IBMPhysicalDerivativeKernel.translatedClass_coeFn (kernel n)
    (kernel_smooth n).continuous (kernel_compactSupport n) x] with r hr
  change profileClass n x r = kernel n (x - r) at hr
  simp only [Pi.mul_apply, hr]

theorem weighted_square_integrable (n : ℕ) (x : ℝ) (u : TimeHilbert) :
    Integrable (fun r : ℝ => (u r) ^ 2 * kernel n (x - r)) := by
  obtain ⟨M, hM⟩ := (kernel_smooth n).continuous.norm.bddAbove_range_of_hasCompactSupport
    (kernel_compactSupport n).norm
  exact (square_integrable u).mul_bdd
    ((kernel_smooth n).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun r => hM ⟨x - r, rfl⟩)

/-- Weighted variance positivity proves Jensen without adding a probability
space or assuming that the signed input is nonnegative. -/
theorem convolution_square_le (n : ℕ) (x : ℝ) (u : TimeHilbert) :
    (∫ r : ℝ, u r * kernel n (x - r)) ^ 2 ≤ ∫ r : ℝ, (u r) ^ 2 * kernel n (x - r) := by
  let c := ∫ r : ℝ, u r * kernel n (x - r)
  have hs := weighted_square_integrable n x u
  have hl := (weighted_integrable n x u).const_mul (2 * c)
  have hc := (shifted_integrable n x).const_mul (c ^ 2)
  have hn : 0 ≤ ∫ r : ℝ,
      ((u r) ^ 2 * kernel n (x - r) - (2 * c)*(u r * kernel n (x - r))) +
        c ^ 2 * kernel n (x - r) := by
    apply integral_nonneg
    intro r
    change 0 ≤ ((u r) ^ 2 * kernel n (x - r) - (2 * c)*(u r * kernel n (x - r))) +
      c ^ 2 * kernel n (x - r)
    have he : ((u r) ^ 2 * kernel n (x - r) - (2 * c)*(u r * kernel n (x - r))) +
        c ^ 2 * kernel n (x - r) = (u r - c) ^ 2 * kernel n (x - r) := by ring
    rw [he]
    exact mul_nonneg (sq_nonneg _) (kernel_nonneg n _)
  have ha := integral_add (hs.sub hl) hc
  have hd := integral_sub hs hl
  simp only [Pi.sub_apply] at ha hd
  rw [ha, hd, integral_const_mul, integral_const_mul, shifted_mass, mul_one] at hn
  change c ^ 2 ≤ _
  change 0 ≤ (∫ r : ℝ, (u r) ^ 2 * kernel n (x - r)) - (2 * c)*c + c ^ 2 at hn
  nlinarith

theorem reverse_shifted_mass (n : ℕ) (r : ℝ) : (∫ x : ℝ, kernel n (x - r)) = 1 := by
  have he : (fun x : ℝ => kernel n (x - r)) = fun x => kernel n (r - x) :=
    funext fun x => kernel_sub_swap n x r
  rw [he, shifted_mass]

theorem square_product_integrable (n : ℕ) (u : TimeHilbert) :
    Integrable (fun p : ℝ × ℝ => (u p.1) ^ 2 * kernel n (p.2 - p.1)) (volume.prod volume) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => (u p.1) ^ 2 * kernel n (p.2 - p.1)) :=
    (((Lp.stronglyMeasurable u).comp_measurable measurable_fst).pow 2).mul
    ((kernel_smooth n).continuous.stronglyMeasurable.comp_measurable
      (measurable_snd.sub measurable_fst))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun r => by
      change Integrable (fun x : ℝ => (u r) ^ 2 * kernel n (x - r))
      apply ((shifted_integrable n r).const_mul ((u r) ^ 2)).congr
      exact ae_of_all _ fun x => by
        dsimp only
        rw [kernel_sub_swap n r x]
  · have he : (fun r : ℝ => ∫ x : ℝ, ‖(u r) ^ 2 * kernel n (x - r)‖) = fun r => (u r) ^ 2 := by
      funext r
      simp only [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg (u r)) (kernel_nonneg n _)),
        integral_const_mul, reverse_shifted_mass, mul_one]
    change Integrable (fun r : ℝ => ∫ x : ℝ, ‖(u r) ^ 2 * kernel n (x - r)‖)
    rw [he]
    exact square_integrable u

theorem energy_integrable (n : ℕ) (u : TimeHilbert) :
    Integrable (fun x : ℝ => ∫ r : ℝ, (u r) ^ 2 * kernel n (x - r)) :=
  (square_product_integrable n u).integral_prod_right

theorem energy_mass (n : ℕ) (u : TimeHilbert) :
    (∫ x : ℝ, ∫ r : ℝ, (u r) ^ 2 * kernel n (x - r)) = ‖u‖ ^ 2 := by
  have hf : Integrable (Function.uncurry
      (fun r x : ℝ => (u r) ^ 2 * kernel n (x - r))) (volume.prod volume) :=
    square_product_integrable n u
  rw [← integral_integral_swap hf]
  simp only [integral_const_mul, reverse_shifted_mass, mul_one]
  simpa only [Real.norm_eq_abs, sq_abs] using (BochnerL2Dominated.norm_sq_integral u).symm

theorem norm_sq_le (n : ℕ) (u v : TimeHilbert)
    (hv : v =ᵐ[volume] fun x => ∫ r : ℝ, u r * kernel n (x - r)) : ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [BochnerL2Dominated.norm_sq_integral v]
  apply le_trans (integral_mono_ae (Lp.memLp v).norm.integrable_sq (energy_integrable n u) ?_)
    (le_of_eq (energy_mass n u))
  filter_upwards [hv] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]
  exact convolution_square_le n x u

end OperatorDerivativeRewrite.Foundation.PositiveMollifierL2Contraction
