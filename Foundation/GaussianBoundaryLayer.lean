import Foundation.GaussianBoundaryFluxBound

/-! A shrinking Gaussian cutoff slice prevents uniform decay on the whole corridor. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundaryLayer
set_option backward.isDefEq.respectTransparency false
open CoerciveMovingBoundary GaussianBoundaryFluxBound

theorem normalizer_upper (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r) : normalizer c r ≤ 2*r := by
  have hw : Continuous (weight c) := by unfold weight; fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := -r) (b := r) (by linarith)
    (hw.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun y _ => show weight c y ≤ 1 by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hc (sq_nonneg y)])
  have he : (∫ y in (-r)..r, (1:ℝ))=2*r := by
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  exact hi.trans_eq he

theorem gap_central_lower (c r : ℝ) (hc : 0 ≤ c) (hr : 0 < r) :
    3*r^3*Real.exp (-c*r^2/4)/4 ≤ gap c r := by
  let f : ℝ → ℝ := fun y => (r^2-y^2)*weight c y
  have hf : Continuous f := by unfold f weight; fun_prop
  have hcentral (y : ℝ) (hy : y ∈ Icc (-r/2) (r/2)) :
      (3*r^2/4)*Real.exp (-c*r^2/4) ≤ f y := by
    have hs : 0 ≤ (r/2-y)*(r/2+y) := mul_nonneg (by linarith [hy.2]) (by linarith [hy.1])
    have hsq : 3*r^2/4 ≤ r^2-y^2 := by nlinarith
    exact mul_le_mul hsq (central_weight_lower c r y hc hy) (Real.exp_pos _).le
      (by nlinarith [sq_nonneg r])
  have hi := intervalIntegral.integral_mono_on (μ := volume) (a := -r/2) (b := r/2) (by linarith)
    (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _) hcentral
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc (-r) r)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun y hy => by
      have hp : 0 ≤ (r-y)*(r+y) := mul_nonneg (by linarith [hy.2]) (by linarith [hy.1])
      exact mul_nonneg (by nlinarith : 0 ≤ r^2-y^2) (weight_pos c y).le
  have hs := intervalIntegral.integral_mono_interval (μ := volume) (a := -r/2) (b := r/2)
    (c := -r) (d := r) (by linarith) (by linarith) (by linarith) hpos (hf.intervalIntegrable _ _)
  have he : (∫ y in (-r/2)..(r/2), (3*r^2/4)*Real.exp (-c*r^2/4))=
      3*r^3*Real.exp (-c*r^2/4)/4 := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [he] at hi
  exact (hi.trans hs).trans_eq (gap_integral c r).symm

theorem boundarySlope_lower (c x : ℝ) (hc : 0 ≤ c) (hx : x^2 < 1) :
    3*|x| /8*Real.exp (-5*c*(radius x)^2/4) ≤ |boundarySlope c x| := by
  let r := radius x
  have hr : 0 < r := radius_pos x hx
  have hz := normalizer_pos c r hr
  have hs : (normalizer c r)^2 ≤ (2*r)^2 :=
    (sq_le_sq₀ hz.le (by positivity)).mpr (normalizer_upper c r hc hr)
  have hden := mul_le_mul_of_nonneg_left hs hr.le
  have hn := mul_le_mul_of_nonneg_left (gap_central_lower c r hc hr)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg x)) (weight_pos c r).le)
  rw [boundarySlope_abs c x hx]
  change 3*|x| /8*Real.exp (-5*c*r^2/4) ≤
    2*|x| *weight c r*gap c r/(r*(normalizer c r)^2)
  calc
    _ = (2*|x| *weight c r*(3*r^3*Real.exp (-c*r^2/4)/4))/(r*(2*r)^2) := by
      have he : Real.exp (-5*c*r^2/4)=weight c r*Real.exp (-c*r^2/4) := by
        rw [weight, ← Real.exp_add]
        congr 1
        ring
      rw [he]
      field_simp <;> ring
    _ ≤ (2*|x| *weight c r*(3*r^3*Real.exp (-c*r^2/4)/4))/(r*(normalizer c r)^2) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg x)) (weight_pos c r).le)
          (by positivity)
      · positivity
      · exact hden
    _ ≤ _ := div_le_div_of_nonneg_right hn (by positivity)

def boundaryPoint (c : ℝ) : ℝ := Real.sqrt (1-1/(2*c))

theorem boundaryPoint_properties (c : ℝ) (hc : 1 ≤ c) :
    1/2 ≤ boundaryPoint c ∧ (boundaryPoint c)^2 < 1 ∧ c*(radius (boundaryPoint c))^2=1/2 := by
  have hc0 : 0 < c := by linarith
  have hi : 0 < (1:ℝ)/(2*c) := by positivity
  have hle : (1:ℝ)/(2*c) ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*c)).mpr (by linarith)
  have hx0 : 0 ≤ boundaryPoint c := Real.sqrt_nonneg _
  have hsq : (boundaryPoint c)^2=1-1/(2*c) := Real.sq_sqrt (by linarith)
  have hhalf : 1/2 ≤ boundaryPoint c := (sq_le_sq₀ (by norm_num) hx0).mp (by nlinarith)
  have hx : (boundaryPoint c)^2 < 1 := by linarith
  have hr : (radius (boundaryPoint c))^2=1/(2*c) := by
    rw [radius, Real.sq_sqrt (by linarith : 0 ≤ 1-(boundaryPoint c)^2), hsq]
    ring
  refine ⟨hhalf, hx, ?_⟩
  rw [hr]
  field_simp

def fluxFloor : ℝ := 3*Real.exp (-5/8)/16

theorem fluxFloor_pos : 0 < fluxFloor := by unfold fluxFloor; positivity

theorem persistent_boundarySlope (c : ℝ) (hc : 1 ≤ c) :
    fluxFloor ≤ |boundarySlope c (boundaryPoint c)| := by
  obtain ⟨hh, hx, hr⟩ := boundaryPoint_properties c hc
  have he := boundarySlope_lower c (boundaryPoint c) (by linarith) hx
  have harg : -5*c*(radius (boundaryPoint c))^2/4=(-5/8 : ℝ) := by nlinarith
  rw [harg] at he
  have ha : 1/2 ≤ |boundaryPoint c| := hh.trans (le_abs_self _)
  have hp := mul_le_mul_of_nonneg_right (show 3*(1/2 : ℝ)/8 ≤ 3*|boundaryPoint c| /8 by linarith)
    (Real.exp_pos (-5/8)).le
  have hf : fluxFloor=3*(1/2 : ℝ)/8*Real.exp (-5/8) := by unfold fluxFloor; ring
  rw [← hf] at hp
  exact hp.trans he

theorem persistent_full_derivative (a c : ℝ) (hc : 1 ≤ c) :
    fluxFloor ≤ |deriv (fullSquareMean a c) (boundaryPoint c)| := by
  have hx := (boundaryPoint_properties c hc).2.1
  have he : fullSquareMean a c=corridorMean c := funext (fullSquareMean_eq a c)
  rw [he, (corridorMean_hasDerivAt c (boundaryPoint c) hx).deriv]
  exact persistent_boundarySlope c hc

/-- No concentration threshold makes the whole-ball derivative error uniformly small. -/
theorem no_whole_corridor_decay :
    ¬ ∃ C : ℝ, ∀ c : ℝ, C ≤ c → ∀ x : ℝ, x^2 < 1 →
      |deriv (fullSquareMean c c) x| < fluxFloor := by
  rintro ⟨C, hC⟩
  let c := max 1 C
  have hc : 1 ≤ c := le_max_left _ _
  have hb : C ≤ c := le_max_right _ _
  have he := hC c hb (boundaryPoint c) (boundaryPoint_properties c hc).2.1
  exact (not_lt_of_ge (persistent_full_derivative c c hc)) he

end OperatorDerivativeRewrite.Foundation.GaussianBoundaryLayer
