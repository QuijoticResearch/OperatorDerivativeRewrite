import Foundation.FourCubeConditionalResponse
import Foundation.SU2OrderedLinkHessian

/-! A coupling-uniform quadratic boundary budget fails after actual one-link Haar integration.
The remaining31 retained links are fixed1, as in FourCubeConditionalResponse. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeConditionalObstruction
open FourCubeConditionalResponse

def mixedHessian (β z : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => conditionalFreeEnergy β x y z) 0) 0

def limitingSlope (z : ℝ) : ℝ := 4*Real.sin z/radius 0 0 z

theorem mixedHessian_formula (β z : ℝ) :
    mixedHessian β z=4*β*mean (β*radius 0 0 z)/radius 0 0 z*Real.sin z :=
  conditional_mixed_hessian β z

theorem mixedHessian_normalized_limit (z : ℝ) :
    Tendsto (fun β => mixedHessian β z/β) atTop (𝓝 (limitingSlope z)) := by
  have hp : 0<radius 0 0 z := lt_of_lt_of_le (by norm_num) (radius_bounds 0 0 z).1
  have hm : Tendsto (fun β => mean (β*radius 0 0 z)) atTop (𝓝 1) :=
    mean_tendsto_one.comp (tendsto_id.atTop_mul_const hp)
  have hl := hm.const_mul (limitingSlope z)
  simp only [mul_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [mixedHessian_formula]
  unfold limitingSlope
  field_simp
  <;> ring

theorem exists_slope_exceeds_quadratic (C ε : ℝ) (hC : 0≤C) (hε : 0<ε) :
    ∃ z : ℝ, 0<z ∧ z<ε ∧ C*z^2<limitingSlope z := by
  obtain ⟨z,hz,hzε,hzq⟩ := SU2OrderedLinkHessian.correction_exceeds_quadratic
    (5*C/8+1) ε (by positivity) hε
  rw [SU2OrderedLinkHessian.correction_eq] at hzq
  have hs : 0<Real.sin z := by nlinarith [sq_nonneg z]
  have hq : C*z^2<4*Real.sin z/5 := by nlinarith [sq_nonneg z]
  have hp : 0<radius 0 0 z := lt_of_lt_of_le (by norm_num) (radius_bounds 0 0 z).1
  have hr : 4*Real.sin z/5≤limitingSlope z := by
    unfold limitingSlope
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ)<5) hp).mpr
    nlinarith [(radius_bounds 0 0 z).2]
  exact ⟨z,hz,hzε,hq.trans_le hr⟩

/-- Fix any angle with a strict limiting-slope excess. The actual mixed Hessian eventually
exceeds the proposed budget, for any real additive constant. -/
theorem eventually_exceeds_budget (C C₀ z : ℝ) (hz : C*z^2<limitingSlope z) :
    ∀ᶠ β : ℝ in atTop, C*β*z^2+C₀<mixedHessian β z := by
  have hzero : Tendsto (fun β : ℝ => C₀/β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hh := ((mixedHessian_normalized_limit z).sub_const (C*z^2)).sub hzero
  have hp : 0<limitingSlope z-C*z^2-0 := by linarith
  have he := hh.eventually (lt_mem_nhds hp)
  filter_upwards [he,eventually_gt_atTop (0 : ℝ)] with β hβ hb
  have hn : 0<(mixedHessian β z-C*β*z^2-C₀)/β := by
    convert hβ using 1 <;> field_simp <;> ring
  have hm := (div_pos_iff.mp hn)
  rcases hm with hm | hm
  · linarith [hm.1]
  · linarith [hm.2]

theorem exists_arbitrarily_large_budget_violation (C C₀ ε β₀ : ℝ)
    (hC : 0≤C) (hε : 0<ε) :
    ∃ z β : ℝ, 0<z ∧ z<ε ∧ β₀<β ∧ 0<β ∧ C*β*z^2+C₀ < |mixedHessian β z| := by
  obtain ⟨z,hz,hzε,hs⟩ := exists_slope_exceeds_quadratic C ε hC hε
  obtain ⟨β,hβ,hβ₀,hβp⟩ := ((eventually_exceeds_budget C C₀ z hs).and
    ((eventually_gt_atTop β₀).and (eventually_gt_atTop (0 : ℝ)))).exists
  exact ⟨z,β,hz,hzε,hβ₀,hβp,hβ.trans_le (le_abs_self _)⟩

theorem no_uniform_quadratic_budget :
    ¬ ∃ C C₀ ε β₀ : ℝ, 0≤C ∧ 0<ε ∧
      ∀ z β : ℝ, 0<z → z<ε → β₀<β → 0<β →
        |mixedHessian β z|≤C*β*z^2+C₀ := by
  rintro ⟨C,C₀,ε,β₀,hC,hε,hb⟩
  obtain ⟨z,β,hz,hzε,hβ₀,hβp,hv⟩ :=
    exists_arbitrarily_large_budget_violation C C₀ ε β₀ hC hε
  exact (not_lt_of_ge (hb z β hz hzε hβ₀ hβp)) hv


/-- The obstruction also survives the shrinking corridor beta=s^2, z=1/s. -/
theorem eventually_shrinking_lower :
    ∀ᶠ s : ℝ in atTop, s/5≤mixedHessian (s^2) (1/s) := by
  have ha : Tendsto (fun s : ℝ => s^2*radius 0 0 (1/s)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun s : ℝ => 3*s^2)
    · intro s
      nlinarith [(radius_bounds 0 0 (1/s)).1,sq_nonneg s]
    · exact (tendsto_pow_atTop (by decide : (2 : ℕ)≠0)).const_mul_atTop (by norm_num)
  have hm := (mean_tendsto_one.comp ha).eventually
    (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  filter_upwards [hm,eventually_ge_atTop (2 : ℝ)] with s hmean hs
  dsimp only [Function.comp_def] at hmean
  have hp : 0<s := by linarith
  have hz : 0<1/s := one_div_pos.mpr hp
  have hzh : 1/s≤1/2 := (div_le_div_iff₀ hp (by norm_num : (0 : ℝ)<2)).mpr (by linarith)
  have hsq : (1/s)^2≤1 := by nlinarith
  have hcube : (1/s)^3≤1/s := by nlinarith [mul_nonneg hz.le (sub_nonneg.mpr hsq)]
  have hsin : (1/s)/2≤Real.sin (1/s) := by nlinarith [Real.sin_ge_sub_cube hz.le]
  have hsinp : 0≤Real.sin (1/s) := by linarith
  have hrp : 0<radius 0 0 (1/s) := by have := (radius_bounds 0 0 (1/s)).1; linarith
  have hr : 2*s^2/5≤2*s^2/radius 0 0 (1/s) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ)<5) hrp).mpr
    nlinarith [(radius_bounds 0 0 (1/s)).2,sq_nonneg s]
  have hmean' : 2*s^2/radius 0 0 (1/s)≤
      4*s^2*mean (s^2*radius 0 0 (1/s))/radius 0 0 (1/s) := by
    apply (div_le_div_iff_of_pos_right hrp).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hmean.le)]
  rw [mixedHessian_formula]
  calc
    s/5=(2*s^2/5)*((1/s)/2) := by field_simp <;> ring
    _ ≤ (2*s^2/5)*Real.sin (1/s) := mul_le_mul_of_nonneg_left hsin (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hr.trans hmean') hsinp

theorem exists_shrinking_budget_violation (C C₀ ε β₀ : ℝ) (hε : 0<ε) :
    ∃ s : ℝ, 0<s ∧ 1/s<ε ∧ β₀<s^2 ∧
      C*s^2*(1/s)^2+C₀ < |mixedHessian (s^2) (1/s)| := by
  have hz : ∀ᶠ s : ℝ in atTop, 1/s<ε :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hε)
  have hb : ∀ᶠ s : ℝ in atTop, β₀<s^2 :=
    (tendsto_pow_atTop (by decide : (2 : ℕ)≠0)).eventually_gt_atTop β₀
  have he : ∀ᶠ s : ℝ in atTop, 0<s ∧ 1/s<ε ∧ β₀<s^2 ∧
      C*s^2*(1/s)^2+C₀ < |mixedHessian (s^2) (1/s)| := by
    filter_upwards [eventually_shrinking_lower,hz,hb,
      eventually_gt_atTop (max 0 (5*(C+C₀)))] with s hh hsz hsb hlarge
    have hp : 0<s := lt_of_le_of_lt (le_max_left _ _) hlarge
    have hc : C+C₀<s/5 := by have := lt_of_le_of_lt (le_max_right _ _) hlarge; linarith
    have hid : C*s^2*(1/s)^2=C := by field_simp <;> ring
    exact ⟨hp,hsz,hsb,by rw [hid]; exact hc.trans_le (hh.trans (le_abs_self _))⟩
  exact he.exists


theorem mean_abs_le (t : ℝ) : |mean t|≤1 := by
  letI := BoundedExponentialTiltResponse.tiltedMeasure_probability
    QuaternionSU2Representation.law QuaternionSU2Representation.halfTrace
    QuaternionSU2Representation.halfTrace_measurable QuaternionSU2Representation.halfTrace_bound t
  simpa [mean] using
    (norm_integral_le_of_norm_le_const
      (f := QuaternionSU2Representation.halfTrace) (C := (1 : ℝ))
      (μ := BoundedExponentialTiltResponse.tiltedMeasure QuaternionSU2Representation.law
        QuaternionSU2Representation.halfTrace t)
      (Filter.Eventually.of_forall (fun U => by
        simpa only [Real.norm_eq_abs] using QuaternionSU2Representation.halfTrace_bound U)))

/-- A valid linear corridor budget survives; failure of the stronger quadratic budget
is not by itself failure of a Schur-complement estimate. -/
theorem mixedHessian_linear_bound (β z : ℝ) :
    |mixedHessian β z|≤(4/3 : ℝ)*|β| * |z| := by
  have hp : 0<radius 0 0 z := by have := (radius_bounds 0 0 z).1; linarith
  have hm := mean_abs_le (β*radius 0 0 z)
  have hprod : |mean (β*radius 0 0 z)| * |Real.sin z|≤|z| := by
    calc
      _ ≤ 1*|Real.sin z| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using (show |Real.sin z|≤|z| from Real.abs_sin_le_abs)
  have hd : 4*|β|/radius 0 0 z≤4*|β|/3 := by
    apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ)<3)).mpr
    nlinarith [(radius_bounds 0 0 z).1,abs_nonneg β]
  calc
    |mixedHessian β z|=4*|β|/radius 0 0 z*
        (|mean (β*radius 0 0 z)| * |Real.sin z|) := by
      rw [mixedHessian_formula,abs_mul,abs_div,abs_mul,abs_mul,
        abs_of_pos hp]
      norm_num
      <;> ring
    _ ≤ (4*|β|/radius 0 0 z)*|z| := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ (4*|β|/3)*|z| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
    _ = _ := by ring

theorem mixedHessian_zero (β : ℝ) : mixedHessian β 0=0 := by
  rw [mixedHessian_formula,Real.sin_zero,mul_zero]

end OperatorDerivativeRewrite.Foundation.FourCubeConditionalObstruction
