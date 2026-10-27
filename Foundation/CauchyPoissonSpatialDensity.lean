import Foundation.CauchyPoissonJumpDomination
/-! Spatial Lipschitz regularity of actual positive-time forward densities,
uniform over initial probability laws, and actual Bregman domination.
No singular-integral identification is assumed. -/
open Complex MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonSpatialDensity
open CauchyPoissonFlow CauchyPoissonForwardDensity CauchyPoissonFeller

theorem squared_distance_lipschitz (v : ℂ) (hv : ‖v‖ ≤ 1) (w u : Circle) :
    |‖(w:ℂ)-v‖^2-‖(u:ℂ)-v‖^2| ≤ 4*‖(w:ℂ)-(u:ℂ)‖ := by
  have hw : ‖(w:ℂ)-v‖ ≤ 2 := (norm_sub_le _ _).trans (by simp only [Circle.norm_coe]; linarith)
  have hu : ‖(u:ℂ)-v‖ ≤ 2 := (norm_sub_le _ _).trans (by simp only [Circle.norm_coe]; linarith)
  have hh := abs_norm_sub_norm_le ((w:ℂ)-v) ((u:ℂ)-v)
  rw [sub_sub_sub_cancel_right] at hh
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [abs_nonneg (‖(w:ℂ)-v‖-‖(u:ℂ)-v‖), norm_nonneg ((w:ℂ)-(u:ℂ))]

theorem ratio_algebra (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (z w : Circle) :
    ratio q t z w = ((1-‖evolution q t z‖^2)/(1-q^2))*
      (‖(w:ℂ)-(q:ℂ)‖^2/‖(w:ℂ)-evolution q t z‖^2) := by
  have hv := evolution_strict_disk q t hq ht z (by simp)
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hd : ‖(w:ℂ)-evolution q t z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
    intro h; rw [← h,Circle.norm_coe] at hv; linarith))
  have he : ‖(w:ℂ)-(q:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
    intro h; have hh := congrArg norm h; simp only [Circle.norm_coe,Complex.norm_real,Real.norm_eq_abs] at hh; linarith))
  simp only [ratio,circleWeight,poissonKernel,sub_zero,Circle.norm_coe,one_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  field_simp

theorem quotient_bound (a b c d ε r : ℝ) (hε : 0 < ε) (hr : 0 ≤ r)
    (hb : ε ≤ b) (hd : ε ≤ d) (hc : 0 ≤ c) (hc4 : c ≤ 4) (hd4 : d ≤ 4)
    (hac : |a-c| ≤ 4*r) (hbd : |b-d| ≤ 4*r) :
    |a/b-c/d| ≤ (32/ε^2)*r := by
  have hb0 : 0 < b := hε.trans_le hb
  have hd0 : 0 < d := hε.trans_le hd
  have hn : |a*d-c*b| ≤ 32*r := by
    have he : a*d-c*b = (a-c)*d+c*(d-b) := by ring
    rw [he]
    have hh := abs_add_le ((a-c)*d) (c*(d-b))
    rw [abs_mul,abs_mul,abs_of_pos hd0,abs_of_nonneg hc,abs_sub_comm d b] at hh
    have h1 := mul_le_mul_of_nonneg_right hac hd0.le
    have h2 := mul_le_mul_of_nonneg_left hbd hc
    nlinarith [mul_le_mul_of_nonneg_left hd4 (show 0 ≤ 4*r by positivity),
      mul_le_mul_of_nonneg_right hc4 (show 0 ≤ 4*r by positivity)]
  rw [div_sub_div _ _ (ne_of_gt hb0) (ne_of_gt hd0),abs_div,
    abs_of_pos (mul_pos hb0 hd0)]
  rw [mul_comm b c]
  have hden : ε^2 ≤ b*d := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hd)]
  calc
    _ ≤ (32*r)/ε^2 := div_le_div₀ (by positivity) hn (sq_pos_of_pos hε) hden
    _ = _ := by ring

theorem uniform_separation (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z w : Circle, ε ≤ ‖(w:ℂ)-evolution q t z‖^2 := by
  let f : Circle × Circle → ℝ := fun p => ‖(p.2:ℂ)-evolution q t p.1‖^2
  have hc : Continuous f := by
    have he : Continuous (fun p : Circle × Circle => evolution q t p.1) :=
      (evolution_circle_continuous q t hq ht.le).comp continuous_fst
    dsimp [f]; fun_prop
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hc.continuousOn
  have hv := evolution_strict_disk q t hq ht p.1 (by simp)
  have hpos : 0 < f p := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro h; rw [← h,Circle.norm_coe] at hv; linarith
  exact ⟨f p,hpos,fun z w => hp (mem_univ (z,w))⟩

theorem ratio_lipschitz (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z w u : Circle,
      |ratio q t z w-ratio q t z u| ≤ L*‖(w:ℂ)-(u:ℂ)‖ := by
  obtain ⟨ε,hε,hsep⟩ := uniform_separation q t hq ht
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  refine ⟨(1/(1-q^2))*(32/ε^2),by positivity,?_⟩
  intro z w u
  have hv := evolution_strict_disk q t hq ht z (by simp)
  have hqnorm : ‖(q:ℂ)‖ ≤ 1 := by simpa using hq.le
  have hcu : ‖(u:ℂ)-(q:ℂ)‖ ≤ 2 := (norm_sub_le _ _).trans (by
    simp only [Circle.norm_coe]; linarith)
  have hdu : ‖(u:ℂ)-evolution q t z‖ ≤ 2 := (norm_sub_le _ _).trans (by
    simp only [Circle.norm_coe]; linarith)
  have hb := quotient_bound (‖(w:ℂ)-(q:ℂ)‖^2) (‖(w:ℂ)-evolution q t z‖^2)
    (‖(u:ℂ)-(q:ℂ)‖^2) (‖(u:ℂ)-evolution q t z‖^2) ε ‖(w:ℂ)-(u:ℂ)‖ hε
    (norm_nonneg _) (hsep z w) (hsep z u) (sq_nonneg _)
    (by nlinarith [norm_nonneg ((u:ℂ)-(q:ℂ))])
    (by nlinarith [norm_nonneg ((u:ℂ)-evolution q t z)])
    (squared_distance_lipschitz q hqnorm w u)
    (squared_distance_lipschitz (evolution q t z) hv.le w u)
  have ha : 0 ≤ (1-‖evolution q t z‖^2)/(1-q^2) := by
    apply div_nonneg _ (by linarith)
    nlinarith [norm_nonneg (evolution q t z)]
  have ha1 : (1-‖evolution q t z‖^2)/(1-q^2) ≤ 1/(1-q^2) :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ‖evolution q t z‖]) (by linarith)
  rw [ratio_algebra q t hq ht z w,ratio_algebra q t hq ht z u,← mul_sub,abs_mul,abs_of_nonneg ha]
  have hh := mul_le_mul_of_nonneg_left hb ha
  have hh1 := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ (32/ε^2)*‖(w:ℂ)-(u:ℂ)‖ by positivity)
  nlinarith [hh,hh1]

theorem density_lipschitz (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (μ : Measure Circle) [IsProbabilityMeasure μ], ∀ w u : Circle,
      |density q t μ w-density q t μ u| ≤ L*‖(w:ℂ)-(u:ℂ)‖ := by
  obtain ⟨L,hL,hl⟩ := ratio_lipschitz q t hq ht
  refine ⟨L,hL,fun μ _ w u => ?_⟩
  unfold density
  rw [← integral_sub (ratio_integrable q t hq ht μ w) (ratio_integrable q t hq ht μ u)]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun z => show ‖ratio q t z w-ratio q t z u‖ ≤ L*‖(w:ℂ)-(u:ℂ)‖ by
      simpa only [Real.norm_eq_abs] using hl z w u))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem density_lower (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : Circle, δ ≤ density q t μ w := by
  obtain ⟨w,_,hw⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
    (density_continuous q t hq ht μ).continuousOn
  exact ⟨density q t μ w,density_positive q t hq ht μ w,fun u => hw (mem_univ u)⟩

theorem actual_bregman_domination (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ z w : Circle,
      h⁻¹ * poissonKernel 0 (evolution q h z) w *
        CauchyPoissonBregmanStep.bregman (density q t μ z) (density q t μ w) ≤ C := by
  obtain ⟨L,hL,hl⟩ := density_lipschitz q t hq ht
  obtain ⟨δ,hδ,hf⟩ := density_lower q t hq ht μ
  exact CauchyPoissonJumpDomination.eventual_bregman_domination q hq
    (density q t μ) δ L hδ hL hf (fun z w => by simpa only [norm_sub_rev] using hl μ z w)
end OperatorDerivativeRewrite.Foundation.CauchyPoissonSpatialDensity
