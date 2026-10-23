import Foundation.IBMSimpsonPeano

/-! Joint compact Peano control for time-dependent spatial Simpson sums.
The time parameter is uniform; only C4 in space and joint continuity of
its fourth spatial derivative are used. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.IBMTimeSpacePeano

theorem horizontal_modulus (H : ℝ → ℝ → ℝ)
    (hH : Continuous (fun p : ℝ × ℝ => H p.1 p.2)) (T R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R,
      |y - x| < δ → |H t y-H t x| < ε := by
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod
      (isCompact_Icc : IsCompact (Icc (-R) R))).uniformContinuousOn_of_continuous
        hH.continuousOn) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht x hx y hy hxy
  have h := hu (t, y) ⟨ht, hy⟩ (t, x) ⟨ht, hx⟩ (by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
      max_eq_right (abs_nonneg (y - x))] using hxy)
  simpa only [Real.dist_eq] using h

theorem segment_bounds {R x y z : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R)
    (hz : z ∈ uIcc x y) : z ∈ Icc (-R) R ∧ |z - x| ≤ |y - x| := by
  have hxR := abs_le.mp hx
  have hyR := abs_le.mp hy
  refine ⟨uIcc_subset_Icc hxR hyR hz, ?_⟩
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hz.2]
  · rw [uIcc_of_ge h] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hz.1]

theorem compact_remainder_3 (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 3 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 3 (F p.1) p.2))
    (T R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ x y : ℝ,
      |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |IBMThirdPeano.remainder (F t) x y| ≤ ε * |y - x|^3 := by
  obtain ⟨δ, hδ, hu⟩ := horizontal_modulus
    (fun t x => iteratedDeriv 3 (F t) x) hD T R (6 * ε) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht x y hx hy hxy
  obtain ⟨z,hz,he⟩ := IBMThirdPeano.remainder_lagrange (F t) (hF t) x y
  have hg := segment_bounds hx hy hz
  have ho := hu t ht x (abs_le.mp hx) z hg.1 (hg.2.trans_lt hxy)
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
  have hm := mul_le_mul_of_nonneg_right ho.le (pow_nonneg (abs_nonneg (y - x)) 3)
  nlinarith

theorem compact_remainder_4 (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (T R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ x y : ℝ,
      |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |IBMFourthTaylor.remainder (F t) x y| ≤ ε * |y - x|^4 := by
  obtain ⟨δ, hδ, hu⟩ := horizontal_modulus
    (fun t x => iteratedDeriv 4 (F t) x) hD T R (24 * ε) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht x y hx hy hxy
  obtain ⟨z,hz,he⟩ := IBMFourthPeano.remainder_lagrange (F t) (hF t) x y
  have hg := segment_bounds hx hy hz
  have ho := hu t ht x (abs_le.mp hx) z hg.1 (hg.2.trans_lt hxy)
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
  have hm := mul_le_mul_of_nonneg_right ho.le (pow_nonneg (abs_nonneg (y - x)) 4)
  nlinarith

/-- Simpson error is spatial o(delta^4), uniformly over compact time-space rectangles. -/
theorem compact_error_bound (F : ℝ → ℝ → ℝ)
    (hF : ∀ t, ContDiff ℝ 4 (F t))
    (hD : Continuous (fun p : ℝ × ℝ => iteratedDeriv 4 (F p.1) p.2))
    (T R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ x y : ℝ,
      |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |IBMSimpsonPeano.simpson (deriv (F t)) x y - (F t y-F t x)| ≤ ε * |y - x|^4 := by
  have hg : ∀ t, ContDiff ℝ 3 (deriv (F t)) := fun t => (hF t).deriv'
  have hD3 : Continuous (fun p : ℝ × ℝ => iteratedDeriv 3 (deriv (F p.1)) p.2) := by
    simpa only [← iteratedDeriv_succ'] using hD
  obtain ⟨δ3, hδ3, h3⟩ := compact_remainder_3 (fun t => deriv (F t)) hg hD3 T R
    (ε / 4) (by positivity)
  obtain ⟨δ4, hδ4, h4⟩ := compact_remainder_4 F hF hD T R
    (ε / 4) (by positivity)
  refine ⟨min δ3 δ4, lt_min hδ3 hδ4, ?_⟩
  intro t ht x y hx hy hxy
  have hmR : |(x + y) / 2| ≤ R := by
    rw [abs_div]
    norm_num
    have h := abs_add_le x y
    linarith
  have hmd : |(x + y) / 2 - x| ≤ |y - x| := by
    have he : (x + y) / 2 - x = (y - x) / 2 := by ring
    rw [he, abs_div]
    norm_num
  have hm := h3 t ht x ((x + y) / 2) hx hmR (hmd.trans_lt (hxy.trans_le (min_le_left _ _)))
  have hy3 := h3 t ht x y hx hy (hxy.trans_le (min_le_left _ _))
  have hy4 := h4 t ht x y hx hy (hxy.trans_le (min_le_right _ _))
  have hm' : |IBMThirdPeano.remainder (deriv (F t)) x ((x + y) / 2)| ≤
      (ε / 4) * |y - x|^3 := hm.trans (by gcongr)
  rw [IBMSimpsonPeano.error_identity (F t) (hF t)]
  calc
    |(y - x) / 6 * (4 * IBMThirdPeano.remainder (deriv (F t)) x ((x + y) / 2) +
        IBMThirdPeano.remainder (deriv (F t)) x y) - IBMFourthTaylor.remainder (F t) x y| ≤
        |(y - x) / 6 * (4 * IBMThirdPeano.remainder (deriv (F t)) x ((x + y) / 2) +
          IBMThirdPeano.remainder (deriv (F t)) x y)| + |IBMFourthTaylor.remainder (F t) x y| :=
      abs_sub _ _
    _ ≤ |y - x| / 6 *
        (4 * |IBMThirdPeano.remainder (deriv (F t)) x ((x + y) / 2)| +
          |IBMThirdPeano.remainder (deriv (F t)) x y|) +
        |IBMFourthTaylor.remainder (F t) x y| := by
      rw [abs_mul, abs_div]
      norm_num
      gcongr
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
        abs_add_le (4 * IBMThirdPeano.remainder (deriv (F t)) x ((x + y) / 2))
          (IBMThirdPeano.remainder (deriv (F t)) x y)
    _ ≤ |y - x| / 6 * (4 * ((ε / 4) * |y - x|^3) +
        (ε / 4) * |y - x|^3) + (ε / 4) * |y - x|^4 := by gcongr
    _ ≤ ε * |y - x|^4 := by
      nlinarith [mul_nonneg hε.le (pow_nonneg (abs_nonneg (y - x)) 4)]

end OperatorDerivativeRewrite.Foundation.IBMTimeSpacePeano
