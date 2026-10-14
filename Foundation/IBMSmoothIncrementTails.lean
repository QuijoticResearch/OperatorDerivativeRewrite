import Foundation.IBMSmoothIncrementMoments
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Normed

/-! Probability control of actual mollified scenery increments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementTails
open InfiniteGaussian GaussianHilbertProcess FractionalSpectralKernel
open IBMJointMollifierGaussian IBMSmoothIncrementMoments
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- Markov control at deterministic spatial points, with no pathwise version
assumed. The fourth power event avoids any choice of a sign. -/
theorem convolution_increment_tail {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    {a b C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Set.Icc a b,
      ‖IBMContinuousScenery.wholeLineScenery (deriv ρ) r‖ ≤ C)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    {δ : ℝ} (hδ : 0 < δ) :
    gaussianProduct.real {ω | δ^4 ≤
      (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
        isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4} ≤
      3 * C^4 * |t-s|^4 / δ^4 := by
  apply (le_div_iff₀ (pow_pos hδ 4)).2
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun _ => by positivity)
    (convolution_increment_fourth_integrable ρ s t) (δ^4)).trans
    (convolution_increment_fourth_le hc hρ hC hbound hs ht)

/-- For all three concrete Gaussian derivative fields, a single compact
constant controls every positive threshold and every pair of spatial points. -/
theorem gaussianTriple_compact_tail (n : ℕ) (i : Fin 3) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ∀ δ : ℝ, 0 < δ →
      gaussianProduct.real {ω | δ^4 ≤
        (gaussianTriple n t i ω - gaussianTriple n s i ω)^4} ≤
          3 * C^4 * |t-s|^4 / δ^4 := by
  obtain ⟨C, hC, hbound⟩ := gaussianTriple_compact_increment_bound n i a b
  refine ⟨C, hC, ?_⟩
  intro s hs t ht δ hδ
  apply (le_div_iff₀ (pow_pos hδ 4)).2
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun _ => by positivity)
    (convolution_increment_fourth_integrable (derivativeKernel n i) s t) (δ^4)).trans
    (hbound s hs t ht)

/-- Countably many finite grids admit one full-measure event with eventual
simultaneous increment control, provided their deterministic fourth-moment
budgets are summable. No independence of grid increments is required. -/
theorem gaussianTriple_grid_control (n : ℕ) (i : Fin 3) (a b : ℝ)
    (m : ℕ → ℕ) (s t : (l : ℕ) → Fin (m l) → ℝ)
    (hs : ∀ l k, s l k ∈ Set.Icc a b) (ht : ∀ l k, t l k ∈ Set.Icc a b)
    (h δ : ℕ → ℝ) (hδ : ∀ l, 0 < δ l)
    (hstep : ∀ l k, |t l k - s l k| ≤ h l)
    (hsum : Summable (fun l => (m l : ℝ) * (h l)^4 / (δ l)^4)) :
    ∀ᵐ ω ∂gaussianProduct, ∀ᶠ l in atTop, ∀ k : Fin (m l),
      |gaussianTriple n (t l k) i ω - gaussianTriple n (s l k) i ω| < δ l := by
  classical
  obtain ⟨C, hC, htail⟩ := gaussianTriple_compact_tail n i a b
  let bad : ℕ → Set SampleSpace := fun l => ⋃ k : Fin (m l),
    {ω | (δ l)^4 ≤
      (gaussianTriple n (t l k) i ω - gaussianTriple n (s l k) i ω)^4}
  have hmajor (l : ℕ) : gaussianProduct.real (bad l) ≤
      (3 * C^4) * ((m l : ℝ) * (h l)^4 / (δ l)^4) := by
    calc
      gaussianProduct.real (bad l) ≤ ∑ k : Fin (m l),
          gaussianProduct.real {ω | (δ l)^4 ≤
            (gaussianTriple n (t l k) i ω - gaussianTriple n (s l k) i ω)^4} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin (m l), 3 * C^4 * (h l)^4 / (δ l)^4 := by
        apply Finset.sum_le_sum
        intro k _
        exact (htail (s l k) (hs l k) (t l k) (ht l k) (δ l) (hδ l)).trans
          (by gcongr; exact hstep l k)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  have hreal : Summable (fun l => gaussianProduct.real (bad l)) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
      hmajor (hsum.mul_left (3 * C^4))
  have hfinite : (∑' l, gaussianProduct (bad l)) ≠ ⊤ := by
    convert hreal.tsum_ofReal_ne_top using 1
    congr 1
    funext l
    exact (ENNReal.ofReal_toReal (measure_ne_top gaussianProduct (bad l))).symm
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with l hl
  intro k
  by_contra! hge
  apply hl
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  change (δ l)^4 ≤ _
  calc
    (δ l)^4 ≤ |gaussianTriple n (t l k) i ω -
        gaussianTriple n (s l k) i ω|^4 := pow_le_pow_left₀ (hδ l).le hge 4
    _ = _ := (show Even 4 by decide).pow_abs _

/-- Explicit dyadic skeleton control on every unit interval. On one event of
probability one, every adjacent level-l increment is eventually smaller than
(3/4)^l. This is uniform over all 2^l cells at that level. -/
theorem gaussianTriple_dyadic_control (n : ℕ) (i : Fin 3) (a : ℝ) :
    ∀ᵐ ω ∂gaussianProduct, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |gaussianTriple n (a + ((k.val + 1 : ℕ) : ℝ) / (2:ℝ)^l) i ω -
        gaussianTriple n (a + (k.val : ℝ) / (2:ℝ)^l) i ω| < (3/4:ℝ)^l := by
  have hp (l k : ℕ) (hk : k ≤ 2^l) :
      a + (k : ℝ) / (2:ℝ)^l ∈ Set.Icc a (a+1) := by
    have hpos : (0:ℝ) < 2^l := by positivity
    have hk' : (k : ℝ) ≤ (2:ℝ)^l := by exact_mod_cast hk
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hpos.le)
    · linarith [(div_le_one hpos).2 hk']
  apply gaussianTriple_grid_control n i a (a+1) (fun l => 2^l)
    (fun l k => a + (k.val : ℝ) / (2:ℝ)^l)
    (fun l k => a + ((k.val+1 : ℕ) : ℝ) / (2:ℝ)^l)
    (fun l k => hp l k.val k.isLt.le)
    (fun l k => hp l (k.val+1) (Nat.succ_le_of_lt k.isLt))
    (fun l => (1/2:ℝ)^l) (fun l => (3/4:ℝ)^l) (fun l => by positivity)
  · intro l k
    have he : a + ((k.val+1 : ℕ) : ℝ) / (2:ℝ)^l -
        (a + (k.val : ℝ) / (2:ℝ)^l) = 1 / (2:ℝ)^l := by push_cast; ring
    rw [he, abs_of_pos (by positivity), one_div_pow]
  · have he (l : ℕ) : ((2^l : ℕ) : ℝ) * ((1/2:ℝ)^l)^4 / ((3/4:ℝ)^l)^4 =
        (32/81:ℝ)^l := by
      push_cast
      simp only [← pow_mul, Nat.mul_comm l 4]
      simp only [pow_mul]
      rw [← mul_pow, ← div_pow]
      norm_num
    simp_rw [he]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- One common full-measure event covers every mollifier scale, all three
fields and all integer unit intervals. The eventual level may depend on them. -/
theorem gaussianTriple_common_dyadic_control :
    ∀ᵐ ω ∂gaussianProduct, ∀ (n : ℕ) (i : Fin 3) (z : ℤ),
      ∀ᶠ l in atTop, ∀ k : Fin (2^l),
        |gaussianTriple n ((z:ℝ) + ((k.val+1 : ℕ) : ℝ) / (2:ℝ)^l) i ω -
          gaussianTriple n ((z:ℝ) + (k.val : ℝ) / (2:ℝ)^l) i ω| < (3/4:ℝ)^l := by
  simp only [ae_all_iff]
  intro n i z
  exact gaussianTriple_dyadic_control n i z

end OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementTails

