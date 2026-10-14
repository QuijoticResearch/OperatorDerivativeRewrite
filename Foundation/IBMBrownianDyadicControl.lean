import Foundation.GaussianContinuousModification
import Foundation.GaussianLipschitzIntegrands

/-! Actual Brownian-source dyadic events at the fourth-moment admissible rate
7/8. These are derived from the verified coordinate laws, not path hypotheses. -/
noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.IBMBrownianDyadicControl
open InfiniteGaussian IBMDyadicExtension IBMSourceLaws IBMSourceMoments
open GaussianTimeProcess GaussianHilbertProcess
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem dyadic_control (G : ℝ → SampleSpace → ℝ)
    (hint : ∀ s t, Integrable (fun ω => (G t ω-G s ω)^4) gaussianProduct)
    (hfourth : ∀ s t, (∫ ω, (G t ω-G s ω)^4 ∂gaussianProduct) ≤ 3*|t-s|^2)
    (a : ℝ) :
    ∀ᵐ ω ∂gaussianProduct, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω| < (7/8 : ℝ)^l := by
  classical
  let bad : ℕ → Set SampleSpace := fun l => ⋃ k : Fin (2^l),
    {ω | ((7/8 : ℝ)^l)^4 ≤ (G (grid a l (k.val+1)) ω-G (grid a l k.val) ω)^4}
  have htail (s t : ℝ) (δ : ℝ) (hδ : 0 < δ) :
      gaussianProduct.real {ω | δ^4 ≤ (G t ω-G s ω)^4} ≤ 3*|t-s|^2/δ^4 := by
    apply (le_div_iff₀ (pow_pos hδ 4)).mpr
    rw [mul_comm]
    exact (mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun _ => by positivity) (hint s t) (δ^4)).trans (hfourth s t)
  have hmajor (l : ℕ) : gaussianProduct.real (bad l) ≤ 3*(2048/2401 : ℝ)^l := by
    have he (k : Fin (2^l)) : grid a l (k.val+1)-grid a l k.val = 1/(2 : ℝ)^l := by
      unfold grid; push_cast; ring
    calc
      gaussianProduct.real (bad l) ≤ ∑ k : Fin (2^l),
          gaussianProduct.real {ω | ((7/8 : ℝ)^l)^4 ≤
            (G (grid a l (k.val+1)) ω-G (grid a l k.val) ω)^4} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin (2^l), 3*((1/2 : ℝ)^l)^2 / ((7/8 : ℝ)^l)^4 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [he, abs_of_pos (by positivity : (0 : ℝ) < 1/2^l), one_div_pow] using
          htail (grid a l k.val) (grid a l (k.val+1)) ((7/8 : ℝ)^l) (by positivity)
      _ = 3*(2048/2401 : ℝ)^l := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hp : ((2^l : ℕ) : ℝ)*((1/2 : ℝ)^l)^2 / ((7/8 : ℝ)^l)^4 =
            (2048/2401 : ℝ)^l := by
          push_cast
          simp only [← pow_mul, Nat.mul_comm l 2, Nat.mul_comm l 4]
          simp only [pow_mul]
          rw [← mul_pow, ← div_pow]
          norm_num
        calc
          _ = 3*(((2^l : ℕ) : ℝ)*((1/2 : ℝ)^l)^2 / ((7/8 : ℝ)^l)^4) := by ring
          _ = _ := by rw [hp]
  have hs : Summable (fun l => gaussianProduct.real (bad l)) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hmajor
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2048/2401)
        (by norm_num : (2048/2401 : ℝ) < 1)).mul_left 3)
  have hfinite : (∑' l, gaussianProduct (bad l)) ≠ ⊤ := by
    convert hs.tsum_ofReal_ne_top using 1
    congr 1; funext l
    exact (ENNReal.ofReal_toReal (measure_ne_top gaussianProduct (bad l))).symm
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with l hl k
  by_contra! hge
  apply hl
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  change ((7/8 : ℝ)^l)^4 ≤ _
  calc
    _ ≤ |G (grid a l (k.val+1)) ω-G (grid a l k.val) ω|^4 :=
      pow_le_pow_left₀ (by positivity) hge 4
    _ = _ := (show Even 4 by decide).pow_abs _

theorem scenery_good : ∀ᵐ ω ∂gaussianProduct,
    GaussianContinuousModification.good IBMContinuousScenery.sourceScenery (7/8) ω := by
  have hint (s t : ℝ) : Integrable (fun ω => (sceneryBase t ω-sceneryBase s ω)^4)
      gaussianProduct := by
    have h := ((isonormal_memLp (IBMFiniteScenerySmoothing.direction t) 4 (by norm_num)).sub
      (isonormal_memLp (IBMFiniteScenerySmoothing.direction s) 4 (by norm_num))).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, Pi.sub_apply, (show Even 4 by decide).pow_abs,
      sceneryBase, IBMFiniteScenerySmoothing.direction] using h
  have hall : ∀ᵐ ω ∂gaussianProduct, ∀ z : ℤ, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |sceneryBase (grid z l (k.val+1)) ω-sceneryBase (grid z l k.val) ω| < (7/8 : ℝ)^l := by
    simp only [ae_all_iff]
    intro z
    exact dyadic_control sceneryBase hint (fun s t => (sceneryBase_increment_fourth s t).le) z
  filter_upwards [hall] with ω hω
  intro z
  exact eventually_atTop.mp (hω z)

def clockClass (r : ℝ) : GaussianL2 := wienerL2 (Real.toNNReal r)

theorem clockClass_continuous : Continuous clockClass :=
  GaussianLipschitzIntegrands.wienerL2_continuous.comp continuous_real_toNNReal

theorem clock_increment_fourth (s t : ℝ) :
    (∫ ω, (clockClass t ω-clockClass s ω)^4 ∂gaussianProduct) ≤ 3*|t-s|^2 := by
  have hbase (u v : ℝ≥0) :
      (∫ ω, (process v ω-process u ω)^4 ∂gaussianProduct) = 3*|(v : ℝ)-u|^2 := by
    rcases le_total u v with h | h
    · have h' : (u : ℝ) ≤ v := h
      simpa only [abs_of_nonneg (sub_nonneg.mpr h')] using clockBase_increment_fourth u v h
    · have he : (fun ω => (process v ω-process u ω)^4) =
          fun ω => (process u ω-process v ω)^4 := by funext ω; ring
      rw [he, clockBase_increment_fourth v u h]
      have h' : (v : ℝ) ≤ u := h
      rw [abs_of_nonpos (sub_nonpos.mpr h')]
      ring
  rw [show (fun ω => (clockClass t ω-clockClass s ω)^4) =
      fun ω => (process (Real.toNNReal t) ω-process (Real.toNNReal s) ω)^4 from rfl, hbase]
  have hd : |(Real.toNNReal t : ℝ)-(Real.toNNReal s : ℝ)| ≤ |t-s| := by
    simpa only [NNReal.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
      Real.lipschitzWith_toNNReal.dist_le_mul t s
  gcongr

theorem clock_good : ∀ᵐ ω ∂gaussianProduct,
    GaussianContinuousModification.good clockClass (7/8) ω := by
  have hint (s t : ℝ) : Integrable (fun ω => (clockClass t ω-clockClass s ω)^4)
      gaussianProduct := by
    have h := ((process_memLp (Real.toNNReal t) 4 (by norm_num)).sub
      (process_memLp (Real.toNNReal s) 4 (by norm_num))).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, Pi.sub_apply, (show Even 4 by decide).pow_abs,
      clockClass, process] using h
  have hall : ∀ᵐ ω ∂gaussianProduct, ∀ z : ℤ, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |clockClass (grid z l (k.val+1)) ω-clockClass (grid z l k.val) ω| < (7/8 : ℝ)^l := by
    simp only [ae_all_iff]
    intro z
    exact dyadic_control (fun r => clockClass r) hint clock_increment_fourth z
  filter_upwards [hall] with ω hω
  intro z
  exact eventually_atTop.mp (hω z)

end OperatorDerivativeRewrite.Foundation.IBMBrownianDyadicControl
