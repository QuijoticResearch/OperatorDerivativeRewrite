import Foundation.BoundedExponentialTiltResponse
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An actual four-dimensional Gaussian angular law, with rotational invariance and sphere support.
Identification with normalized surface measure is a separate obligation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter NormedSpace
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianAngularSphere
set_option backward.isDefEq.respectTransparency false

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev gaussian : Measure Space := stdGaussian Space

theorem normalize_measurable : Measurable (NormedSpace.normalize : Space → Space) := by
  exact measurable_norm.inv.smul measurable_id

def angularLaw : Measure Space := gaussian.map NormedSpace.normalize

instance angularLaw_probability : IsProbabilityMeasure angularLaw := by
  unfold angularLaw
  infer_instance

theorem gaussian_zero : gaussian {0} = 0 := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  change (stdGaussian (EuclideanSpace ℝ (Fin 4))) {0} = 0
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have he : (WithLp.toLp 2 : (Fin 4 → ℝ) → Space) ⁻¹' {0} = {0} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, WithLp.toLp_eq_zero]
  rw [he]
  exact measure_singleton _

theorem gaussian_ae_ne_zero : ∀ᵐ x ∂gaussian, x ≠ 0 := by
  rw [ae_iff]
  simpa using gaussian_zero

theorem gaussian_ae_normalize_norm : ∀ᵐ x ∂gaussian, ‖NormedSpace.normalize x‖ = 1 := by
  filter_upwards [gaussian_ae_ne_zero] with x hx
  exact norm_normalize hx

theorem angularLaw_ae_norm : ∀ᵐ x ∂angularLaw, ‖x‖ = 1 := by
  apply (ae_map_iff normalize_measurable.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact gaussian_ae_normalize_norm

theorem normalize_norm_le (x : Space) : ‖NormedSpace.normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_normalize hx).le

def coord (i : Fin 4) (x : Space) : ℝ := NormedSpace.normalize x i

theorem coord_measurable (i : Fin 4) : Measurable (coord i) := by
  exact (PiLp.continuous_apply 2 _ i).measurable.comp normalize_measurable

theorem coord_bound (i : Fin 4) (x : Space) : |coord i x| ≤ 1 := by
  change |NormedSpace.normalize x i| ≤ 1
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (NormedSpace.normalize x) i).trans (normalize_norm_le x)

theorem coord_power_integrable (i : Fin 4) (k : ℕ) : Integrable (fun x => coord i x^k) gaussian :=
  BoundedExponentialTiltResponse.bounded_power_integrable gaussian (coord i)
    (coord_measurable i) (coord_bound i) k

theorem normalize_isometry (U : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    NormedSpace.normalize (U x) = U (NormedSpace.normalize x) := by
  simp only [NormedSpace.normalize, U.norm_map, map_smul]

theorem angularLaw_isometry (U : Space ≃ₗᵢ[ℝ] Space) : angularLaw.map U = angularLaw := by
  calc
    angularLaw.map U = gaussian.map (U ∘ NormedSpace.normalize) :=
      Measure.map_map U.continuous.measurable normalize_measurable
    _ = gaussian.map (NormedSpace.normalize ∘ U) := by
      congr 1
      funext x
      exact (normalize_isometry U x).symm
    _ = (gaussian.map U).map NormedSpace.normalize :=
      (Measure.map_map normalize_measurable U.continuous.measurable).symm
    _ = angularLaw := by rw [stdGaussian_map]; rfl

theorem gaussian_integral_isometry (U : Space ≃ₗᵢ[ℝ] Space) (f : Space → ℝ)
    (hf : Measurable f) : (∫ x, f (U x) ∂gaussian) = ∫ x, f x ∂gaussian := by
  have he := integral_map (μ := gaussian) U.continuous.measurable.aemeasurable hf.aestronglyMeasurable
  rw [stdGaussian_map] at he
  exact he.symm

theorem coord_neg (i : Fin 4) (x : Space) : coord i (-x) = -coord i x := by
  simp [coord, normalize_neg]

theorem coord_odd_moment (i : Fin 4) (k : ℕ) :
    (∫ x, coord i x^(2*k+1) ∂gaussian) = 0 := by
  have he := gaussian_integral_isometry (LinearIsometryEquiv.neg ℝ)
    (fun x => coord i x^(2*k+1)) ((coord_measurable i).pow_const _)
  have hpow : ∀ a : ℝ, (-a)^(2*k+1) = -a^(2*k+1) :=
    Odd.neg_pow ⟨k, by omega⟩
  simp only [LinearIsometryEquiv.coe_neg, coord_neg, hpow, integral_neg] at he
  linarith

def permutation (e : Fin 4 ≃ Fin 4) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

theorem coord_permutation (e : Fin 4 ≃ Fin 4) (i : Fin 4) (x : Space) :
    coord i (permutation e x) = coord (e.symm i) x := by
  rw [coord, normalize_isometry]
  rfl

theorem coord_moment_equal (i j : Fin 4) (k : ℕ) :
    (∫ x, coord i x^k ∂gaussian) = ∫ x, coord j x^k ∂gaussian := by
  have he := gaussian_integral_isometry (permutation (Equiv.swap i j))
    (fun x => coord i x^k) ((coord_measurable i).pow_const k)
  simpa only [coord_permutation, Equiv.symm_swap, Equiv.swap_apply_left] using he.symm

theorem coord_square_sum_ae : ∀ᵐ x ∂gaussian, ∑ i : Fin 4, coord i x^2 = 1 := by
  filter_upwards [gaussian_ae_normalize_norm] with x hx
  change ∑ i : Fin 4, (NormedSpace.normalize x i)^2 = 1
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

theorem coord_second_moment (i : Fin 4) : (∫ x, coord i x^2 ∂gaussian) = 1/4 := by
  have he : (∑ j : Fin 4, ∫ x, coord j x^2 ∂gaussian) = 1 := by
    rw [← integral_finsetSum _ (fun j _ => coord_power_integrable j 2)]
    calc
      _ = ∫ _ : Space, (1 : ℝ) ∂gaussian := integral_congr_ae coord_square_sum_ae
      _ = 1 := by simp
  have hsame : (∑ j : Fin 4, ∫ x, coord j x^2 ∂gaussian) =
      ∑ _ : Fin 4, ∫ x, coord i x^2 ∂gaussian := by
    apply Finset.sum_congr rfl
    intro j _
    exact coord_moment_equal j i 2
  rw [hsame] at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at he
  linarith

def halfRoot : ℝ := 1 / Real.sqrt 2

theorem halfRoot_sq : halfRoot^2 = 1/2 := by
  unfold halfRoot
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def mixLinear : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 ![halfRoot*(x 0+x 1), halfRoot*(x 0-x 1), x 2, x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem mixLinear_norm (x : Space) : ‖mixLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have he : (halfRoot*(x 0+x 1))^2+(halfRoot*(x 0-x 1))^2 = (x 0)^2+(x 1)^2 := by
    calc
      _ = 2*halfRoot^2*((x 0)^2+(x 1)^2) := by ring
      _ = _ := by rw [halfRoot_sq]; ring
  convert congrArg (fun z => z+(x 2)^2+(x 3)^2) he using 1 <;>
    simp [mixLinear, Fin.sum_univ_succ] <;> ring

def mix : Space ≃ₗᵢ[ℝ] Space :=
  (show Space →ₗᵢ[ℝ] Space from { mixLinear with norm_map' := mixLinear_norm }).toLinearIsometryEquiv rfl

theorem coord_mix_zero (x : Space) :
    coord 0 (mix x) = halfRoot*(coord 0 x+coord 1 x) := by
  rw [coord, normalize_isometry]
  rfl

theorem coord_mix_one (x : Space) :
    coord 1 (mix x) = halfRoot*(coord 0 x-coord 1 x) := by
  rw [coord, normalize_isometry]
  rfl

theorem coord_product_integrable (i j : Fin 4) (k l : ℕ) :
    Integrable (fun x => coord i x^k * coord j x^l) gaussian := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((coord_measurable i).pow_const k).mul ((coord_measurable j).pow_const l)).aestronglyMeasurable
  filter_upwards with x
  change |coord i x^k * coord j x^l| ≤ 1
  rw [abs_mul, abs_pow, abs_pow]
  have hi : |coord i x|^k ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg (coord i x)) (coord_bound i x) k
  have hj : |coord j x|^l ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg (coord j x)) (coord_bound j x) l
  simpa using mul_le_mul hi hj (by positivity) (by norm_num : (0 : ℝ) ≤ 1)

def fourth : ℝ := ∫ x, coord 0 x^4 ∂gaussian
def crossFourth : ℝ := ∫ x, coord 0 x^2 * coord 1 x^2 ∂gaussian

theorem mixed_fourth_equal (j : Fin 4) (hj : j ≠ 0) :
    (∫ x, coord 0 x^2 * coord j x^2 ∂gaussian) = crossFourth := by
  have he := gaussian_integral_isometry (permutation (Equiv.swap 1 j))
    (fun x => coord 0 x^2 * coord 1 x^2)
    (((coord_measurable 0).pow_const 2).mul ((coord_measurable 1).pow_const 2))
  have hzero : (Equiv.swap (1 : Fin 4) j).symm 0 = 0 := by
    simp [Equiv.symm_swap, Equiv.swap_apply_def, hj, Ne.symm hj]
  simp only [coord_permutation] at he
  rw [hzero, Equiv.symm_swap, Equiv.swap_apply_left] at he
  exact he

theorem fourth_cross_identity : fourth + 3*crossFourth = 1/4 := by
  have he : (∫ x, ∑ j : Fin 4, coord 0 x^2 * coord j x^2 ∂gaussian) = 1/4 := by
    calc
      _ = ∫ x, coord 0 x^2 ∂gaussian := by
        apply integral_congr_ae
        filter_upwards [coord_square_sum_ae] with x hx
        rw [← Finset.mul_sum, hx, mul_one]
      _ = _ := coord_second_moment 0
  rw [integral_finsetSum _ (fun j _ => coord_product_integrable 0 j 2 2)] at he
  have hzero : (∫ x, coord 0 x^2 * coord 0 x^2 ∂gaussian) = fourth := by
    congr 1
    funext x
    ring
  simp [Fin.sum_univ_succ] at he
  rw [hzero, mixed_fourth_equal 1 (by decide), mixed_fourth_equal 2 (by decide),
    mixed_fourth_equal 3 (by decide)] at he
  linarith

theorem fourth_triple_cross : fourth = 3*crossFourth := by
  have h0 := gaussian_integral_isometry mix (fun x => coord 0 x^4)
    ((coord_measurable 0).pow_const 4)
  have h1 := gaussian_integral_isometry mix (fun x => coord 1 x^4)
    ((coord_measurable 1).pow_const 4)
  have hsame := coord_moment_equal 1 0 4
  have hp : ∀ x, coord 0 (mix x)^4+coord 1 (mix x)^4 =
      (coord 0 x^4+6*(coord 0 x^2*coord 1 x^2)+coord 1 x^4)/2 := by
    intro x
    rw [coord_mix_zero, coord_mix_one]
    have h4 : halfRoot^4 = 1/4 := by nlinarith [halfRoot_sq]
    calc
      _ = halfRoot^4*((coord 0 x+coord 1 x)^4+(coord 0 x-coord 1 x)^4) := by ring
      _ = _ := by rw [h4]; ring
  have hmix0 : Integrable (fun x => coord 0 (mix x)^4) gaussian := by
    exact Integrable.mono' (integrable_const (1 : ℝ))
      (((coord_measurable 0).comp mix.continuous.measurable).pow_const 4).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_pow, one_pow] using
          pow_le_pow_left₀ (abs_nonneg (coord 0 (mix x))) (coord_bound 0 (mix x)) 4)
  have hmix1 : Integrable (fun x => coord 1 (mix x)^4) gaussian := by
    exact Integrable.mono' (integrable_const (1 : ℝ))
      (((coord_measurable 1).comp mix.continuous.measurable).pow_const 4).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_pow, one_pow] using
          pow_le_pow_left₀ (abs_nonneg (coord 1 (mix x))) (coord_bound 1 (mix x)) 4)
  have he := integral_congr_ae (μ := gaussian) (Eventually.of_forall hp)
  rw [integral_add hmix0 hmix1, h0, h1, hsame] at he
  have hsum : Integrable (fun x => coord 0 x^4+6*(coord 0 x^2*coord 1 x^2)) gaussian :=
    (coord_power_integrable 0 4).add ((coord_product_integrable 0 1 2 2).const_mul 6)
  rw [integral_div, integral_add hsum
    (coord_power_integrable 1 4),
    integral_add (coord_power_integrable 0 4) ((coord_product_integrable 0 1 2 2).const_mul 6),
    integral_const_mul, hsame] at he
  change fourth + fourth = (fourth + 6*crossFourth + fourth)/2 at he
  linarith

theorem coord_fourth_moment (i : Fin 4) : (∫ x, coord i x^4 ∂gaussian) = 1/8 := by
  rw [coord_moment_equal i 0 4]
  change fourth = 1/8
  linarith [fourth_cross_identity, fourth_triple_cross]

theorem crossFourth_value : crossFourth = 1/24 := by
  linarith [fourth_cross_identity, fourth_triple_cross]

theorem angular_coord_eq_ae (i : Fin 4) : ∀ᵐ x ∂angularLaw, coord i x = x i := by
  filter_upwards [angularLaw_ae_norm] with x hx
  rw [coord, normalize_eq_self_of_norm_eq_one hx]

theorem angular_coord_power (i : Fin 4) (k : ℕ) :
    (∫ x, coord i x^k ∂angularLaw) = ∫ x, coord i x^k ∂gaussian := by
  rw [angularLaw, integral_map normalize_measurable.aemeasurable
    ((coord_measurable i).pow_const k).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with x
  simp only [coord, normalize_normalize]

theorem angular_variance_derivative (i : Fin 4) :
    HasDerivAt (BoundedExponentialTiltResponse.variance angularLaw (coord i)
      (fun x => coord i x+coord i x^2)) (1/8) 0 := by
  apply BoundedExponentialTiltResponse.polynomial_variance_hasDerivAt_zero
    angularLaw (coord i) (coord_measurable i) (coord_bound i)
  · simpa only [pow_one] using
      (angular_coord_power i 1).trans (by simpa using coord_odd_moment i 0)
  · rw [angular_coord_power, coord_second_moment]
  · rw [angular_coord_power]
    simpa using coord_odd_moment i 1
  · rw [angular_coord_power, coord_fourth_moment]
  · rw [angular_coord_power]
    simpa using coord_odd_moment i 2

theorem angular_variance_increases (i : Fin 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧
      BoundedExponentialTiltResponse.variance angularLaw (coord i)
        (fun x => coord i x+coord i x^2) 0 <
      BoundedExponentialTiltResponse.variance angularLaw (coord i)
        (fun x => coord i x+coord i x^2) t :=
  BoundedExponentialTiltResponse.positive_derivative_arbitrarily_small_increase _ _
    (angular_variance_derivative i) (by norm_num) ε hε

theorem angular_variance_zero (i : Fin 4) :
    BoundedExponentialTiltResponse.variance angularLaw (coord i)
      (fun x => coord i x+coord i x^2) 0 = 5/16 := by
  have hi := BoundedExponentialTiltResponse.bounded_power_integrable angularLaw (coord i)
    (coord_measurable i) (coord_bound i)
  have hi1 : Integrable (coord i) angularLaw := by simpa using hi 1
  have h1 : (∫ x, coord i x ∂angularLaw) = 0 := by
    simpa only [pow_one] using
      (angular_coord_power i 1).trans (by simpa using coord_odd_moment i 0)
  have h2 : (∫ x, coord i x^2 ∂angularLaw) = 1/4 :=
    (angular_coord_power i 2).trans (coord_second_moment i)
  have h3 : (∫ x, coord i x^3 ∂angularLaw) = 0 :=
    (angular_coord_power i 3).trans (by simpa using coord_odd_moment i 1)
  have h4 : (∫ x, coord i x^4 ∂angularLaw) = 1/8 :=
    (angular_coord_power i 4).trans (coord_fourth_moment i)
  have hf : (∫ x, coord i x+coord i x^2 ∂angularLaw) = 1/4 := by
    rw [integral_add hi1 (hi 2), h1, h2]; norm_num
  have hf2 : (∫ x, (coord i x+coord i x^2)^2 ∂angularLaw) = 3/8 := by
    calc
      _ = ∫ x, (coord i x^2+2*coord i x^3)+coord i x^4 ∂angularLaw := by
        apply integral_congr_ae; filter_upwards with x; ring
      _ = _ := by
        have hs : Integrable (fun x => coord i x^2+2*coord i x^3) angularLaw :=
          (hi 2).add ((hi 3).const_mul 2)
        rw [integral_add hs (hi 4), integral_add (hi 2) ((hi 3).const_mul 2),
          integral_const_mul, h2, h3, h4]
        norm_num
  rw [BoundedExponentialTiltResponse.variance,
    BoundedExponentialTiltResponse.expectation_zero,
    BoundedExponentialTiltResponse.expectation_zero, hf2, hf]
  norm_num

theorem angular_variance_not_antitone (i : Fin 4) :
    ¬ AntitoneOn (BoundedExponentialTiltResponse.variance angularLaw (coord i)
      (fun x => coord i x+coord i x^2)) (Ici 0) := by
  intro hanti
  obtain ⟨t, ht, _, hinc⟩ := angular_variance_increases i 1 (by norm_num)
  have he := hanti (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht.le) ht.le
  exact (not_lt_of_ge he) hinc

end OperatorDerivativeRewrite.Foundation.GaussianAngularSphere
