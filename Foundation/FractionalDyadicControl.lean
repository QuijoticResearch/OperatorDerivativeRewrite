import Foundation.GaussianAbsoluteMoments
import Foundation.DyadicMomentControl
import Foundation.FractionalGaussianProcess

/-! All-H moment estimates for the already constructed fractional Gaussian
family. They prove a dyadic event, rather than assuming continuous paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalDyadicControl
open InfiniteGaussian SeparableHilbertEmbedding FractionalSpectralKernel
open FractionalSpectralGeometry GaussianAbsoluteMoments IBMDyadicExtension
attribute [local instance] spectralSpace_secondCountable
set_option backward.isDefEq.respectTransparency false

variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def direction (r : ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (normalized H hH0 hH1 r)
def value (r : ℝ) : GaussianL2 := firstChaosEmbedding (direction H hH0 hH1 r)

theorem value_continuous : Continuous (value H hH0 hH1) :=
  firstChaosEmbedding.continuous.comp
    ((hilbertEmbedding SpectralSpace).continuous.comp (normalized_continuous H hH0 hH1))

theorem direction_increment_norm (s t : ℝ) :
    ‖direction H hH0 hH1 t-direction H hH0 hH1 s‖ = |t-s|^H := by
  unfold direction
  rw [← map_sub, (hilbertEmbedding SpectralSpace).norm_map, normalized_sub_norm]

theorem increment_integrable (s t : ℝ) (p : ℕ) :
    Integrable (fun ω => |value H hH0 hH1 t ω-value H hH0 hH1 s ω|^p) gaussianProduct := by
  have ht := (firstChaos_hasGaussianLaw (direction H hH0 hH1 t)).memLp
    (by simp : (p : ℝ≥0∞) ≠ ∞)
  have hs := (firstChaos_hasGaussianLaw (direction H hH0 hH1 s)).memLp
    (by simp : (p : ℝ≥0∞) ≠ ∞)
  simpa only [Real.norm_eq_abs, Pi.sub_apply, value] using (ht.sub hs).integrable_norm_pow'

theorem increment_moment (s t : ℝ) (p : ℕ) :
    (∫ ω, |value H hH0 hH1 t ω-value H hH0 hH1 s ω|^p ∂gaussianProduct) =
      (|t-s|^H)^p * standardMoment p := by
  have he : (fun ω => |value H hH0 hH1 t ω-value H hH0 hH1 s ω|^p) =ᵐ[gaussianProduct]
      (fun ω => |firstChaosEmbedding (direction H hH0 hH1 t-direction H hH0 hH1 s) ω|^p) := by
    filter_upwards [Lp.coeFn_sub (value H hH0 hH1 t) (value H hH0 hH1 s)] with ω hω
    have hv : value H hH0 hH1 t-value H hH0 hH1 s =
        firstChaosEmbedding (direction H hH0 hH1 t-direction H hH0 hH1 s) :=
      (map_sub firstChaosEmbedding _ _).symm
    rw [← hv, hω]
    rfl
  rw [integral_congr_ae he, firstChaos_absolute_moment, direction_increment_norm]

def rate (H : ℝ) : ℝ := (1/2 : ℝ)^(H/2)

theorem rate_pos : 0 < rate H := Real.rpow_pos_of_pos (by norm_num) _
include hH0 in
theorem rate_lt_one : rate H < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

include hH0 in
theorem exists_moment_order : ∃ p : ℕ, 2 < H*(p : ℝ) := by
  obtain ⟨p,hp⟩ := exists_nat_gt (2/H)
  refine ⟨p, ?_⟩
  have h := (div_lt_iff₀ hH0).mp hp
  nlinarith

def momentOrder : ℕ := Classical.choose (exists_moment_order H hH0)

theorem momentOrder_admissible : 2 < H*(momentOrder H hH0 : ℝ) :=
  Classical.choose_spec (exists_moment_order H hH0)

theorem dyadic_rate (p : ℕ) (hp : 2 < H*(p : ℝ)) :
    2*((1/2 : ℝ)^(H*(p : ℝ)))/(rate H)^p < 1 := by
  have he : (rate H)^p = (1/2 : ℝ)^(H/2*(p : ℝ)) := by
    exact (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1/2) (H/2) p).symm
  have hi := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1) (by nlinarith : 1+H/2*(p : ℝ) < H*(p : ℝ))
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1/2), Real.rpow_one, ← he] at hi
  apply (div_lt_one (pow_pos (rate_pos H) p)).mpr
  nlinarith

theorem dyadic_moment (p : ℕ) (a : ℝ) (l : ℕ) (k : Fin (2^l)) :
    (∫ ω, |value H hH0 hH1 (grid a l (k.val+1)) ω-
      value H hH0 hH1 (grid a l k.val) ω|^p ∂gaussianProduct) =
      standardMoment p * ((1/2 : ℝ)^(H*(p : ℝ)))^l := by
  rw [increment_moment]
  have he : grid a l (k.val+1)-grid a l k.val = (1/2 : ℝ)^l := by
    unfold grid
    push_cast
    rw [div_pow]
    ring
  rw [he, abs_of_pos (by positivity)]
  have hp : (((1/2 : ℝ)^l)^H)^p = ((1/2 : ℝ)^(H*(p : ℝ)))^l := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1/2),
      ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1/2)]
    congr 1
    ring
  rw [hp, mul_comm]

theorem good : ∀ᵐ ω ∂gaussianProduct,
    GaussianContinuousModification.good (value H hH0 hH1) (rate H) ω := by
  let p := momentOrder H hH0
  have hall : ∀ᵐ ω ∂gaussianProduct, ∀ z : ℤ, ∀ᶠ l in atTop, ∀ k : Fin (2^l),
      |value H hH0 hH1 (grid z l (k.val+1)) ω-
        value H hH0 hH1 (grid z l k.val) ω| < (rate H)^l := by
    rw [ae_all_iff]
    intro z
    exact DyadicMomentControl.dyadic_control (fun r => value H hH0 hH1 r) p
      (standardMoment p) ((1/2 : ℝ)^(H*(p : ℝ))) (rate H)
      (standardMoment_nonnegative p) (Real.rpow_nonneg (by norm_num) _)
      (rate_pos H) (dyadic_rate H p (momentOrder_admissible H hH0))
      (fun s t => increment_integrable H hH0 hH1 s t p)
      (fun a l k => (dyadic_moment H hH0 hH1 p a l k).le) z
  filter_upwards [hall] with ω hω z
  exact eventually_atTop.mp (hω z)

end OperatorDerivativeRewrite.Foundation.FractionalDyadicControl
