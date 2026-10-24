import Foundation.GaussianBoundedTiltDerivative
import Foundation.GaussianHalfHolderScore

/-! The actual spatial derivative of a Gaussian Bochner heat mean for bounded
continuous real-Banach curves equals the centered score. No smoothness of the
original curve, Malliavin-domain membership or stochastic reconstruction is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundedHeatDerivative
open GaussianCore GaussianBoundedTiltDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def mean (f : ℝ → E) (b h : ℝ) : E := ∫ z : ℝ, f (b+h*z) ∂γ

theorem mean_integrable (f : ℝ → E) (hf : Continuous f) (M : ℝ)
    (hB : ∀ x, ‖f x‖ ≤ M) (b h : ℝ) :
    Integrable (fun z : ℝ => f (b+h*z)) γ :=
  (integrable_const M).mono'
    ((hf.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => hB _)

theorem linear_weight_integrable (f : ℝ → E) (hf : Continuous f) (M : ℝ)
    (hM : 0 ≤ M) (hB : ∀ x, ‖f x‖ ≤ M) (b h : ℝ) :
    Integrable (fun z : ℝ => z • f (b+h*z)) γ := by
  have hz : Integrable (fun z : ℝ => |z|) γ :=
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable (by norm_num)).norm
  apply (hz.mul_const M).mono'
    (continuous_id.smul (hf.comp (continuous_const.add
      (continuous_const.mul continuous_id)))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change ‖z • f (b+h*z)‖ ≤ |z| * M
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg z)

theorem mean_continuous (f : ℝ → E) (hf : Continuous f) (M : ℝ)
    (hB : ∀ x, ‖f x‖ ≤ M) : Continuous (fun p : ℝ × ℝ => mean f p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => M)
  · intro p
    exact (mean_integrable f hf M hB p.1 p.2).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun z => hB _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun z =>
      hf.comp (continuous_fst.add (continuous_snd.mul continuous_const))

theorem centered_integral (f : ℝ → E) (hf : Continuous f) (M : ℝ)
    (hM : 0 ≤ M) (hB : ∀ x, ‖f x‖ ≤ M) (b h : ℝ) :
    (∫ z : ℝ, z • (f (b+h*z)-f b) ∂γ) = ∫ z : ℝ, z • f (b+h*z) ∂γ := by
  have hz : Integrable (fun z : ℝ => z) γ :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by simp)).integrable (by norm_num)
  simp_rw [smul_sub]
  rw [integral_sub (linear_weight_integrable f hf M hM hB b h) (hz.smul_const (f b)),
    integral_smul_const,integral_id_gaussianReal]
  simp

theorem mean_hasDerivAt (f : ℝ → E) (hf : Continuous f) (M : ℝ)
    (hM : 0 ≤ M) (hB : ∀ x, ‖f x‖ ≤ M) (b h : ℝ) (hh : h ≠ 0) :
    HasDerivAt (fun x => mean f x h) (GaussianHalfHolderScore.score f b h) b := by
  let F : ℝ → E := fun z => f (b+h*z)
  have hF : Continuous F := hf.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hd := translate_hasDerivAt_zero F hF M hM (fun z => hB _)
  have hq : HasDerivAt (fun x : ℝ => (x-b)/h) (1/h) b := by
    simpa only [id_eq,one_div] using ((hasDerivAt_id b).sub_const b).div_const h
  have hc := hd.scomp_of_eq b hq (by simp)
  have he : ((fun t : ℝ => ∫ z : ℝ, F (z+t) ∂γ) ∘ fun x : ℝ => (x-b)/h) =
      fun x => mean f x h := by
    funext x
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change f (b+h*(z+(x-b)/h)) = f (x+h*z)
      congr 1
      field_simp
      ring
  rw [he] at hc
  have hv : (1/h) • (∫ z : ℝ, z • F z ∂γ) = GaussianHalfHolderScore.score f b h := by
    rw [GaussianHalfHolderScore.score,centered_integral f hf M hM hB,one_div]
  rw [hv] at hc
  exact hc

end OperatorDerivativeRewrite.Foundation.GaussianBoundedHeatDerivative
