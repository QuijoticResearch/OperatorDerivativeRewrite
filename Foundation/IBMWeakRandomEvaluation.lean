import Foundation.BochnerL2RepresentativeFubini
import Foundation.GaussianTimeProcess
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Scalar evaluation of a weakly measurable random functional against an
actual Bochner-L2 random input. No strong norm-dual measurability is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMWeakRandomEvaluation
open InfiniteGaussian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem evaluation_measurable (A : SampleSpace → E →L[ℝ] ℝ)
    (hA : ∀ x, Measurable (fun Y => A Y x)) (f : SampleSpace → E)
    (hf : StronglyMeasurable f) : Measurable (fun Y => A Y (f Y)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => (hf.approx n).measurable_bind (fun x Y => A Y x) hA)
  rw [tendsto_pi_nhds]
  intro Y
  exact (A Y).continuous.continuousAt.tendsto.comp (hf.tendsto_approx Y)

theorem evaluation_aestronglyMeasurable (A : SampleSpace → E →L[ℝ] ℝ)
    (hA : ∀ x, Measurable (fun Y => A Y x)) (f : SampleSpace → E)
    (hf : AEStronglyMeasurable f gaussianProduct) :
    AEStronglyMeasurable (fun Y => A Y (f Y)) gaussianProduct := by
  apply (evaluation_measurable A hA (hf.mk f) hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [hf.ae_eq_mk] with Y hY
  rw [hY]

private def normClass (f : Lp E 2 gaussianProduct) : GaussianL2 :=
  (Lp.memLp f).norm.toLp (fun Y => ‖f Y‖)

private theorem normClass_actual (f : Lp E 2 gaussianProduct) :
    normClass f =ᵐ[gaussianProduct] fun Y => ‖f Y‖ := MemLp.coeFn_toLp _

private theorem normClass_norm (f : Lp E 2 gaussianProduct) : ‖normClass f‖ = ‖f‖ := by
  rw [normClass,Lp.norm_toLp,eLpNorm_norm _ (Lp.aestronglyMeasurable f)]
  rfl

variable (A : SampleSpace → E →L[ℝ] ℝ) (hA : ∀ x, Measurable (fun Y => A Y x))
  (w : GaussianL2) (hb : ∀ᵐ Y ∂gaussianProduct, ∀ x, ‖A Y x‖ ≤ ‖w Y‖*‖x‖)

include hA w hb in
theorem evaluation_integrable (f : Lp E 2 gaussianProduct) :
    Integrable (fun Y => A Y (f Y)) gaussianProduct := by
  apply ((Lp.memLp w).norm.integrable_mul (Lp.memLp f).norm).mono'
    (evaluation_aestronglyMeasurable A hA f (Lp.aestronglyMeasurable f))
  exact hb.mono fun Y hY => hY (f Y)

def value (f : Lp E 2 gaussianProduct) : Lp ℝ 1 gaussianProduct :=
  (evaluation_integrable A hA w hb f).toL1 _

theorem value_actual (f : Lp E 2 gaussianProduct) :
    value A hA w hb f =ᵐ[gaussianProduct] fun Y => A Y (f Y) :=
  (evaluation_integrable A hA w hb f).coeFn_toL1

theorem value_bound (f : Lp E 2 gaussianProduct) : ‖value A hA w hb f‖ ≤ ‖w‖*‖f‖ := by
  rw [value,L1.norm_of_fun_eq_integral_norm]
  calc
    _ ≤ ∫ Y, ‖w Y‖*‖f Y‖ ∂gaussianProduct := integral_mono_ae
      (evaluation_integrable A hA w hb f).norm
      ((Lp.memLp w).norm.integrable_mul (Lp.memLp f).norm) (hb.mono fun Y hY => hY (f Y))
    _ = ∫ Y, ‖inner ℝ (w Y) (normClass f Y)‖ ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [normClass_actual f] with Y hY
      rw [hY,Real.inner_apply,norm_mul,norm_norm,mul_comm]
    _ ≤ _ := by
      simpa only [normClass_norm] using
        BochnerL2RepresentativeFubini.pairing_norm_integral_le w (normClass f)

theorem value_add (f g : Lp E 2 gaussianProduct) :
    value A hA w hb (f+g) = value A hA w hb f+value A hA w hb g := by
  apply Lp.ext
  filter_upwards [value_actual A hA w hb (f+g),value_actual A hA w hb f,
    value_actual A hA w hb g,Lp.coeFn_add f g,
    Lp.coeFn_add (value A hA w hb f) (value A hA w hb g)] with Y ha hf hg hi ho
  rw [ha,ho,Pi.add_apply,hf,hg,hi,Pi.add_apply,map_add]

theorem value_smul (c : ℝ) (f : Lp E 2 gaussianProduct) :
    value A hA w hb (c • f) = c • value A hA w hb f := by
  apply Lp.ext
  filter_upwards [value_actual A hA w hb (c • f),value_actual A hA w hb f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (value A hA w hb f)] with Y ha hf hi ho
  rw [ha,ho,Pi.smul_apply,hf,hi,Pi.smul_apply,map_smul]

def operator : Lp E 2 gaussianProduct →L[ℝ] Lp ℝ 1 gaussianProduct :=
  ({ toFun := value A hA w hb
     map_add' := value_add A hA w hb
     map_smul' := value_smul A hA w hb } :
      Lp E 2 gaussianProduct →ₗ[ℝ] Lp ℝ 1 gaussianProduct).mkContinuous ‖w‖
    (value_bound A hA w hb)

end OperatorDerivativeRewrite.Foundation.IBMWeakRandomEvaluation
