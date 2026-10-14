import Foundation.GaussianDisplacementQuarticObstruction
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! The Poisson-constructed Gaussian group has the actual half-density translation formula on all L2. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPhysicalDisplacement
open GaussianCore GaussianDisplacementContinuity GaussianDisplacementQuarticObstruction
open GaussianDisplacementFromPoisson PoissonTiltSourceGauge PoissonTiltHellingerGeometry

def physicalAction (d : ℝ) (f : GaussianL2) (x : ℝ) : ℝ := Real.exp (d*x-d^2)*f (x-2*d)

theorem shifted_gaussian_absolutelyContinuous (d : ℝ) : γ.map (fun x : ℝ => x-2*d)≪γ := by
  rw [γ,gaussianReal_map_sub_const]
  have ha : gaussianReal (0-2*d) 1≪(volume : Measure ℝ) :=
    gaussianReal_absolutelyContinuous (0-2*d) (by norm_num)
  exact ha.trans (gaussianReal_absolutelyContinuous' 0 (by norm_num))

theorem shift_ae (d : ℝ) {P : ℝ → Prop} (h : ∀ᵐ x ∂γ,P x) : ∀ᵐ x ∂γ,P (x-2*d) :=
  ae_of_ae_map (by fun_prop) ((shifted_gaussian_absolutelyContinuous d).ae_le h)

def physicalFormulaDomain (d : ℝ) (U : GaussianL2 ≃ₗᵢ[ℝ] GaussianL2) : Submodule ℝ GaussianL2 where
  carrier := {f | U f =ᵐ[γ] physicalAction d f}
  zero_mem' := by
    change U 0 =ᵐ[γ] physicalAction d 0
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ),
      shift_ae d (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ))] with x hx hs
    simp only [physicalAction,hx,hs,mul_zero,Pi.zero_apply]
  add_mem' := by
    intro f g hf hg
    change U (f+g) =ᵐ[γ] physicalAction d (f+g)
    rw [map_add]
    filter_upwards [hf,hg,Lp.coeFn_add (U f) (U g),shift_ae d (Lp.coeFn_add f g)] with x hf hg hu hs
    simp only [physicalAction] at hf hg ⊢
    rw [hu,Pi.add_apply,hf,hg,hs,Pi.add_apply,mul_add]
  smul_mem' := by
    intro c f hf
    change U (c • f) =ᵐ[γ] physicalAction d (c • f)
    rw [map_smul]
    filter_upwards [hf,Lp.coeFn_smul c (U f),shift_ae d (Lp.coeFn_smul c f)] with x hf hu hs
    simp only [physicalAction] at hf ⊢
    rw [hu,Pi.smul_apply,hf,hs,Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

theorem physicalFormulaDomain_isClosed (d : ℝ) (U : GaussianL2 ≃ₗᵢ[ℝ] GaussianL2) :
    IsClosed (physicalFormulaDomain d U : Set GaussianL2) := by
  apply isSeqClosed_iff_isClosed.mp
  intro fs f hfs ht
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hu : Tendsto (fun n => U (fs (φ n))) atTop (𝓝 (U f)) := by
    simpa only [Function.comp_def] using U.continuous.continuousAt.tendsto.comp (ht.comp hφ.tendsto_atTop)
  obtain ⟨ψ,hψ,hψae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂γ, ∀ n : ℕ, U (fs (φ (ψ n))) x=physicalAction d (fs (φ (ψ n))) x :=
    ae_all_iff.mpr (fun n => hfs (φ (ψ n)))
  change U f =ᵐ[γ] physicalAction d f
  filter_upwards [hψae,shift_ae d hφae,hall] with x hout hin hevery
  have hi : Tendsto (fun n => fs (φ (ψ n)) (x-2*d)) atTop (𝓝 (f (x-2*d))) := by
    simpa only [Function.comp_def] using hin.comp hψ.tendsto_atTop
  have hp : Tendsto (fun n => physicalAction d (fs (φ (ψ n))) x) atTop (𝓝 (physicalAction d f x)) :=
    tendsto_const_nhds.mul hi
  have ho : Tendsto (fun n => U (fs (φ (ψ n))) x) atTop (𝓝 (physicalAction d f x)) :=
    hp.congr' (Eventually.of_forall fun n => (hevery n).symm)
  exact tendsto_nhds_unique hout ho

theorem coherent_physical_formula (rate : ℝ≥0) (hr : 0<rate) (θ a : ℝ) :
    gaussianDisplacement rate hr θ (gaussianRoot a) =ᵐ[γ] physicalAction (displacement rate θ) (gaussianRoot a) := by
  filter_upwards [displaced_coherent_physical rate hr θ a,
    shift_ae (displacement rate θ) (coherentTwo_coeFn a)] with x hout hin
  rw [hout,physicalAction,hin,← Real.exp_add]
  congr 1
  ring

theorem displacement_physical_formula (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : GaussianL2) :
    gaussianDisplacement rate hr θ f =ᵐ[γ]
      fun x => Real.exp (displacement rate θ*x-(displacement rate θ)^2)*f (x-2*displacement rate θ) := by
  let d := displacement rate θ
  let U := gaussianDisplacement rate hr θ
  have hs : coherentSpan≤physicalFormulaDomain d U := by
    apply Submodule.span_le.mpr
    rintro g ⟨a,rfl⟩
    exact coherent_physical_formula rate hr θ a
  have hc := coherentSpan.topologicalClosure_minimal hs (physicalFormulaDomain_isClosed d U)
  rw [coherentSpan_closure] at hc
  exact hc (show f∈(⊤ : Submodule ℝ GaussianL2) from trivial)

theorem physicalAction_memLp (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : GaussianL2) :
    MemLp (physicalAction (displacement rate θ) f) 2 γ :=
  (Lp.memLp (gaussianDisplacement rate hr θ f)).ae_eq (displacement_physical_formula rate hr θ f)

theorem physicalAction_class (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : GaussianL2) :
    (physicalAction_memLp rate hr θ f).toLp (physicalAction (displacement rate θ) f)=
      gaussianDisplacement rate hr θ f := by
  apply Lp.ext
  exact (physicalAction_memLp rate hr θ f).coeFn_toLp.trans (displacement_physical_formula rate hr θ f).symm

end OperatorDerivativeRewrite.Foundation.GaussianPhysicalDisplacement
