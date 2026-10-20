import Foundation.RiemannQuarticEvolution
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Joint time-space continuity and compact-uniform time limits for the
literal quartic flow. The majorant is an actual integrable arithmetic weight. -/
noncomputable section
open MeasureTheory Filter Set Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTimeCompact
open RiemannQuarticFlow RiemannQuarticDomain RiemannQuarticKernel

theorem jet_joint_continuous (k : ℕ) :
    Continuous (fun p : ℝ × ℂ => jet k p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hfst : Continuous (fun q : ℝ × ℂ => q.1) := continuous_fst
  have hsnd : Continuous (fun q : ℝ × ℂ => ‖q.2‖) := continuous_snd.norm
  have hT : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.1 ≤ |p.1|+1 :=
    (hfst.continuousAt.eventually
      (Iio_mem_nhds (by linarith [le_abs_self p.1]))).mono fun _ h => h.le
  have hB : ∀ᶠ q : ℝ × ℂ in 𝓝 p, ‖q.2‖ ≤ ‖p.2‖+1 :=
    (hsnd.continuousAt.eventually
      (Iio_mem_nhds (by linarith : ‖p.2‖ < ‖p.2‖+1))).mono fun _ h => h.le
  apply continuousAt_of_dominated
    (F := fun q : ℝ × ℂ => integrand k q.1 q.2)
    (μ := halfLine) (bound := weighted k (|p.1|+1) (‖p.2‖+1))
    (Eventually.of_forall fun q => (integrand_integrable k q.1 q.2).aestronglyMeasurable)
    ?_ (weighted_integrable k (|p.1|+1) (‖p.2‖+1)) ?_
  · filter_upwards [hT,hB] with q hqT hqB
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact (integrand_bound k q.1 q.2 u hu).trans (weighted_mono k hqT hqB hu)
  · apply Eventually.of_forall
    intro u
    have he : Continuous (fun q : ℝ × ℂ =>
        (((Real.exp (q.1*u^4)*kernel u : ℝ) : ℂ) *
          (Complex.I*(u : ℂ))^k * Complex.exp (Complex.I*(u : ℂ)*q.2))) := by
      fun_prop
    simpa only [integrand,weighted,pow_zero,one_mul,zero_mul,add_zero] using he.continuousAt

theorem flow_joint_continuous :
    Continuous (fun p : ℝ × ℂ => flow p.1 p.2) := by
  have hn : Continuous (fun p : ℝ × ℂ => (p.1,-p.2)) := by fun_prop
  exact ((jet_joint_continuous 0).add
    (Continuous.comp (g := fun p : ℝ × ℂ => jet 0 p.1 p.2)
      (f := fun p : ℝ × ℂ => (p.1,-p.2)) (jet_joint_continuous 0) hn)).div_const 2

theorem flow_time_tendsto_uniformly_on (t : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun s z => flow s z) (flow t) (𝓝 t) K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hp : Continuous (fun p : ℝ × K => (p.1,(p.2 : ℂ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun p : ℝ × K => flow p.1 p.2) :=
    Continuous.comp (g := fun p : ℝ × ℂ => flow p.1 p.2)
      (f := fun p : ℝ × K => (p.1,(p.2 : ℂ))) flow_joint_continuous hp
  have h := Continuous.tendstoUniformly (fun s (z : K) => flow s z) hc t
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr h

theorem flow_time_tendsto_locally_uniformly (t : ℝ) :
    TendstoLocallyUniformly (fun s z => flow s z) (flow t) (𝓝 t) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact flow_time_tendsto_uniformly_on t

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTimeCompact
