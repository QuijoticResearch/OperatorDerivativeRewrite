import Foundation.FourierPathDualTimeGradient
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Actual jointly measurable time/path representatives of the dual-control time density. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualJointDensity
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDualControls FourierPathDualTimeGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def representative (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : ℝ → TestSpace levels ξ :=
  (Lp.aestronglyMeasurable (timeGradient levels ξ m T hT q)).mk
    (timeGradient levels ξ m T hT q)

theorem representative_stronglyMeasurable (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : StronglyMeasurable (representative levels ξ m T hT q) :=
  (Lp.aestronglyMeasurable (timeGradient levels ξ m T hT q)).stronglyMeasurable_mk

theorem representative_ae (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) :
    (timeGradient levels ξ m T hT q : ℝ → TestSpace levels ξ) =ᵐ[volume]
      representative levels ξ m T hT q :=
  (Lp.aestronglyMeasurable (timeGradient levels ξ m T hT q)).ae_eq_mk

def joint (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (z : ℝ × Path) : ℂ :=
  realize levels ξ (representative levels ξ m T hT q z.1) z.2

theorem joint_measurable (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : Measurable (joint levels ξ m T hT q) := by
  letI : SecondCountableTopology Path :=
    TopologicalSpace.Subtype.secondCountableTopology {ω : C(ℝ,ℝ) | ω 0 = 0}
  letI : MeasurableSpace (TestSpace levels ξ) := borel (TestSpace levels ξ)
  letI : BorelSpace (TestSpace levels ξ) := ⟨rfl⟩
  have he : Continuous (fun z : TestSpace levels ξ × Path => realize levels ξ z.1 z.2) := by
    fun_prop
  exact he.measurable.comp
    (((representative_stronglyMeasurable levels ξ m T hT q).measurable.comp measurable_fst).prodMk
      measurable_snd)

theorem joint_path_continuous (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (t : ℝ) : Continuous (fun ω => joint levels ξ m T hT q (t,ω)) :=
  (realize levels ξ (representative levels ξ m T hT q t)).continuous

theorem joint_section_ae (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) :
    (realizedField levels ξ m T hT q ω : ℝ → ℂ) =ᵐ[volume]
      fun t => joint levels ξ m T hT q (t,ω) := by
  let L := (BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)
  filter_upwards [L.coeFn_compLpL (timeGradient levels ξ m T hT q),
    representative_ae levels ξ m T hT q] with t ht hr
  exact ht.trans (congrArg L hr)

theorem joint_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (z : ℝ × Path) :
    ‖joint levels ξ m T hT q z‖ ≤ ‖representative levels ξ m T hT q z.1‖ :=
  ((realize levels ξ _).norm_coe_le_norm z.2).trans (realize_bound levels ξ _)

theorem joint_memLp (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (μ : Measure Path) [IsFiniteMeasure μ] :
    MemLp (joint levels ξ m T hT q) (HigherHeatLpControls.power m) (volume.prod μ) := by
  have hr : MemLp (representative levels ξ m T hT q) (HigherHeatLpControls.power m) volume :=
    MemLp.ae_eq (representative_ae levels ξ m T hT q)
      (Lp.memLp (timeGradient levels ξ m T hT q))
  exact (hr.comp_fst μ).mono (joint_measurable levels ξ m T hT q).aestronglyMeasurable
    (Eventually.of_forall (joint_bound levels ξ m T hT q))

theorem joint_contraction (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : Path) (u : Control m) :
    (∫ t : ℝ, u t • joint levels ξ m T hT q (t,ω)) =
      realize levels ξ (FourierPathDualGradient.gradient levels ξ m T hT q u) ω := by
  rw [← realizedField_pairing, BochnerDualControlPairing.pairing_integral]
  apply integral_congr_ae
  exact (joint_section_ae levels ξ m T hT q ω).symm.mono (fun t ht => congrArg (u t • ·) ht)

end OperatorDerivativeRewrite.Foundation.FourierPathDualJointDensity
