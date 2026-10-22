import Foundation.IBMIntrinsicEnergyResolvent
import Mathlib.Topology.MetricSpace.Contracting

/-! Actual centered intrinsic Poisson solutions via the verified energy resolvent. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicPoisson
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicPoincare
open IBMIntrinsicEnergyResolvent
open IBMCenteredSourceRepresentation (intrinsicOne)
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def centered : Submodule ℝ IntrinsicSpace := (innerSL ℝ intrinsicOne).ker

theorem centered_mem (x : IntrinsicSpace) : x ∈ centered ↔ mean x = 0 := by
  change inner ℝ intrinsicOne x = 0 ↔ mean x = 0
  rw [mean_pairing]

theorem centered_closed : IsClosed (centered : Set IntrinsicSpace) :=
  (innerSL ℝ intrinsicOne).isClosed_ker

local instance : CompleteSpace centered := centered_closed.completeSpace_coe

theorem mean_add (x y : IntrinsicSpace) : mean (x+y) = mean x + mean y := by
  rw [mean_pairing, mean_pairing, mean_pairing, inner_add_right]

theorem mean_sub (x y : IntrinsicSpace) : mean (x-y) = mean x - mean y := by
  rw [mean_pairing, mean_pairing, mean_pairing, inner_sub_right]

def iteration (x : centered) (u : centered) : centered :=
  ⟨resolvent ((x : IntrinsicSpace)+(u : IntrinsicSpace)), by
    apply (centered_mem _).mpr
    rw [resolvent_mean, mean_add, (centered_mem _).mp x.property,
      (centered_mem _).mp u.property, zero_add]⟩

theorem iteration_contracting (x : centered) : ContractingWith (1/2 : ℝ≥0) (iteration x) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change dist (resolvent ((x : IntrinsicSpace)+(u : IntrinsicSpace)))
    (resolvent ((x : IntrinsicSpace)+(v : IntrinsicSpace))) ≤
      ((1/2 : ℝ≥0) : ℝ) * dist (u : IntrinsicSpace) (v : IntrinsicSpace)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    show ((x : IntrinsicSpace)+(u : IntrinsicSpace))-((x : IntrinsicSpace)+(v : IntrinsicSpace)) =
      (u : IntrinsicSpace)-(v : IntrinsicSpace) from by abel]
  have hm : mean ((u : IntrinsicSpace)-(v : IntrinsicSpace)) = 0 := by
    rw [mean_sub, (centered_mem _).mp u.property, (centered_mem _).mp v.property, sub_self]
  have h := centered_half_contraction _ hm
  norm_num at h ⊢
  linarith

def solution (x : centered) : centered := (iteration_contracting x).fixedPoint (iteration x)

theorem solution_fixed (x : centered) :
    resolvent ((x : IntrinsicSpace)+(solution x : IntrinsicSpace)) = (solution x : IntrinsicSpace) :=
  congrArg Subtype.val (iteration_contracting x).fixedPoint_isFixedPt

theorem solution_mem (x : centered) : (solution x : IntrinsicSpace) ∈ jointDerivative.domain := by
  have h := resolvent_mem ((x : IntrinsicSpace)+(solution x : IntrinsicSpace))
  rwa [solution_fixed x] at h

def solutionElement (x : centered) : jointDerivative.domain := ⟨solution x, solution_mem x⟩

theorem solution_gradient (x : centered) : jointDerivative (solutionElement x) =
    gradient ((x : IntrinsicSpace)+(solution x : IntrinsicSpace)) := by
  have hg := ClosedOperatorEnergyResolvent.pair_mem_graph jointDerivative jointDerivative_closed
    ((x : IntrinsicSpace)+(solution x : IntrinsicSpace))
  change (resolvent ((x : IntrinsicSpace)+(solution x : IntrinsicSpace)),
    gradient ((x : IntrinsicSpace)+(solution x : IntrinsicSpace))) ∈ jointDerivative.graph at hg
  rw [solution_fixed x] at hg
  exact ((jointDerivative.image_iff (solution_mem x)).mpr hg).symm

theorem fixed_point_poisson_graph (x u : IntrinsicSpace) (hu : resolvent (x+u) = u) :
    (gradient (x+u), x) ∈ jointDivergence.graph := by
  have hv := divergence_gradient (x+u)
  rw [hu, add_sub_cancel_right] at hv
  exact jointDivergence.mem_graph_iff.mpr ⟨⟨gradient (x+u), gradient_mem (x+u)⟩, rfl, hv⟩

theorem poisson_graph (x : centered) :
    (jointDerivative (solutionElement x), (x : IntrinsicSpace)) ∈ jointDivergence.graph := by
  have hg := fixed_point_poisson_graph (x : IntrinsicSpace) (solution x : IntrinsicSpace) (solution_fixed x)
  rw [solution_gradient x]
  exact hg

theorem poisson_equation (x : centered) :
    ∃ h : jointDerivative (solutionElement x) ∈ jointDivergence.domain,
      jointDivergence ⟨jointDerivative (solutionElement x), h⟩ = (x : IntrinsicSpace) := by
  have h := LinearPMap.mem_domain_of_mem_graph (poisson_graph x)
  exact ⟨h, ((jointDivergence.image_iff h).mpr (poisson_graph x)).symm⟩

theorem graph_pairing (u : JointFieldSpace) (y : IntrinsicSpace)
    (hu : (u,y) ∈ jointDivergence.graph) (v : jointDerivative.domain) :
    inner ℝ y (v : IntrinsicSpace) = inner ℝ u (jointDerivative v) := by
  have hd := LinearPMap.mem_domain_of_mem_graph hu
  have he : jointDivergence ⟨u,hd⟩ = y := ((jointDivergence.image_iff hd).mpr hu).symm
  calc
    inner ℝ y (v : IntrinsicSpace) = inner ℝ (jointDivergence ⟨u,hd⟩) (v : IntrinsicSpace) :=
      congrArg (fun z : IntrinsicSpace => inner ℝ z (v : IntrinsicSpace)) he.symm
    _ = _ := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense ⟨u,hd⟩ v

theorem zero_solution (v : jointDerivative.domain)
    (hm : mean (v : IntrinsicSpace) = 0)
    (hg : (jointDerivative v, (0 : IntrinsicSpace)) ∈ jointDivergence.graph) :
    (v : IntrinsicSpace) = 0 := by
  have hi := graph_pairing (jointDerivative v) 0 hg v
  rw [inner_zero_left] at hi
  have hz : jointDerivative v = 0 := inner_self_eq_zero.mp hi.symm
  have hp := centered_poincare v hm
  rw [hz, norm_zero] at hp
  exact norm_eq_zero.mp (le_antisymm hp (norm_nonneg _))

theorem solution_unique (x : centered) (v : jointDerivative.domain)
    (hm : mean (v : IntrinsicSpace) = 0)
    (hg : (jointDerivative v, (x : IntrinsicSpace)) ∈ jointDivergence.graph) :
    (v : IntrinsicSpace) = (solution x : IntrinsicSpace) := by
  let w : jointDerivative.domain := v-solutionElement x
  have hw : (jointDerivative w, (0 : IntrinsicSpace)) ∈ jointDivergence.graph := by
    have h := jointDivergence.graph.sub_mem hg (poisson_graph x)
    change (jointDerivative v-jointDerivative (solutionElement x),
      (x : IntrinsicSpace)-(x : IntrinsicSpace)) ∈ jointDivergence.graph at h
    rw [sub_self, ← jointDerivative.map_sub] at h
    exact h
  have hmean : mean (w : IntrinsicSpace) = 0 := by
    change mean ((v : IntrinsicSpace)-(solution x : IntrinsicSpace)) = 0
    rw [mean_sub, hm, (centered_mem _).mp (solution x).property, sub_self]
  have hz := zero_solution w hmean hw
  exact sub_eq_zero.mp hz

theorem gradient_minimal (x : centered) (v : JointFieldSpace)
    (hv : (v, (x : IntrinsicSpace)) ∈ jointDivergence.graph) :
    ‖jointDerivative (solutionElement x)‖ ≤ ‖v‖ := by
  have hk : (v-jointDerivative (solutionElement x), (0 : IntrinsicSpace)) ∈ jointDivergence.graph := by
    simpa only [Prod.mk_sub_mk, sub_self] using jointDivergence.graph.sub_mem hv (poisson_graph x)
  have ho := graph_pairing (v-jointDerivative (solutionElement x)) 0 hk (solutionElement x)
  rw [inner_zero_left] at ho
  change 0 = inner ℝ (v-jointDerivative (solutionElement x)) (jointDerivative (solutionElement x)) at ho
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have hn := sq_nonneg ‖v-jointDerivative (solutionElement x)‖
  rw [norm_sub_sq_real] at hn
  nlinarith [norm_nonneg v, norm_nonneg (jointDerivative (solutionElement x))]

theorem solution_bounds (x : centered) :
    ‖jointDerivative (solutionElement x)‖ ≤ ‖(x : IntrinsicSpace)‖ ∧
    ‖(solution x : IntrinsicSpace)‖ ≤ ‖(x : IntrinsicSpace)‖ := by
  obtain ⟨hr, hv⟩ := IBMStochasticNativeDivergence.centered_observable_recovery (x : IntrinsicSpace)
    ((centered_mem _).mp x.property)
  have hg : (IBMNativeGaussianRecovery.recoveryPair ((x : IntrinsicSpace) : JointL2),
      (x : IntrinsicSpace)) ∈ jointDivergence.graph :=
    jointDivergence.mem_graph_iff.mpr ⟨⟨_, hr⟩, rfl, hv⟩
  have hb := (gradient_minimal x _ hg).trans
    (IBMNativeRecoveryContraction.recovery_contraction ((x : IntrinsicSpace) : JointL2))
  refine ⟨hb, ?_⟩
  exact (centered_poincare (solutionElement x) ((centered_mem _).mp (solution x).property)).trans hb

theorem iterate_convergence (x : centered) (u : centered) :
    Tendsto (fun n => (iteration x)^[n] u) atTop (𝓝 (solution x)) :=
  (iteration_contracting x).tendsto_iterate_fixedPoint u

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicPoisson
