import Foundation.PoissonWeightedScalarGeometry
import Foundation.GaussianHermiteAdjoints

/-! Exact maximal Poisson graphs from complete scalar and weighted field coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonSpectralGraphs
open PoissonDifferenceOperators PoissonMaximalOperators PoissonCharlierLadder
open PoissonCharlierHilbertBasis hiding coefficient
open PoissonDivergenceRecovery PoissonWeightedScalarGeometry

def fieldCoefficient (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (n : ℕ) : ℝ :=
  inner ℝ (normalizedField rate hr n) u

def scalarTruncation (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (N : ℕ) : ScalarL2 rate :=
  ∑ n ∈ Finset.range N, coefficient rate hr f n • normalized rate hr n

def fieldTruncation (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (N : ℕ) : FieldL2 rate :=
  ∑ n ∈ Finset.range N, fieldCoefficient rate hr u n • normalizedField rate hr n

theorem scalarTruncation_tendsto (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    Tendsto (scalarTruncation rate hr f) atTop (𝓝 f) :=
  (expansion_hasSum rate hr f).tendsto_sum_nat

theorem fieldTruncation_tendsto (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) :
    Tendsto (fieldTruncation rate hr u) atTop (𝓝 u) :=
  (fieldBasis_hasSum rate hr u).tendsto_sum_nat

theorem normalized_lowering_graph (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    (normalized rate hr (n+1),Real.sqrt (n+1 : ℝ) • normalizedField rate hr n) ∈
      (maximalDifference rate hr).graph := by
  have hg := (maximalDifference rate hr).graph.smul_mem (normalizer rate (n+1))⁻¹
    (lowering_graph rate hr n)
  have hp := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<n+1 by positivity))
  have hn := ne_of_gt (normalizer_pos rate hr n)
  have hR := ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ)<rate from hr))
  have he : (normalizer rate (n+1))⁻¹*(n+1 : ℝ)=
      Real.sqrt (n+1 : ℝ)*(Real.sqrt (rate : ℝ)*normalizer rate n)⁻¹ := by
    rw [normalizer_succ]
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n+1 by positivity)]
  simpa only [normalized,normalizedField,Prod.smul_mk,smul_smul,he] using hg

theorem difference_coefficients (rate : ℝ≥0) (hr : 0 < rate) {f : ScalarL2 rate} {g : FieldL2 rate}
    (hf : (f,g) ∈ (maximalDifference rate hr).graph) (n : ℕ) :
    fieldCoefficient rate hr g n=Real.sqrt (n+1 : ℝ)*coefficient rate hr f (n+1) := by
  have hi := graph_duality rate hr hf (normalized_raising_graph rate hr n)
  simpa only [inner_smul_right,real_inner_comm g,real_inner_comm f,coefficient,fieldCoefficient] using hi

theorem divergence_coefficients (rate : ℝ≥0) (hr : 0 < rate) {u : FieldL2 rate} {f : ScalarL2 rate}
    (hu : (u,f) ∈ (maximalDivergence rate hr).graph) (n : ℕ) :
    coefficient rate hr f (n+1)=Real.sqrt (n+1 : ℝ)*fieldCoefficient rate hr u n := by
  have hi := graph_duality rate hr (normalized_lowering_graph rate hr n) hu
  simpa only [real_inner_smul_left,coefficient,fieldCoefficient] using hi.symm

theorem scalarTruncation_succ (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (N : ℕ) :
    scalarTruncation rate hr f (N+1)=scalarTruncation rate hr f N+
      coefficient rate hr f N • normalized rate hr N := by
  exact Finset.sum_range_succ _ _

theorem fieldTruncation_succ (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (N : ℕ) :
    fieldTruncation rate hr u (N+1)=fieldTruncation rate hr u N+
      fieldCoefficient rate hr u N • normalizedField rate hr N := by
  exact Finset.sum_range_succ _ _

theorem truncation_difference_graph (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (g : FieldL2 rate)
    (h : ∀ n, fieldCoefficient rate hr g n=Real.sqrt (n+1 : ℝ)*coefficient rate hr f (n+1)) (N : ℕ) :
    (scalarTruncation rate hr f (N+1),fieldTruncation rate hr g N) ∈
      (maximalDifference rate hr).graph := by
  induction N with
  | zero =>
    simpa only [scalarTruncation,fieldTruncation,Nat.zero_add,Finset.sum_range_one,Finset.range_zero,
      Finset.sum_empty,Prod.smul_mk,smul_zero] using
      (maximalDifference rate hr).graph.smul_mem (coefficient rate hr f 0) (zero_mode_difference_graph rate hr)
  | succ N ih =>
    have hn := (maximalDifference rate hr).graph.smul_mem (coefficient rate hr f (N+1))
      (normalized_lowering_graph rate hr N)
    have hh := (maximalDifference rate hr).graph.add_mem ih hn
    rw [scalarTruncation_succ rate hr f (N+1),fieldTruncation_succ rate hr g N,h N]
    convert hh using 1
    simp only [Prod.mk_add_mk,Prod.smul_mk,smul_smul,mul_comm]

theorem truncation_divergence_graph (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (f : ScalarL2 rate)
    (h0 : coefficient rate hr f 0=0)
    (h : ∀ n, coefficient rate hr f (n+1)=Real.sqrt (n+1 : ℝ)*fieldCoefficient rate hr u n) (N : ℕ) :
    (fieldTruncation rate hr u N,scalarTruncation rate hr f (N+1)) ∈
      (maximalDivergence rate hr).graph := by
  induction N with
  | zero =>
    simp only [scalarTruncation,fieldTruncation,Nat.zero_add,Finset.sum_range_one,Finset.range_zero,
      Finset.sum_empty,h0,zero_smul]
    exact (maximalDivergence rate hr).graph.zero_mem
  | succ N ih =>
    have hn := (maximalDivergence rate hr).graph.smul_mem (fieldCoefficient rate hr u N)
      (normalized_raising_graph rate hr N)
    have hh := (maximalDivergence rate hr).graph.add_mem ih hn
    rw [fieldTruncation_succ rate hr u N,scalarTruncation_succ rate hr f (N+1),h N]
    convert hh using 1
    simp only [Prod.mk_add_mk,Prod.smul_mk,smul_smul,mul_comm]

theorem difference_graph_iff (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (g : FieldL2 rate) :
    (f,g) ∈ (maximalDifference rate hr).graph ↔
      ∀ n, fieldCoefficient rate hr g n=Real.sqrt (n+1 : ℝ)*coefficient rate hr f (n+1) := by
  constructor
  · exact fun hf n => difference_coefficients rate hr hf n
  · intro h
    apply (maximalDifference_isClosed rate hr).mem_of_tendsto
      (((scalarTruncation_tendsto rate hr f).comp (tendsto_add_atTop_nat 1)).prodMk_nhds
        (fieldTruncation_tendsto rate hr g))
    exact Eventually.of_forall (truncation_difference_graph rate hr f g h)

theorem divergence_graph_iff (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (f : ScalarL2 rate) :
    (u,f) ∈ (maximalDivergence rate hr).graph ↔ coefficient rate hr f 0=0 ∧
      ∀ n, coefficient rate hr f (n+1)=Real.sqrt (n+1 : ℝ)*fieldCoefficient rate hr u n := by
  constructor
  · intro hu
    exact ⟨(exists_divergence_iff_zero_mode rate hr f).mp ⟨u,hu⟩,divergence_coefficients rate hr hu⟩
  · rintro ⟨h0,h⟩
    apply (maximalDivergence_isClosed rate hr).mem_of_tendsto
      ((fieldTruncation_tendsto rate hr u).prodMk_nhds
        ((scalarTruncation_tendsto rate hr f).comp (tendsto_add_atTop_nat 1)))
    exact Eventually.of_forall (truncation_divergence_graph rate hr u f h0 h)

def fieldGaussianTransfer (rate : ℝ≥0) (hr : 0 < rate) : FieldL2 rate ≃ₗᵢ[ℝ] GaussianCore.GaussianL2 :=
  (weightedScalarEquiv rate hr).trans (gaussianTransfer rate hr)

theorem fieldTransfer_normalized (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    fieldGaussianTransfer rate hr (normalizedField rate hr n)=GaussianCore.normalizedHermite n := by
  rw [fieldGaussianTransfer,LinearIsometryEquiv.trans_apply,equiv_normalizedField,transfer_normalized]

theorem scalarTransfer_coefficient (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) :
    GaussianCore.hermiteCoefficient (gaussianTransfer rate hr f) n=coefficient rate hr f n :=
  transfer_coefficient rate hr f n

theorem fieldTransfer_coefficient (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (n : ℕ) :
    GaussianCore.hermiteCoefficient (fieldGaussianTransfer rate hr u) n=fieldCoefficient rate hr u n := by
  rw [GaussianCore.hermiteCoefficient,← fieldTransfer_normalized rate hr n]
  exact (fieldGaussianTransfer rate hr).inner_map_map _ _

theorem difference_transfer_iff (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (g : FieldL2 rate) :
    (f,g) ∈ (maximalDifference rate hr).graph ↔
      (gaussianTransfer rate hr f,fieldGaussianTransfer rate hr g) ∈ GaussianCore.closedDerivative.graph := by
  rw [difference_graph_iff,GaussianCore.closedDerivative_graph_iff]
  simp only [scalarTransfer_coefficient,fieldTransfer_coefficient]

theorem divergence_transfer_iff (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) (f : ScalarL2 rate) :
    (u,f) ∈ (maximalDivergence rate hr).graph ↔
      (fieldGaussianTransfer rate hr u,gaussianTransfer rate hr f) ∈ GaussianCore.closedDivergence.graph := by
  rw [divergence_graph_iff,GaussianCore.closedDivergence_graph_iff]
  simp only [scalarTransfer_coefficient,fieldTransfer_coefficient]

end OperatorDerivativeRewrite.Foundation.PoissonSpectralGraphs
