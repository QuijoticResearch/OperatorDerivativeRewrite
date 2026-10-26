import Foundation.GaussianClockSourceSpectral
import Mathlib.Analysis.Normed.Group.Tannery
import Foundation.BochnerCoefficientParseval
/-! Closed spectral multipliers on the ORIGINAL source-valued clock space.
Their exact maximal domains and strong graph-core approximations are proved
from original Gaussian number projections, Parseval, and L2 completeness. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockSpectralPowers
open InfiniteGaussian GaussianClockValueOperators GaussianNumberSectors
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def project (n : ℕ) : Field →L[ℝ] Field := clockLift (projection n)

theorem project_comp (n m : ℕ) (f : Field) :
    project n (project m f) = if n=m then project n f else 0 := by
  apply eq_of_all_tests
  intro L
  by_cases h : n=m
  · subst m
    simp only [project,clockLift_test,ite_true,projection_idempotent]
  · simp only [if_neg h,project,clockLift_test,map_zero]
    exact projection_of_sector (n := n) ⟨_,projection_mem m _⟩ |>.trans (by simp only [if_neg h])

theorem project_hasSum_norm_sq (f : Field) :
    HasSum (fun n => ‖project n f‖^2) (‖f‖^2) := by
  let F := ProductL2Curry.flip gaussianProduct gaussianProduct
  have hs := BochnerCoefficientParseval.lift_hasSum gaussianProduct projection
    projection_hasSum_norm_sq (F f)
  have he (n : ℕ) : ‖project n f‖ = ‖(projection n).compLpL 2 gaussianProduct (F f)‖ := by
    exact F.norm_map _
  simpa only [he,F.norm_map] using hs

def graph (w : ℕ → ℝ) : Submodule ℝ (Field × Field) where
  carrier := {z | ∀ n, project n z.2 = w n • project n z.1}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro z t hz ht n
    simp only [Prod.fst_add,Prod.snd_add,map_add,hz n,ht n,smul_add]
  smul_mem' := by
    intro c z hz n
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,hz n,smul_smul,mul_comm]

theorem graph_isClosed (w : ℕ → ℝ) : IsClosed (graph w : Set (Field × Field)) := by
  have he : (graph w : Set (Field × Field)) = ⋂ n, {z | project n z.2 = w n • project n z.1} := by
    ext z; simp only [Set.mem_iInter,Set.mem_setOf_eq]; rfl
  rw [he]
  apply isClosed_iInter
  intro n
  exact isClosed_eq ((project n).continuous.comp continuous_snd)
    (((project n).continuous.comp continuous_fst).const_smul (w n))

theorem graph_functional (w : ℕ → ℝ) (z : Field × Field) (hz : z ∈ graph w) (h0 : z.1 = 0) :
    z.2 = 0 := by
  apply eq_of_clock_projections
  intro n
  change project n z.2 = project n 0
  rw [hz n,h0,map_zero,smul_zero]

def operator (w : ℕ → ℝ) : Field →ₗ.[ℝ] Field := (graph w).toLinearPMap

theorem operator_graph (w : ℕ → ℝ) : (operator w).graph = graph w :=
  Submodule.toLinearPMap_graph_eq _ (graph_functional w)

theorem operator_isClosed (w : ℕ → ℝ) : (operator w).IsClosed := by
  change IsClosed ((operator w).graph : Set (Field × Field))
  rw [operator_graph]
  exact graph_isClosed w



def weightedPartial (w : ℕ → ℝ) (N : ℕ) (f : Field) : Field :=
  ∑ n ∈ Finset.range (N+1), w n • project n f

theorem project_partial (w : ℕ → ℝ) (N n : ℕ) (f : Field) :
    project n (weightedPartial w N f) = if n ≤ N then w n • project n f else 0 := by
  classical
  simp only [weightedPartial,map_sum,map_smul,project_comp,smul_ite,smul_zero]
  simp [Finset.sum_ite_eq,Finset.mem_range]

theorem graph_energy (w : ℕ → ℝ) (f g : Field) (hfg : (f,g) ∈ graph w) :
    HasSum (fun n => (w n)^2*‖project n f‖^2) (‖g‖^2) := by
  have he (n : ℕ) : ‖project n g‖^2 = (w n)^2*‖project n f‖^2 := by
    rw [hfg n,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simpa only [he] using project_hasSum_norm_sq g

theorem partial_cauchy (w : ℕ → ℝ) (f : Field)
    (hs : Summable (fun n => (w n)^2*‖project n f‖^2)) :
    CauchySeq (fun N => weightedPartial w N f) := by
  have hb (p : ℕ × ℕ) (n : ℕ) :
      ‖project n (weightedPartial w p.1 f-weightedPartial w p.2 f)‖^2 ≤ (w n)^2*‖project n f‖^2 := by
    rw [map_sub,project_partial,project_partial]
    split_ifs <;> simp only [sub_self,sub_zero,zero_sub,norm_zero,norm_neg,
      norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,zero_pow (by norm_num : 2 ≠ 0)] <;> first | exact le_rfl | positivity
  have ht (n : ℕ) : Tendsto (fun p : ℕ × ℕ =>
      ‖project n (weightedPartial w p.1 f-weightedPartial w p.2 f)‖^2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n,n)] with p hp
    simp only [map_sub,project_partial,if_pos hp.1,if_pos hp.2,sub_self,norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)]
  have ht' := tendsto_tsum_of_dominated_convergence hs ht
    (Eventually.of_forall fun p n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hb p n)
  have he (p : ℕ × ℕ) : (∑' n, ‖project n (weightedPartial w p.1 f-weightedPartial w p.2 f)‖^2) =
      ‖weightedPartial w p.1 f-weightedPartial w p.2 f‖^2 := (project_hasSum_norm_sq _).tsum_eq
  simp only [he,tsum_zero] at ht'
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,dist_eq_norm] using hr

theorem graph_exists_iff (w : ℕ → ℝ) (f : Field) :
    (∃ g : Field, (f,g) ∈ graph w) ↔ Summable (fun n => (w n)^2*‖project n f‖^2) := by
  constructor
  · rintro ⟨g,hg⟩
    exact (graph_energy w f g hg).summable
  · intro hs
    obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete (partial_cauchy w f hs)
    refine ⟨g,fun n => ?_⟩
    have hl := (project n).continuous.tendsto g |>.comp hg
    have hc : Tendsto (fun N => project n (weightedPartial w N f)) atTop (𝓝 (w n • project n f)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with N hN
      rw [project_partial,if_pos hN]
    exact tendsto_nhds_unique hl hc



theorem operator_domain (w : ℕ → ℝ) (f : Field) :
    f ∈ (operator w).domain ↔ Summable (fun n => (w n)^2*‖project n f‖^2) := by
  rw [← graph_exists_iff]
  change f ∈ (graph w).map (LinearMap.fst ℝ Field Field) ↔ _
  constructor
  · rintro ⟨⟨x,y⟩,hxy,hx⟩
    change x=f at hx
    subst x
    exact ⟨y,hxy⟩
  · rintro ⟨g,hg⟩
    exact ⟨(f,g),hg,rfl⟩

theorem operator_projection (w : ℕ → ℝ) (f : (operator w).domain) (n : ℕ) :
    project n (operator w f) = w n • project n f := by
  have hg := (operator w).mem_graph f
  rw [operator_graph] at hg
  exact hg n

theorem operator_energy (w : ℕ → ℝ) (f : (operator w).domain) :
    HasSum (fun n => (w n)^2*‖project n f‖^2) (‖operator w f‖^2) := by
  apply graph_energy
  rw [← operator_graph]
  exact (operator w).mem_graph f

theorem truncation_eq (N : ℕ) (f : Field) :
    weightedPartial (fun _ => 1) N f = clockLift (truncation N) f := by
  rw [clock_truncation_eq]
  simp only [weightedPartial,one_smul,project]

theorem truncation_mem_domain (w : ℕ → ℝ) (N : ℕ) (f : Field) :
    clockLift (truncation N) f ∈ (operator w).domain := by
  rw [operator_domain,← graph_exists_iff]
  refine ⟨weightedPartial w N f,fun n => ?_⟩
  rw [← truncation_eq,project_partial,project_partial]
  split_ifs <;> simp only [one_smul,smul_zero]

theorem operator_dense_domain (w : ℕ → ℝ) : Dense ((operator w).domain : Set Field) := by
  intro f
  exact mem_closure_of_tendsto (clock_truncation_tendsto f)
    (Eventually.of_forall fun N => truncation_mem_domain w N f)

theorem partial_eq_output_truncation (w : ℕ → ℝ) (N : ℕ) (f : (operator w).domain) :
    weightedPartial w N f = clockLift (truncation N) (operator w f) := by
  apply eq_of_clock_projections
  intro n
  change project n (weightedPartial w N f) = project n (clockLift (truncation N) (operator w f))
  rw [← truncation_eq,project_partial,project_partial,operator_projection]
  split_ifs <;> simp only [one_smul]

theorem partial_tendsto_operator (w : ℕ → ℝ) (f : (operator w).domain) :
    Tendsto (fun N => weightedPartial w N f) atTop (𝓝 (operator w f)) := by
  simpa only [partial_eq_output_truncation] using clock_truncation_tendsto (operator w f)



theorem truncation_operator (w : ℕ → ℝ) (N : ℕ) (f : Field) :
    operator w ⟨clockLift (truncation N) f,truncation_mem_domain w N f⟩ = weightedPartial w N f := by
  apply eq_of_clock_projections
  intro n
  change project n (operator w _) = project n (weightedPartial w N f)
  rw [operator_projection]
  change w n • project n (clockLift (truncation N) f) = _
  rw [← truncation_eq,project_partial,project_partial]
  split_ifs <;> simp only [one_smul,smul_zero]

theorem graph_truncation_tendsto (w : ℕ → ℝ) (f : (operator w).domain) :
    Tendsto (fun N => (clockLift (truncation N) f,
      operator w ⟨clockLift (truncation N) f,truncation_mem_domain w N f⟩))
      atTop (𝓝 ((f:Field),operator w f)) := by
  simp only [truncation_operator]
  exact (clock_truncation_tendsto (f:Field)).prodMk_nhds (partial_tendsto_operator w f)

theorem project_mem_domain (w : ℕ → ℝ) (m : ℕ) (f : Field) :
    project m f ∈ (operator w).domain := by
  rw [operator_domain,← graph_exists_iff]
  refine ⟨w m • project m f,fun n => ?_⟩
  rw [map_smul,project_comp]
  by_cases hn : n=m
  · subst n; simp only [ite_true]
  · simp only [if_neg hn,smul_zero]

theorem operator_on_project (w : ℕ → ℝ) (m : ℕ) (f : Field) :
    operator w ⟨project m f,project_mem_domain w m f⟩ = w m • project m f := by
  apply eq_of_clock_projections
  intro n
  change project n (operator w _) = project n (w m • project m f)
  rw [operator_projection]
  change w n • project n (project m f) = _
  rw [map_smul,project_comp]
  by_cases hn : n=m
  · subst n; simp only [ite_true]
  · simp only [if_neg hn,smul_zero]

end OperatorDerivativeRewrite.Foundation.GaussianClockSpectralPowers
