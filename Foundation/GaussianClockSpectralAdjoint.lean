import Foundation.GaussianClockSpectralPowers
/-! Exact Hilbert adjoints and integration by parts for the ORIGINAL clock
spectral multipliers, including unbounded real weights and their maximal domains.
The domain and graph core are the already constructed genuine L2 ones. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockSpectralAdjoint
open InfiniteGaussian GaussianClockValueOperators GaussianClockSpectralPowers
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem inner_hasSum (f g : Field) :
    HasSum (fun n => inner ℝ (project n f) (project n g)) (inner ℝ f g) := by
  have hs := (((project_hasSum_norm_sq (f+g)).sub (project_hasSum_norm_sq f)).sub
    (project_hasSum_norm_sq g)).div_const 2
  have he (n : ℕ) : (‖project n (f+g)‖^2-‖project n f‖^2-‖project n g‖^2)/2 =
      inner ℝ (project n f) (project n g) := by
    rw [map_add,norm_add_sq_real]
    ring
  have hf : (‖f+g‖^2-‖f‖^2-‖g‖^2)/2 = inner ℝ f g := by rw [norm_add_sq_real]; ring
  simpa only [he,hf] using hs

theorem project_inner (n : ℕ) (f g : Field) :
    inner ℝ (project n f) g = inner ℝ f (project n g) := by
  have he (k : ℕ) : inner ℝ (project k (project n f)) (project k g) =
      inner ℝ (project k f) (project k (project n g)) := by
    rw [project_comp,project_comp]
    split_ifs <;> simp only [inner_zero_left,inner_zero_right]
  apply (inner_hasSum (project n f) g).unique
  simpa only [he] using inner_hasSum f (project n g)

theorem graph_inner (w : ℕ → ℝ) (f a g b : Field)
    (hfa : (f,a) ∈ graph w) (hgb : (g,b) ∈ graph w) :
    inner ℝ a g = inner ℝ f b := by
  have he (n : ℕ) : inner ℝ (project n a) (project n g) =
      inner ℝ (project n f) (project n b) := by
    rw [hfa n,hgb n,real_inner_smul_left,real_inner_smul_right]
  apply (inner_hasSum a g).unique
  simpa only [he] using inner_hasSum f b

theorem graph_adjoint (w : ℕ → ℝ) : (graph w).adjoint = graph w := by
  ext z
  constructor
  · intro hz n
    apply ext_inner_left ℝ
    intro f
    have hp : (project n f,w n • project n f) ∈ graph w := by
      have hg := (operator w).mem_graph ⟨project n f,project_mem_domain w n f⟩
      rw [operator_graph,operator_on_project] at hg
      exact hg
    have ht := (Submodule.mem_adjoint_iff _ _).1 hz _ _ hp
    rw [real_inner_smul_left,project_inner,project_inner] at ht
    rw [real_inner_smul_right]
    linarith
  · intro hz
    rw [Submodule.mem_adjoint_iff]
    intro f a hfa
    exact sub_eq_zero.mpr (graph_inner w f a z.1 z.2 hfa hz)

theorem operator_adjoint (w : ℕ → ℝ) : (operator w).adjoint = operator w := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (operator_dense_domain w),operator_graph,graph_adjoint]

theorem operator_ibp (w : ℕ → ℝ) (f g : (operator w).domain) :
    inner ℝ (operator w f) (g:Field) = inner ℝ (f:Field) (operator w g) := by
  apply graph_inner
  · rw [← operator_graph]; exact (operator w).mem_graph f
  · rw [← operator_graph]; exact (operator w).mem_graph g



theorem operator_pairing_hasSum (w : ℕ → ℝ) (f : (operator w).domain) (g : Field) :
    HasSum (fun n => w n*inner ℝ (project n f) (project n g)) (inner ℝ (operator w f) g) := by
  have hs := inner_hasSum (operator w f) g
  simpa only [operator_projection,real_inner_smul_left] using hs

theorem operator_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (f : (operator w).domain) :
    0 ≤ inner ℝ (operator w f) (f:Field) := by
  have hs := operator_pairing_hasSum w f (f:Field)
  apply hasSum_le _ hasSum_zero hs
  intro n
  rw [real_inner_self_eq_norm_sq]
  exact mul_nonneg (hw n) (sq_nonneg _)

end OperatorDerivativeRewrite.Foundation.GaussianClockSpectralAdjoint
