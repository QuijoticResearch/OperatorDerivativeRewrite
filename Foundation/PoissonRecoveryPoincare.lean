import Foundation.PoissonDivergenceRecovery

/-! Full-domain sharp source Poincare and divergence coercivity from recovery. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonRecoveryPoincare
open PoissonDifferenceOperators PoissonMaximalOperators PoissonCharlierLadder
open PoissonCharlierHilbertBasis hiding coefficient
open PoissonDivergenceRecovery

theorem centered_zero_mode (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    coefficient rate hr (centered rate hr f) 0=0 :=
  (exists_divergence_iff_zero_mode rate hr _).mp ⟨recovery rate hr f,recovery_graph rate hr f⟩

theorem recovery_centered (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    recovery rate hr (centered rate hr f)=recovery rate hr f := by
  apply Eq.symm
  apply recovery_unique
  have he : centered rate hr (centered rate hr f)=centered rate hr f := by
    change centered rate hr f-coefficient rate hr (centered rate hr f) 0 • normalized rate hr 0= _
    rw [centered_zero_mode,zero_smul,sub_zero]
  simpa only [he] using recovery_graph rate hr f

theorem recovery_norm_le_centered (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    ‖recovery rate hr f‖ ≤ ‖centered rate hr f‖ := by
  rw [← recovery_centered]
  exact recovery_norm_le rate hr _

theorem centered_pairing (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    inner ℝ f (centered rate hr f)=‖centered rate hr f‖^2 := by
  have hz := centered_zero_mode rate hr f
  have he : f=centered rate hr f+coefficient rate hr f 0 • normalized rate hr 0 := by
    simp only [centered,sub_add_cancel]
  calc
    _ = inner ℝ (centered rate hr f+coefficient rate hr f 0 • normalized rate hr 0)
        (centered rate hr f) := congrArg (fun v => inner ℝ v (centered rate hr f)) he
    _ = ‖centered rate hr f‖^2 := by
      rw [inner_add_left,real_inner_smul_left]
      change inner ℝ (centered rate hr f) (centered rate hr f)+
        coefficient rate hr f 0*coefficient rate hr (centered rate hr f) 0= _
      rw [hz,mul_zero,add_zero,real_inner_self_eq_norm_sq]

theorem poincare (rate : ℝ≥0) (hr : 0 < rate) {f : ScalarL2 rate} {g : FieldL2 rate}
    (hf : (f,g) ∈ (maximalDifference rate hr).graph) :
    ‖centered rate hr f‖ ≤ ‖g‖ := by
  have hi := graph_duality rate hr hf (recovery_graph rate hr f)
  rw [centered_pairing] at hi
  have hb := real_inner_le_norm g (recovery rate hr f)
  have hn := recovery_norm_le_centered rate hr f
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg g)
  rw [hi] at hb
  nlinarith [norm_nonneg g,norm_nonneg (centered rate hr f)]

theorem divergence_coercive (rate : ℝ≥0) (hr : 0 < rate) {u : FieldL2 rate} {f : ScalarL2 rate}
    (hu : (u,f) ∈ (maximalDivergence rate hr).graph) : ‖u‖ ≤ ‖f‖ := by
  have hz := (exists_divergence_iff_zero_mode rate hr f).mp ⟨u,hu⟩
  have hg : (u,centered rate hr f) ∈ (maximalDivergence rate hr).graph := by
    simpa only [centered,hz,zero_smul,sub_zero] using hu
  rw [recovery_unique rate hr f u hg]
  exact recovery_norm_le rate hr f

theorem centered_first_normalized (rate : ℝ≥0) (hr : 0 < rate) :
    centered rate hr (normalized rate hr 1)=normalized rate hr 1 := by
  have hz : coefficient rate hr (normalized rate hr 1) 0=0 := by
    simpa only [coefficient] using (normalized_orthonormal rate hr).2 (by norm_num : (0 : ℕ)≠1)
  simp only [centered,hz,zero_smul,sub_zero]

theorem normalized_first_lowering_graph (rate : ℝ≥0) (hr : 0 < rate) :
    (normalized rate hr 1,normalizedField rate hr 0) ∈ (maximalDifference rate hr).graph := by
  have hg := (maximalDifference rate hr).graph.smul_mem (normalizer rate 1)⁻¹
    (lowering_graph rate hr 0)
  simpa [normalized,normalizedField,normalizer] using hg

theorem poincare_equality_first_mode (rate : ℝ≥0) (hr : 0 < rate) :
    ‖centered rate hr (normalized rate hr 1)‖=‖normalizedField rate hr 0‖ := by
  rw [centered_first_normalized,(normalized_orthonormal rate hr).1,
    (normalizedField_orthonormal rate hr).1]

end OperatorDerivativeRewrite.Foundation.PoissonRecoveryPoincare
