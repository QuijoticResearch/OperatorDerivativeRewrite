import Foundation.GaussianAbsoluteMinimumGraph
import Foundation.IBMSingleFourierClockGraph

/-! Actual folded Brownian covariances, including collision levels, belong to
the original closed Gaussian clock graph. This is an ambient clock derivative,
not a claim of intrinsic IBM observability. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMMultitimeClockVarianceGraph
open InfiniteGaussian GaussianTimeProcess IBMSingleFourierClockGraph

def foldedGradient (R : ℝ≥0) (Y : SampleSpace) : CoefficientSpace :=
  BrownianSignIntegral.signum (process R Y) • clockGradient R Y

def overlapGradient (R S : ℝ≥0) (Y : SampleSpace) : CoefficientSpace :=
  (1 / 2 : ℝ) • (foldedGradient R Y + foldedGradient S Y -
    BrownianSignIntegral.signum (|process R Y| - |process S Y|) •
      (foldedGradient R Y - foldedGradient S Y))

theorem overlapGradient_self (R : ℝ≥0) (Y : SampleSpace) :
    overlapGradient R R Y = foldedGradient R Y := by
  simp only [overlapGradient, sub_self, BrownianSignIntegral.signum_zero,
    zero_smul, sub_zero]
  module

theorem folded_graph (R : ℝ≥0) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun Y => |process R Y|) ∧
      G =ᵐ[gaussianProduct] foldedGradient R ∧ ‖G‖ ≤ Real.sqrt (R : ℝ) := by
  obtain ⟨F, G, hg, hf, hd, hn⟩ := GaussianAbsoluteMinimumGraph.absolute_graph
    (wienerL2 R) (clockGradient R) (clock_graph R)
  exact ⟨F, G, hg, hf, hd, hn.trans (clockGradient_norm R).le⟩

theorem overlap_graph (R S : ℝ≥0) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun Y => min |process R Y| |process S Y|) ∧
      G =ᵐ[gaussianProduct] overlapGradient R S ∧
      ‖G‖ ≤ Real.sqrt (R : ℝ) + Real.sqrt (S : ℝ) := by
  obtain ⟨F, G, hfg, hf, hg, hn⟩ := folded_graph R
  obtain ⟨H, K, hhk, hh, hk, hkn⟩ := folded_graph S
  obtain ⟨A, B, hab, ha, hb, hbn⟩ :=
    GaussianAbsoluteMinimumGraph.minimum_graph F H G K hfg hhk
  refine ⟨A, B, hab, ?_, ?_, hbn.trans (add_le_add hn hkn)⟩
  · filter_upwards [ha, hf, hh] with Y ha hf hh
    rw [ha, hf, hh]
  · filter_upwards [hb, hf, hh, hg, hk] with Y hb hf hh hg hk
    rw [hb, hf, hh, hg, hk]
    rfl

variable {ι : Type*} [Fintype ι]

def varianceGradient (b : ι → ℝ) (r : ι → ℝ≥0) (Y : SampleSpace) :
    CoefficientSpace := ∑ i, ∑ j, (b i * b j) • overlapGradient (r i) (r j) Y

def varianceCost (b : ι → ℝ) (r : ι → ℝ≥0) : ℝ :=
  ∑ i, ∑ j, |b i * b j| * (Real.sqrt (r i : ℝ) + Real.sqrt (r j : ℝ))

theorem varianceCost_bound (b : ι → ℝ) (r : ι → ℝ≥0) :
    varianceCost b r ≤ 2 * (IBMUniformRidgeNativeBounds.amplitude b) ^ 2 *
      ∑ i, Real.sqrt (r i : ℝ) := by
  classical
  let S := ∑ i, Real.sqrt (r i : ℝ)
  have hs (i : ι) : Real.sqrt (r i : ℝ) ≤ S :=
    Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (r j : ℝ)) (Finset.mem_univ i)
  calc
    varianceCost b r ≤ ∑ i, ∑ j, |b i| * |b j| * (2 * S) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      linarith [hs i, hs j]
    _ = (∑ i, |b i|) * (∑ j, |b j|) * (2 * S) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      dsimp [IBMUniformRidgeNativeBounds.amplitude, S]
      ring

theorem variance_graph (b : ι → ℝ) (r : ι → ℝ≥0) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct]
        (fun Y => IBMFoldedSourceCovariance.variance b (fun i => process (r i) Y)) ∧
      G =ᵐ[gaussianProduct] varianceGradient b r ∧ ‖G‖ ≤ varianceCost b r := by
  classical
  choose F G hgraph hF hG hbound using fun i j => overlap_graph (r i) (r j)
  let A : GaussianL2 := ∑ i, ∑ j, (b i * b j) • F i j
  let B : GaussianVectorL2 := ∑ i, ∑ j, (b i * b j) • G i j
  have hab : (A, B) ∈ closedCylindricalDerivative.graph := by
    convert closedCylindricalDerivative.graph.sum_mem (fun i (_ : i ∈ Finset.univ) =>
      closedCylindricalDerivative.graph.sum_mem (fun j (_ : j ∈ Finset.univ) =>
        closedCylindricalDerivative.graph.smul_mem (b i * b j) (hgraph i j))) using 1 <;>
      simp only [A, B, prod_mk_sum] <;> rfl
  have hA : A =ᵐ[gaussianProduct] (fun Y =>
      IBMFoldedSourceCovariance.variance b (fun i => process (r i) Y)) := by
    have ho := Lp.coeFn_finsetSum Finset.univ (fun i => ∑ j, (b i * b j) • F i j)
    have hi := fun i => Lp.coeFn_finsetSum Finset.univ (fun j => (b i * b j) • F i j)
    have hs := fun i j => Lp.coeFn_smul (b i * b j) (F i j)
    filter_upwards [ho, ae_all_iff.mpr hi,
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hs i),
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hF i)] with Y ho hi hs hf
    rw [IBMFoldedSourceCovariance.variance_expansion]
    change (∑ i, ∑ j, (b i * b j) • F i j) Y = _
    rw [ho]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs i j, Pi.smul_apply, hf i j, smul_eq_mul]
  have hB : B =ᵐ[gaussianProduct] varianceGradient b r := by
    have ho := Lp.coeFn_finsetSum Finset.univ (fun i => ∑ j, (b i * b j) • G i j)
    have hi := fun i => Lp.coeFn_finsetSum Finset.univ (fun j => (b i * b j) • G i j)
    have hs := fun i j => Lp.coeFn_smul (b i * b j) (G i j)
    filter_upwards [ho, ae_all_iff.mpr hi,
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hs i),
      ae_all_iff.mpr fun i => ae_all_iff.mpr (hG i)] with Y ho hi hs hg
    change (∑ i, ∑ j, (b i * b j) • G i j) Y = _
    rw [ho]
    simp only [Finset.sum_apply, varianceGradient]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs i j, Pi.smul_apply, hg i j]
  refine ⟨A, B, hab, hA, hB, ?_⟩
  change ‖∑ i, ∑ j, (b i * b j) • G i j‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hbound i j) (abs_nonneg _)

def dampingGradient (b : ι → ℝ) (r : ι → ℝ≥0) (Y : SampleSpace) :
    CoefficientSpace :=
  GaussianReflectedDampingGraph.coefficient (1 / 2)
    (IBMFoldedSourceCovariance.variance b (fun i => process (r i) Y)) •
      varianceGradient b r Y

theorem damping_graph (b : ι → ℝ) (r : ι → ℝ≥0) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun Y => Real.exp
        (-IBMFoldedSourceCovariance.variance b (fun i => process (r i) Y) / 2)) ∧
      G =ᵐ[gaussianProduct] dampingGradient b r ∧
      ‖G‖ ≤ varianceCost b r / 2 := by
  obtain ⟨A, B, hab, ha, hb, hbn⟩ := variance_graph b r
  obtain ⟨F, G, hfg, hf, hg, hn⟩ := GaussianReflectedDampingGraph.closed_graph
    (by norm_num : (0 : ℝ) ≤ 1 / 2) A B hab
  refine ⟨F, G, hfg, ?_, ?_, ?_⟩
  · filter_upwards [hf, ha] with Y hf ha
    rw [hf, ha, GaussianReflectedDampingGraph.value,
      abs_of_nonneg (IBMFoldedSourceCovariance.variance_nonneg _ _)]
    congr 1
    ring
  · filter_upwards [hg, ha, hb] with Y hg ha hb
    rw [hg, ha, hb]
    rfl
  · linarith

end OperatorDerivativeRewrite.Foundation.IBMMultitimeClockVarianceGraph
