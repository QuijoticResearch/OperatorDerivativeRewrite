import Foundation.IBMNonlinearSceneryCovariance

/-! Actual measurable nonlinear source columns for the sine clock gradient.
The old continuous scenery modifications supply the joint representative;
the old derivative column supplies L2 membership and fixed-mollifier bounds. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockColumn
open InfiniteGaussian IBMClockAverageCandidate IBMGaussianSteinMoments
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def value (n : ℕ) (r : ℝ) (ω : SampleSpace) : ℝ :=
  Real.cos (IBMDyadicExtension.field n 0 ω r)*IBMDyadicExtension.field n 1 ω r

theorem value_measurable (n : ℕ) :
    Measurable (fun p : ℝ × SampleSpace => value n p.1 p.2) :=
  (Real.continuous_cos.measurable.comp (IBMDyadicExtension.field_jointly_measurable n 0)).mul
    (IBMDyadicExtension.field_jointly_measurable n 1)

theorem value_memLp (n : ℕ) (r : ℝ) : MemLp (value n r) 2 gaussianProduct := by
  change MemLp (fun ω => Real.cos (IBMDyadicExtension.field n 0 ω r)*
    IBMDyadicExtension.field n 1 ω r) 2 gaussianProduct
  have h1 : MemLp (fun ω => IBMDyadicExtension.field n 1 ω r) 2 gaussianProduct :=
    (memLp_congr_ae (sourceColumn_actual_ae n r)).mp (Lp.memLp (sourceColumn n r))
  have h0 : MemLp (fun ω => Real.cos (IBMDyadicExtension.field n 0 ω r)) ∞ gaussianProduct :=
    MemLp.of_bound ((Real.continuous_cos.measurable.comp
      (IBMDyadicExtension.field_coordinate_measurable n 0 r)).aestronglyMeasurable) 1
        (ae_of_all _ fun ω => Real.abs_cos_le_one _)
  simpa only [smul_eq_mul] using (smul_memLp (p := ∞) (q := 2) (r := 2) h0 h1)

def column (n : ℕ) (r : ℝ) : GaussianL2 :=
  ProductL2Sections.sectionL2 gaussianProduct (fun p : ℝ × SampleSpace => value n p.1 p.2) r

theorem column_actual_ae (n : ℕ) (r : ℝ) : column n r =ᵐ[gaussianProduct] value n r :=
  ProductL2Sections.sectionL2_coeFn gaussianProduct _ r (value_memLp n r)

theorem column_stronglyMeasurable (n : ℕ) : StronglyMeasurable (column n) :=
  ProductL2Sections.sectionL2_stronglyMeasurable gaussianProduct _
    (value_measurable n).stronglyMeasurable

theorem column_firstChaos_ae (n : ℕ) (r : ℝ) : column n r =ᵐ[gaussianProduct]
    (fun ω => Real.cos (firstChaosEmbedding (tripleCoefficient n r 0) ω)*
      firstChaosEmbedding (tripleCoefficient n r 1) ω) := by
  filter_upwards [column_actual_ae n r, IBMDyadicExtension.field_coordinate_ae n 0 r,
    IBMDyadicExtension.field_coordinate_ae n 1 r] with ω hc h0 h1
  rw [hc]
  change Real.cos (IBMDyadicExtension.field n 0 ω r)*IBMDyadicExtension.field n 1 ω r = _
  rw [h0,h1,gaussianTriple_eq_firstChaos,gaussianTriple_eq_firstChaos]

theorem column_norm_le (n : ℕ) (r : ℝ) : ‖column n r‖ ≤ ‖sourceColumn n r‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [column_actual_ae n r,sourceColumn_actual_ae n r] with ω hc hd
  rw [hc,hd]
  change ‖Real.cos (IBMDyadicExtension.field n 0 ω r)*IBMDyadicExtension.field n 1 ω r‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)).trans_eq (one_mul _)

theorem column_bounded (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖column n r‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := sourceColumn_bounded n
  exact ⟨C,hC,fun r => (column_norm_le n r).trans (hb r)⟩

theorem column_inner_bound (n m : ℕ) (r q : ℝ) :
    |inner ℝ (column n r) (column m q)| ≤ IBMFoldedTransitionBound.overlap n m r q+4 := by
  have he : inner ℝ (column n r) (column m q) =
      ∫ ω, firstChaosEmbedding (tripleCoefficient n r 1) ω*
        firstChaosEmbedding (tripleCoefficient m q 1) ω*
          Real.cos (firstChaosEmbedding (tripleCoefficient n r 0) ω)*
            Real.cos (firstChaosEmbedding (tripleCoefficient m q 0) ω) ∂gaussianProduct := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [column_firstChaos_ae n r,column_firstChaos_ae m q] with ω hn hm
    rw [hn,hm,Real.inner_apply]
    ring
  rw [he]
  exact IBMNonlinearSceneryCovariance.nonlinear_source_bound n m r q

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockColumn
