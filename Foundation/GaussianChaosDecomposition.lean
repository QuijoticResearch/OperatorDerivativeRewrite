import Foundation.GaussianNumberHermite

/-! A complete all-orders orthogonal Gaussian decomposition, constructed from
the actual number-operator sectors and the verified finite Hermite density. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian

theorem sector_orthogonalFamily :
    OrthogonalFamily ℝ (fun n => sector n) (fun n => (sector n).subtypeₗᵢ) := by
  intro n m hnm f g
  exact sectors_orthogonal hnm f g

theorem sector_isHilbertSum :
    IsHilbertSum ℝ (fun n => sector n) (fun n => (sector n).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal sector sector_orthogonalFamily (by rw [sector_total])

def coefficients : GaussianL2 ≃ₗᵢ[ℝ] lp (fun n => sector n) 2 :=
  sector_isHilbertSum.linearIsometryEquiv

theorem coefficients_eq_projection (f : GaussianL2) (n : ℕ) :
    coefficients f n = (sector n).orthogonalProjectionOnto f := by
  apply ext_inner_left ℝ
  intro g
  have h := coefficients.symm.inner_map_map (lp.single 2 n g) (coefficients f)
  have hs : coefficients.symm (lp.single 2 n g) = g :=
    sector_isHilbertSum.linearIsometryEquiv_symm_apply_single g
  rw [hs, coefficients.symm_apply_apply, lp.inner_single_left] at h
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact h.symm

theorem projection_hasSum (f : GaussianL2) : HasSum (fun n => projection n f) f := by
  have h := sector_isHilbertSum.hasSum_linearIsometryEquiv_symm (coefficients f)
  change HasSum (fun n => ((coefficients f n : sector n) : GaussianL2))
    (coefficients.symm (coefficients f)) at h
  simpa only [coefficients_eq_projection, coefficients.symm_apply_apply, projection,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using h

theorem projection_hasSum_norm_sq (f : GaussianL2) :
    HasSum (fun n => ‖projection n f‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (coefficients f)
  have hn (n : ℕ) : ‖projection n f‖ = ‖(sector n).orthogonalProjectionOnto f‖ := rfl
  simp_rw [hn]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, coefficients.norm_map,
    coefficients_eq_projection] using h

def truncation (N : ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  ∑ n ∈ Finset.range (N + 1), projection n

theorem truncation_tendsto (f : GaussianL2) :
    Tendsto (fun N => truncation N f) atTop (𝓝 f) := by
  have h := (projection_hasSum f).tendsto_sum_nat
  simpa only [truncation, ContinuousLinearMap.sum_apply, Function.comp_def] using
    h.comp (tendsto_add_atTop_nat 1)

theorem sector_zero_iff (f : GaussianL2) :
    f ∈ sector 0 ↔ f = inner ℝ gaussianOne f • gaussianOne := by
  constructor
  · intro hf
    have hg := gradient_graph 0 ⟨f, hf⟩
    have hn := gradient_norm 0 ⟨f, hf⟩
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, norm_eq_zero] at hn
    have hd := hg.1
    rw [hn] at hd
    exact (closedDerivative_zero_iff_vacuum f).mp hd
  · intro hf
    apply (mem_sector 0 f).mpr
    refine ⟨0, (closedDerivative_zero_iff_vacuum f).mpr hf, ?_⟩
    simpa using hilbertDivergence.graph.zero_mem

theorem projection_zero (f : GaussianL2) : projection 0 f = inner ℝ gaussianOne f • gaussianOne := by
  have h := (sector_zero_iff _).mp (projection_mem 0 f)
  have ho : gaussianOne ∈ sector 0 := by
    apply (mem_sector 0 _).mpr
    refine ⟨0, ?_, ?_⟩
    · simpa only [one_smul] using closedDerivative_constant_graph 1
    · simpa using hilbertDivergence.graph.zero_mem
  have hi := (sector 0).inner_orthogonalProjectionOnto_eq_of_mem_left ⟨gaussianOne, ho⟩ f
  change inner ℝ gaussianOne (projection 0 f) = inner ℝ gaussianOne f at hi
  rwa [hi] at h

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
