import Foundation.GaussianSpectralPoincare

/-! A bounded source-divergence recovery operator on all centered Gaussian L2,
assembled from the verified complete number sectors and closed graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianDivergenceRecovery
open InfiniteGaussian GaussianNumberSectors

def inverseGradientComponent (f : GaussianL2) (n : ℕ) : (gradient n).range :=
  (n : ℝ)⁻¹ • gradientComponent f n

theorem inverseGradient_norm_sq (f : GaussianL2) (n : ℕ) :
    ‖inverseGradientComponent f n‖^2 = (n : ℝ)⁻¹*‖projection n f‖^2 := by
  change ‖(n : ℝ)⁻¹ • projectedGradient n f‖^2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, projectedGradient_energy]
  by_cases hn : n=0
  · simp [hn]
  · have hp : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have he : (n : ℝ)⁻¹^2*(n : ℝ) = (n : ℝ)⁻¹ := by field_simp
    rw [← mul_assoc, he]

theorem inverseGradient_norm_sq_le (f : GaussianL2) (n : ℕ) :
    ‖inverseGradientComponent f n‖^2 ≤ ‖projection n f‖^2 := by
  change ‖(n : ℝ)⁻¹ • projectedGradient n f‖^2 ≤ _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, projectedGradient_energy]
  by_cases hn : n=0
  · simp [hn]
  · have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have he : (n : ℝ)⁻¹^2*(n : ℝ) = (n : ℝ)⁻¹ := by field_simp
    rw [← mul_assoc, he]
    exact mul_le_of_le_one_left (sq_nonneg _) (inv_le_one_of_one_le₀ h1)

theorem inverseGradient_summable (f : GaussianL2) :
    Summable (fun n => ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)) := by
  have hn : Summable (fun n => ‖inverseGradientComponent f n‖^2) :=
    (projection_hasSum_norm_sq f).summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (inverseGradient_norm_sq_le f)
  exact (gradient_ranges_orthogonal.summable_iff_norm_sq_summable
    (inverseGradientComponent f)).mpr hn

def recovery (f : GaussianL2) : GaussianVectorL2 :=
  ∑' n, ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)

def centeredComponent (f : GaussianL2) (n : ℕ) : GaussianL2 :=
  projection n f - if n=0 then projection 0 f else 0

theorem centeredComponent_hasSum (f : GaussianL2) :
    HasSum (centeredComponent f) (f-projection 0 f) :=
  (projection_hasSum f).sub (hasSum_ite_eq 0 (projection 0 f))

theorem inverseGradient_divergence_graph (f : GaussianL2) (n : ℕ) :
    (((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2),
      centeredComponent f n) ∈ hilbertDivergence.graph := by
  have hg := hilbertDivergence.graph.smul_mem (n : ℝ)⁻¹ (projectedGradient_graph n f).2
  change ((n : ℝ)⁻¹ • projectedGradient n f,
    (n : ℝ)⁻¹ • ((n : ℝ) • projection n f)) ∈ _ at hg
  change ((n : ℝ)⁻¹ • projectedGradient n f, _) ∈ _
  by_cases hn : n=0
  · simpa [hn, centeredComponent] using hg
  · simpa [centeredComponent, hn, smul_smul, inv_mul_cancel₀
      (show (n : ℝ) ≠ 0 by exact_mod_cast hn)] using hg

/-- Every centered L2 target has an actual full source-divergence preimage;
no Malliavin differentiability hypothesis on the target is needed. -/
theorem recovery_graph (f : GaussianL2) :
    (recovery f, f-projection 0 f) ∈ hilbertDivergence.graph := by
  have hi := (inverseGradient_summable f).hasSum
  change HasSum (fun n => ((inverseGradientComponent f n : (gradient n).range) :
    GaussianVectorL2)) (recovery f) at hi
  apply hilbertDivergence_isClosed.mem_of_tendsto (hi.prodMk_nhds (centeredComponent_hasSum f))
  exact Eventually.of_forall fun s => by
    change (∑ n ∈ s, ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2),
      ∑ n ∈ s, centeredComponent f n) ∈ hilbertDivergence.graph
    rw [prod_mk_sum]
    exact hilbertDivergence.graph.sum_mem
      (fun n (_ : n ∈ s) => inverseGradient_divergence_graph f n)

theorem recovery_energy_hasSum (f : GaussianL2) :
    HasSum (fun n => ‖inverseGradientComponent f n‖^2) (‖recovery f‖^2) := by
  have h := (inverseGradient_summable f).hasSum.norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ n ∈ s,
    ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)‖^2)
    atTop (𝓝 (‖recovery f‖^2)) at h
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, ‖inverseGradientComponent f n‖^2)
    atTop (𝓝 (‖recovery f‖^2))
  have he : (fun s : Finset ℕ => ∑ n ∈ s, ‖inverseGradientComponent f n‖^2) =
      (fun s : Finset ℕ => ‖∑ n ∈ s,
        ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)‖^2) := by
    funext s
    exact (gradient_ranges_orthogonal.norm_sum (inverseGradientComponent f) s).symm
  rw [he]
  exact h

theorem recovery_norm_le (f : GaussianL2) : ‖recovery f‖ ≤ ‖f‖ := by
  have h := hasSum_le (inverseGradient_norm_sq_le f)
    (recovery_energy_hasSum f) (projection_hasSum_norm_sq f)
  nlinarith [norm_nonneg (recovery f), norm_nonneg f]

theorem recovery_inverse_energy_hasSum (f : GaussianL2) :
    HasSum (fun n : ℕ => (n : ℝ)⁻¹*‖projection n f‖^2) (‖recovery f‖^2) := by
  simpa only [inverseGradient_norm_sq] using recovery_energy_hasSum f

theorem recovery_add (f g : GaussianL2) : recovery (f+g) = recovery f+recovery g := by
  apply (inverseGradient_summable (f+g)).hasSum.unique
  have hs := (inverseGradient_summable f).hasSum.add (inverseGradient_summable g).hasSum
  change HasSum (fun n => ((inverseGradientComponent f n : (gradient n).range) :
    GaussianVectorL2) + ((inverseGradientComponent g n : (gradient n).range) :
    GaussianVectorL2)) (recovery f+recovery g) at hs
  have he : (fun n => ((inverseGradientComponent (f+g) n : (gradient n).range) :
      GaussianVectorL2)) = (fun n => ((inverseGradientComponent f n : (gradient n).range) :
      GaussianVectorL2) + ((inverseGradientComponent g n : (gradient n).range) :
      GaussianVectorL2)) := by
    funext n
    change (n : ℝ)⁻¹ • projectedGradient n (f+g) =
      (n : ℝ)⁻¹ • projectedGradient n f + (n : ℝ)⁻¹ • projectedGradient n g
    simp only [map_add, smul_add]
  rw [he]
  exact hs

theorem recovery_smul (c : ℝ) (f : GaussianL2) : recovery (c • f) = c • recovery f := by
  apply (inverseGradient_summable (c • f)).hasSum.unique
  have hs := (inverseGradient_summable f).hasSum.const_smul c
  change HasSum (fun n => c • ((inverseGradientComponent f n : (gradient n).range) :
    GaussianVectorL2)) (c • recovery f) at hs
  have he : (fun n => ((inverseGradientComponent (c • f) n : (gradient n).range) :
      GaussianVectorL2)) = (fun n => c • ((inverseGradientComponent f n : (gradient n).range) :
      GaussianVectorL2)) := by
    funext n
    change (n : ℝ)⁻¹ • projectedGradient n (c • f) = c • ((n : ℝ)⁻¹ • projectedGradient n f)
    rw [map_smul, smul_comm]
  rw [he]
  exact hs

def recoveryOperator : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  ({ toFun := recovery, map_add' := recovery_add, map_smul' := recovery_smul } :
    GaussianL2 →ₗ[ℝ] GaussianVectorL2).mkContinuous 1
      (fun f => by
        change ‖recovery f‖ ≤ 1*‖f‖
        simpa only [one_mul] using recovery_norm_le f)

/-- Recovery is perpendicular to every divergence-free field. This is the
operator analogue of selecting a gradient potential instead of a solenoidal part. -/
theorem recovery_orthogonal_kernel (f : GaussianL2) (u : GaussianVectorL2)
    (hu : (u,0) ∈ hilbertDivergence.graph) : inner ℝ u (recovery f) = 0 := by
  have hs := (inverseGradient_summable f).hasSum.map
    (innerSL ℝ u).toAddMonoidHom (innerSL ℝ u).continuous
  change HasSum (fun n => inner ℝ u
    ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2))
    (inner ℝ u (recovery f)) at hs
  have he (n : ℕ) : inner ℝ u
      ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2) = 0 := by
    have hd := GaussianNumberSectors.graph_duality (projectedGradient_graph n f).1 hu
    rw [inner_zero_right] at hd
    change inner ℝ u ((n : ℝ)⁻¹ • projectedGradient n f) = 0
    rw [inner_smul_right, real_inner_comm (projectedGradient n f) u, hd, mul_zero]
  have h0 : HasSum (fun n : ℕ => inner ℝ u
      ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)) 0 := by
    simpa only [he] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  exact hs.unique h0

theorem recovery_minimal_norm (f : GaussianL2) (u : GaussianVectorL2)
    (hu : (u,f-projection 0 f) ∈ hilbertDivergence.graph) : ‖recovery f‖ ≤ ‖u‖ := by
  have hk : (u-recovery f,0) ∈ hilbertDivergence.graph := by
    simpa only [Prod.mk_sub_mk, sub_self] using
      hilbertDivergence.graph.sub_mem hu (recovery_graph f)
  have ho := recovery_orthogonal_kernel f (u-recovery f) hk
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have hn := norm_sub_sq_real u (recovery f)
  nlinarith [sq_nonneg ‖u-recovery f‖, norm_nonneg u, norm_nonneg (recovery f)]

/-- The full source divergence range is precisely the centered subspace.
This asserts no predictable representation or intrinsic observable domain. -/
theorem exists_divergence_iff_centered (f : GaussianL2) :
    (∃ u : GaussianVectorL2, (u,f) ∈ hilbertDivergence.graph) ↔
      inner ℝ gaussianOne f = 0 := by
  constructor
  · rintro ⟨u,hu⟩
    have hd := GaussianNumberSectors.graph_duality (closedDerivative_constant_graph 1) hu
    simpa only [inner_zero_left, one_smul] using hd.symm
  · intro hf
    refine ⟨recovery f, ?_⟩
    have hg := recovery_graph f
    rw [projection_zero, hf, zero_smul, sub_zero] at hg
    exact hg

/-- The adjoint of this bounded divergence recovery recovers a centered
potential from its full derivative. It is an inverse derivative, not D itself. -/
theorem recovery_adjoint_derivative {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f,g) ∈ closedCylindricalDerivative.graph) :
    recoveryOperator.adjoint g = f-projection 0 f := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ g (recovery k) = inner ℝ (f-projection 0 f) k
  rw [GaussianNumberSectors.graph_duality hf (recovery_graph k), inner_sub_right,
    inner_sub_left]
  have hp := (sector 0).inner_starProjection_left_eq_right f k
  change inner ℝ (projection 0 f) k = inner ℝ f (projection 0 k) at hp
  rw [hp]

end OperatorDerivativeRewrite.Foundation.GaussianDivergenceRecovery
