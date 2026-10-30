import Foundation.CubeLimitKernelSymmetry
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Weighted Schur control on the actual original-coordinate limiting kernel. -/
noncomputable section
open MeasureTheory Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianSchurBound
open CubeChartAction CubeGaussianGroundEigenvector CubeGaussianRootGround
open CubeCompressedNormLimit CubeLimitKernelSymmetry CubeBoundaryChartL2 CubeKernelOperatorBound
attribute [local irreducible] CubeBoundaryHaarL2.limit actualState

private theorem state_positive (X : Boundary) : 0 < actualState X := by
  unfold actualState
  exact gaussianState_positive (CubeGaussianModes.analysis X)

def energy (F : EuclideanL2) (p : Boundary × Boundary) : ℝ :=
  (F p.1)^2/actualState p.1*(CubeBoundaryHaarL2.limit p*actualState p.2)

theorem energy_nonnegative (F : EuclideanL2) (p : Boundary × Boundary) : 0 ≤ energy F p :=
  mul_nonneg (div_nonneg (sq_nonneg _) (state_positive p.1).le)
    (mul_nonneg (CubeBoundaryHaarL2.limit_nonnegative p) (state_positive p.2).le)

theorem energy_aestronglyMeasurable (F : EuclideanL2) : AEStronglyMeasurable (energy F) := by
  have hm : Measurable (fun p : Boundary × Boundary => (F p.1)^2/actualState p.1) :=
    (((Lp.stronglyMeasurable F).measurable.comp measurable_fst).pow_const 2).div
      (actualState_continuous.measurable.comp measurable_fst)
  exact hm.aestronglyMeasurable.mul (CubeBoundaryHaarL2.limit_memLp.aestronglyMeasurable.mul
    (actualState_continuous.measurable.comp measurable_snd).aestronglyMeasurable)

theorem energy_row_integrable (F : EuclideanL2) (X : Boundary) :
    Integrable (fun Y : Boundary => energy F (X,Y)) := by
  change Integrable (fun Y : Boundary =>
    (F X)^2/actualState X*(CubeBoundaryHaarL2.limit (X,Y)*actualState Y))
  exact (actual_row_ground_integrable X).const_mul _

theorem energy_row_integral (F : EuclideanL2) (X : Boundary) :
    (∫ Y : Boundary,energy F (X,Y))=eigenvalue*(F X)^2 := by
  change (∫ Y : Boundary,(F X)^2/actualState X*
    (CubeBoundaryHaarL2.limit (X,Y)*actualState Y))=_
  rw [integral_const_mul,actual_row_ground]
  field_simp [(state_positive X).ne']

theorem energy_integrable (F : EuclideanL2) : Integrable (energy F) := by
  apply (integrable_prod_iff (energy_aestronglyMeasurable F)).mpr
  constructor
  · exact ae_of_all _ (energy_row_integrable F)
  · have he : (fun X : Boundary => ∫ Y : Boundary,‖energy F (X,Y)‖)=
        (fun X : Boundary => eigenvalue*(F X)^2) := by
      funext X
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (energy_nonnegative F (X,_))]
      exact energy_row_integral F X
    rw [he]
    exact (Lp.memLp F).integrable_sq.const_mul _

theorem energy_integral (F : EuclideanL2) :
    (∫ p : Boundary × Boundary,energy F p)=eigenvalue*‖F‖^2 := by
  change (∫ p : Boundary × Boundary,energy F p ∂(volume.prod volume))=_
  rw [integral_prod _ (energy_integrable F)]
  simp_rw [energy_row_integral]
  rw [integral_const_mul]
  congr 1
  simpa only [Real.norm_eq_abs,sq_abs] using
    (BochnerL2Dominated.norm_sq_integral F).symm

theorem energy_swap_integrable (F : EuclideanL2) :
    Integrable (fun p : Boundary × Boundary => energy F p.swap) := by
  exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr (energy_integrable F)).comp_measurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure Boundary)) (ν := volume)))

theorem energy_swap_integral (F : EuclideanL2) :
    (∫ p : Boundary × Boundary,energy F p.swap)=eigenvalue*‖F‖^2 := by
  change (∫ p : Boundary × Boundary,energy F p.swap ∂(volume.prod volume))=_
  rw [(Measure.measurePreserving_swap (μ := (volume : Measure Boundary)) (ν := volume)).integral_comp
    (MeasurableEquiv.prodComm (α := Boundary) (β := Boundary)).measurableEmbedding (energy F)]
  exact energy_integral F

theorem weighted_young (F : EuclideanL2) (p : Boundary × Boundary) :
    |CubeBoundaryHaarL2.limit p*(F p.1*F p.2)| ≤ (energy F p+energy F p.swap)/2 := by
  have hx := state_positive p.1
  have hy := state_positive p.2
  have hh := sq_nonneg (actualState p.2*|F p.1|-actualState p.1*|F p.2|)
  have hb : 2*|F p.1*F p.2| ≤
      ((actualState p.2)^2*(F p.1)^2+(actualState p.1)^2*(F p.2)^2)/
        (actualState p.1*actualState p.2) := by
    apply (le_div_iff₀ (mul_pos hx hy)).mpr
    rw [abs_mul]
    nlinarith [sq_abs (F p.1),sq_abs (F p.2)]
  have he : ((actualState p.2)^2*(F p.1)^2+(actualState p.1)^2*(F p.2)^2)/
      (actualState p.1*actualState p.2)=
      (F p.1)^2/actualState p.1*actualState p.2+
        (F p.2)^2/actualState p.2*actualState p.1 := by
    field_simp [hx.ne',hy.ne']
  rw [he] at hb
  have hk := CubeBoundaryHaarL2.limit_nonnegative p
  have hm := mul_le_mul_of_nonneg_left hb hk
  rw [abs_mul,abs_of_nonneg hk]
  calc
    _ ≤ CubeBoundaryHaarL2.limit p*((F p.1)^2/actualState p.1*actualState p.2+
        (F p.2)^2/actualState p.2*actualState p.1)/2 := by nlinarith [hm]
    _ = _ := by
      unfold energy
      rcases p with ⟨X,Y⟩
      dsimp only [Prod.swap,Prod.fst,Prod.snd]
      rw [limit_swap Y X]
      ring

theorem quadratic_bound (F : EuclideanL2) :
    |inner ℝ (actualLimitOperator F) F| ≤ eigenvalue*‖F‖^2 := by
  have hi : Integrable (fun p : Boundary × Boundary =>
      CubeBoundaryHaarL2.limit p*(F p.1*F p.2)) :=
    CubeBoundaryHaarL2.limit_memLp.integrable_mul (tensor_memLp F F)
  have he : inner ℝ (actualLimitOperator F) F=
      ∫ p : Boundary × Boundary,CubeBoundaryHaarL2.limit p*(F p.1*F p.2) := by
    rw [actualLimitOperator_pairing,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [limitKernelClass_coe,tensorClass_coe F F] with p hK hT
    rw [hK,hT,Real.inner_apply]
    rfl
  rw [he]
  have h0 := norm_integral_le_integral_norm (μ := (volume : Measure (Boundary × Boundary)))
    (fun p : Boundary × Boundary => CubeBoundaryHaarL2.limit p*(F p.1*F p.2))
  simp only [Real.norm_eq_abs] at h0
  have h1 := integral_mono_ae hi.norm
    (((energy_integrable F).add (energy_swap_integrable F)).div_const 2)
      (ae_of_all _ (weighted_young F))
  simp only [Real.norm_eq_abs,Pi.add_apply] at h1
  have hr : (∫ p : Boundary × Boundary,(energy F p+energy F p.swap)/2)=eigenvalue*‖F‖^2 := by
    rw [integral_div,integral_add (energy_integrable F) (energy_swap_integrable F),
      energy_integral,energy_swap_integral]
    ring
  rw [hr] at h1
  exact h0.trans h1

theorem norm_le_eigenvalue : ‖actualLimitOperator‖ ≤ eigenvalue := by
  have hs : actualLimitOperator.IsSymmetric := by
    intro F G
    have h := ContinuousLinearMap.adjoint_inner_right actualLimitOperator F G
    rw [actualLimitOperator_selfadjoint] at h
    exact h.symm
  rw [actualLimitOperator.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro F
  by_cases hF : F=0
  · simp [hF,ContinuousLinearMap.rayleighQuotient,eigenvalue_positive.le]
  · have hn : 0 < ‖F‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hF)
    have h := quadratic_bound F
    simpa only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real,abs_div,abs_of_pos hn,div_le_iff₀ hn] using h

theorem norm_eq_eigenvalue : ‖actualLimitOperator‖=eigenvalue :=
  le_antisymm norm_le_eigenvalue eigenvalue_le_norm

theorem normalized_ground_fixed :
    CubeGroundNormLimit.normalizedLimitOperator stateClass=stateClass := by
  rw [normalized_operator_eigenvector,norm_eq_eigenvalue,
    div_self eigenvalue_positive.ne',one_smul]

theorem exact_groundScale_limit :
    Tendsto CubeGroundNormLimit.groundScale (𝓝[>] (0:ℝ)) (𝓝 eigenvalue) := by
  have h := CubeGroundNormLimit.groundScale_tendsto
  rwa [norm_eq_eigenvalue] at h

end OperatorDerivativeRewrite.Foundation.CubeGaussianSchurBound
