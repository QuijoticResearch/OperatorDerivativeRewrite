import Foundation.CubeKernelOperatorBound
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Operator-norm convergence of the actual local Wilson compressions on a fixed L2 space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeCompressedNormLimit
open CubeChartAction CubeBoundaryChartL2 CubeKernelOperatorBound CubeChartCompressedKernel CubeSlabGround

def limitKernelClass : KernelL2 := CubeBoundaryHaarL2.limit_memLp.toLp CubeBoundaryHaarL2.limit
theorem limitKernelClass_coe : limitKernelClass =ᵐ[volume] CubeBoundaryHaarL2.limit := MemLp.coeFn_toLp _

def kernelFamily (t : ℝ) : KernelL2 :=
  if h : 0 < t ∧ t ≤ 1 then kernelClass t h.1 h.2 else 0

theorem kernelFamily_pos (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    kernelFamily t=kernelClass t ht h1 := by
  unfold kernelFamily
  rw [dif_pos (show 0<t ∧ t≤1 from ⟨ht,h1⟩)]

theorem kernelFamily_coe (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    kernelFamily t =ᵐ[volume] CubeBoundaryHaarL2.kernel t := by
  simpa only [kernelFamily,dif_pos (show 0<t ∧ t≤1 from ⟨ht,h1⟩)] using kernelClass_coe t ht h1

theorem kernel_error_sq (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    ‖kernelFamily t-limitKernelClass‖^2=
      ∫ p : Boundary × Boundary,(CubeBoundaryHaarL2.kernel t p-CubeBoundaryHaarL2.limit p)^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (kernelFamily t) limitKernelClass,kernelFamily_coe t ht h1,
    limitKernelClass_coe] with p hS hK hL
  rw [hS]
  simp only [Pi.sub_apply]
  rw [hK,hL,Real.norm_eq_abs,sq_abs]

theorem kernelFamily_tendsto : Tendsto kernelFamily (𝓝[>] (0:ℝ)) (𝓝 limitKernelClass) := by
  have hs : Tendsto (fun t : ℝ => ‖kernelFamily t-limitKernelClass‖^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply CubeBoundaryHaarL2.integral_sq_error_tendsto.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
    exact (kernel_error_sq t ht h1).symm
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h

variable (d : ∀ t : ℝ, 0 < t → GroundData (1/t^2))

def operatorFamily (t : ℝ) : EuclideanL2 →L[ℝ] EuclideanL2 :=
  if ht : 0 < t then compressed t ht (d t ht) else 0

theorem operatorFamily_pos (t : ℝ) (ht : 0 < t) :
    operatorFamily d t=compressed t ht (d t ht) := by
  unfold operatorFamily
  rw [dif_pos ht]

theorem operatorFamily_selfadjoint (t : ℝ) : (operatorFamily d t).adjoint=operatorFamily d t := by
  by_cases ht : 0 < t
  · simp only [operatorFamily,dif_pos ht,compressed_selfadjoint]
  · simp [operatorFamily,ht]

/-- The actual operator family is Cauchy in operator norm, not merely weakly on test functions. -/
theorem operatorFamily_cauchy : Cauchy (Filter.map (operatorFamily d) (𝓝[>] (0:ℝ))) := by
  apply Metric.cauchy_iff.mpr
  refine ⟨by infer_instance,?_⟩
  intro ε hε
  let good : Set ℝ := {t | 0<t ∧ t≤1 ∧ ‖kernelFamily t-limitKernelClass‖<ε/2}
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp kernelFamily_tendsto).eventually
    (eventually_lt_nhds (show (0:ℝ)<ε/2 by linarith))
  have hg : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),t ∈ good := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,hn] with t ht h1 he
    exact ⟨ht,h1,he⟩
  refine ⟨operatorFamily d '' good,?_,?_⟩
  · change ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),operatorFamily d t ∈ operatorFamily d '' good
    exact hg.mono (fun t ht => ⟨t,ht,rfl⟩)
  · rintro _ ⟨t,ht,rfl⟩ _ ⟨s,hs,rfl⟩
    rcases ht with ⟨ht,h1,het⟩
    rcases hs with ⟨hs,hs1,hes⟩
    rw [dist_eq_norm]
    have hb : ‖operatorFamily d t-operatorFamily d s‖ ≤ ‖kernelFamily t-kernelFamily s‖ := by
      simpa only [operatorFamily,dif_pos ht,dif_pos hs,kernelFamily,
        dif_pos (show 0<t ∧ t≤1 from ⟨ht,h1⟩),dif_pos (show 0<s ∧ s≤1 from ⟨hs,hs1⟩)] using
          compressed_difference_bound t s ht hs h1 hs1 (d t ht) (d s hs)
    calc
      _ ≤ ‖kernelFamily t-kernelFamily s‖ := hb
      _ ≤ ‖kernelFamily t-limitKernelClass‖+‖kernelFamily s-limitKernelClass‖ := by
        calc
          _ = ‖(kernelFamily t-limitKernelClass)+(limitKernelClass-kernelFamily s)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev limitKernelClass (kernelFamily s)]
      _ < ε := by linarith

theorem exists_operator_norm_limit : ∃ T : EuclideanL2 →L[ℝ] EuclideanL2,
    Tendsto (operatorFamily d) (𝓝[>] (0:ℝ)) (𝓝 T) :=
  cauchy_map_iff_exists_tendsto.mp (operatorFamily_cauchy d)

def limitOperator : EuclideanL2 →L[ℝ] EuclideanL2 := Classical.choose (exists_operator_norm_limit d)
theorem operatorFamily_tendsto : Tendsto (operatorFamily d) (𝓝[>] (0:ℝ)) (𝓝 (limitOperator d)) :=
  Classical.choose_spec (exists_operator_norm_limit d)

/-- Quantitative error to the actual operator-norm limit is controlled by the genuine kernel error. -/
theorem operator_error_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    ‖operatorFamily d t-limitOperator d‖ ≤ ‖kernelFamily t-limitKernelClass‖ := by
  have hL : Tendsto (fun s : ℝ => ‖operatorFamily d t-operatorFamily d s‖)
      (𝓝[>] (0:ℝ)) (𝓝 ‖operatorFamily d t-limitOperator d‖) :=
    (tendsto_const_nhds.sub (operatorFamily_tendsto d)).norm
  have hR : Tendsto (fun s : ℝ => ‖kernelFamily t-kernelFamily s‖)
      (𝓝[>] (0:ℝ)) (𝓝 ‖kernelFamily t-limitKernelClass‖) :=
    (tendsto_const_nhds.sub kernelFamily_tendsto).norm
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with s hs hs1
  rw [operatorFamily_pos d t ht,operatorFamily_pos d s hs,kernelFamily_pos t ht h1,kernelFamily_pos s hs hs1]
  exact compressed_difference_bound t s ht hs h1 hs1 (d t ht) (d s hs)

theorem limitOperator_selfadjoint : (limitOperator d).adjoint=limitOperator d := by
  have h := (ContinuousLinearMap.adjoint.continuous.tendsto (limitOperator d)).comp (operatorFamily_tendsto d)
  have he : Tendsto (operatorFamily d) (𝓝[>] (0:ℝ)) (𝓝 (limitOperator d).adjoint) := by
    simpa only [Function.comp_def,operatorFamily_selfadjoint] using h
  exact tendsto_nhds_unique he (operatorFamily_tendsto d)

theorem limitOperator_ground_independent (e : ∀ t : ℝ,0 < t → GroundData (1/t^2)) : limitOperator d=limitOperator e := by
  have h : operatorFamily d=operatorFamily e := by
    funext t
    by_cases ht : 0<t
    · simp only [operatorFamily,dif_pos ht]
      exact compressed_ground_independent t ht (d t ht) (e t ht)
    · simp only [operatorFamily,dif_neg ht]
  apply tendsto_nhds_unique (operatorFamily_tendsto d)
  rw [h]
  exact operatorFamily_tendsto e

/-- The norm limit is identified by the same genuine Haar-root-averaged Schur kernel. -/
theorem limitOperator_pairing (F G : EuclideanL2) :
    inner ℝ (limitOperator d F) G=inner ℝ limitKernelClass (tensorClass F G) := by
  have hEval := ((ContinuousLinearMap.apply ℝ EuclideanL2 F).continuous.tendsto
    (limitOperator d)).comp (operatorFamily_tendsto d)
  have hL : Tendsto (fun t : ℝ => inner ℝ (operatorFamily d t F) G) (𝓝[>] (0:ℝ))
      (𝓝 (inner ℝ (limitOperator d F) G)) :=
    hEval.inner tendsto_const_nhds
  have hR : Tendsto (fun t : ℝ => inner ℝ (kernelFamily t) (tensorClass F G)) (𝓝[>] (0:ℝ))
      (𝓝 (inner ℝ limitKernelClass (tensorClass F G))) := kernelFamily_tendsto.inner tendsto_const_nhds
  have he : (fun t : ℝ => inner ℝ (operatorFamily d t F) G) =ᶠ[𝓝[>] (0:ℝ)]
      (fun t => inner ℝ (kernelFamily t) (tensorClass F G)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
    rw [operatorFamily_pos d t ht,kernelFamily_pos t ht h1]
    exact compressed_pairing t ht h1 (d t ht) F G
  exact tendsto_nhds_unique (hL.congr' he) hR

/-- Closed instantiation uses the EXISTING proved finite-slab ground construction. -/
def actualOperatorFamily : ℝ → EuclideanL2 →L[ℝ] EuclideanL2 :=
  operatorFamily (fun t _ => ground (1/t^2))
def actualLimitOperator : EuclideanL2 →L[ℝ] EuclideanL2 :=
  limitOperator (fun t _ => ground (1/t^2))

theorem actualOperatorFamily_tendsto :
    Tendsto actualOperatorFamily (𝓝[>] (0:ℝ)) (𝓝 actualLimitOperator) :=
  operatorFamily_tendsto (fun t _ => ground (1/t^2))

theorem actualLimitOperator_pairing (F G : EuclideanL2) :
    inner ℝ (actualLimitOperator F) G=inner ℝ limitKernelClass (tensorClass F G) :=
  limitOperator_pairing (fun t _ => ground (1/t^2)) F G

theorem actual_operator_error (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    ‖actualOperatorFamily t-actualLimitOperator‖ ≤ ‖kernelFamily t-limitKernelClass‖ :=
  operator_error_bound (fun t _ => ground (1/t^2)) t ht h1

theorem actualLimitOperator_selfadjoint : actualLimitOperator.adjoint=actualLimitOperator :=
  limitOperator_selfadjoint (fun t _ => ground (1/t^2))

theorem actualLimitOperator_norm_bound : ‖actualLimitOperator‖ ≤ ‖limitKernelClass‖ :=
  opNorm_le_of_pairing actualLimitOperator limitKernelClass actualLimitOperator_pairing

theorem actualLimitOperator_integral_pairing (F G : EuclideanL2) :
    inner ℝ (actualLimitOperator F) G=
      ∫ X : Boundary,G X*(∫ Y : Boundary,CubeBoundaryHaarL2.limit (X,Y)*F Y) := by
  rw [actualLimitOperator_pairing]
  exact pairing_eq_integral _ CubeBoundaryHaarL2.limit_memLp F G

end OperatorDerivativeRewrite.Foundation.CubeCompressedNormLimit
