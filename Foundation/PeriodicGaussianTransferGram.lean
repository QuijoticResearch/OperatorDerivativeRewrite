import Foundation.GaussianLikelihoodRootOverlap
import Foundation.FiniteGaussianTensor
import Foundation.PeriodicHighActionControl
/-! Actual Gaussian Gram realization of the periodic Wilson kinetic kernel.
The finite Gaussian product, scalar likelihood roots, exact quaternion distance
and constructed ground-transform pairing are reused. Positivity is proved on
the bounded measurable physical native L2 core, not assumed from reversibility.
No strict spectral gap, continuum limit or mass-gap statement follows. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicGaussianTransferGram
open GaussianLikelihoodRootKernel GaussianLikelihoodRootOverlap FiniteGaussian
variable {ι : Type*} [Fintype ι]
def root (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∏ i, rootKernel (a i) (x i)
theorem root_continuous (a : ι → ℝ) : Continuous (root a) := by
  classical
  apply continuous_finsetProd
  intro i _
  exact rootKernel_continuous.comp (continuous_const.prodMk (continuous_apply i))
theorem root_square_integrable (a : ι → ℝ) :
    Integrable (fun x => root a x ^ 2) (productGaussian ι) := by
  classical
  have he : (fun x => root a x ^ 2) = fun x => ∏ i, rootKernel (a i) (x i)^2 := by
    funext x
    simp only [root, Finset.prod_pow]
  rw [he]
  simp_rw [rootKernel_square]
  exact Integrable.fintype_prod (fun i => GaussianRandomDensityKernel.kernel_integrable (a i))
theorem root_memLp (a : ι → ℝ) : MemLp (root a) 2 (productGaussian ι) :=
  (memLp_two_iff_integrable_sq (root_continuous a).aestronglyMeasurable).mpr
    (root_square_integrable a)
def feature (a : ι → ℝ) : Lp ℝ 2 (productGaussian ι) := (root_memLp a).toLp (root a)
theorem feature_inner (a b : ι → ℝ) :
    inner ℝ (feature a) (feature b) = Real.exp (- (∑ i, (a i-b i)^2)/8) := by
  classical
  rw [L2_inner_eq_integral]
  have he : (fun x => inner ℝ (feature a x) (feature b x)) =ᵐ[productGaussian ι]
      fun x => ∏ i, (rootKernel (a i) (x i) * rootKernel (b i) (x i)) := by
    filter_upwards [MemLp.coeFn_toLp (root_memLp a), MemLp.coeFn_toLp (root_memLp b)] with x ha hb
    change inner ℝ ((root_memLp a).toLp (root a) x) ((root_memLp b).toLp (root b) x) = _
    rw [ha,hb,Real.inner_apply]
    exact Finset.prod_mul_distrib.symm
  rw [integral_congr_ae he,productGaussian,integral_fintype_prod_eq_prod (fun i (y : ℝ) => rootKernel (a i) y * rootKernel (b i) y)]
  simp only [overlap_integral]
  rw [← Real.exp_sum]
  congr 1
  simp only [← Finset.sum_div, ← Finset.sum_neg_distrib]
theorem feature_norm (a : ι → ℝ) : ‖feature a‖ = 1 := by
  have h := feature_inner a a
  simp only [sub_self,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,neg_zero,zero_div,Real.exp_zero] at h
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (feature a)]
theorem feature_dist (a b : ι → ℝ) :
    dist (feature a) (feature b) = Real.sqrt (2 * (1 - Real.exp (-(∑ i, (a i-b i)^2)/8))) := by
  calc
    dist (feature a) (feature b) = Real.sqrt (‖feature a-feature b‖^2) := by
      rw [Real.sqrt_sq (norm_nonneg _),dist_eq_norm]
    _ = _ := by
      congr 1
      rw [norm_sub_sq_real,feature_norm,feature_norm,feature_inner]
      ring
theorem feature_continuous : Continuous (feature (ι := ι)) := by
  rw [continuous_iff_continuous_dist]
  simp_rw [feature_dist]
  fun_prop

open QuaternionSU2Representation PeriodicTemporalSlab PeriodicLoopVariation PeriodicWilsonSlab
open scoped Quaternion

def coordinates (U : SU2) : Fin 4 → ℝ := ![(lift U).re,(lift U).imI,(lift U).imJ,(lift U).imK]
theorem coordinates_continuous : Continuous coordinates := by
  have hl : Continuous lift := continuous_subtype_val.comp homeomorph.symm.continuous
  apply continuous_pi
  intro i
  fin_cases i
  · exact Quaternion.continuous_re.comp hl
  · exact Quaternion.continuous_imI.comp hl
  · exact Quaternion.continuous_imJ.comp hl
  · exact Quaternion.continuous_imK.comp hl

theorem coordinates_distance (U V : SU2) :
    (∑ i, (coordinates U i-coordinates V i)^2) = 2*(1-halfTrace (U*V⁻¹)) := by
  calc
    _ = distance U V ^2 := by
      unfold distance
      rw [pow_two,← Quaternion.normSq_eq_norm_mul_self]
      norm_num [coordinates,Fin.sum_univ_succ,Quaternion.normSq_def',Quaternion.re_sub,
        Quaternion.imI_sub,Quaternion.imJ_sub,Quaternion.imK_sub]
      ring
    _ = _ := distance_sq U V

def parameters (β : ℝ) (U : State) : SpatialEdge × Fin 4 → ℝ :=
  fun q => 2*Real.sqrt β * coordinates (U q.1) q.2

theorem parameter_distance (β : ℝ) (hb : 0 ≤ β) (U V : State) :
    (∑ q, (parameters β U q-parameters β V q)^2) = 8*β*temporalAction U V 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have hs (e : SpatialEdge) :
      (∑ i : Fin 4, (parameters β U (e,i)-parameters β V (e,i))^2) =
        8*β*(1-halfTrace (U e*(V e)⁻¹)) := by
    simp only [parameters]
    simp_rw [show ∀ x y : ℝ, (2*Real.sqrt β*x-2*Real.sqrt β*y)^2 =
      4*β*(x-y)^2 by intro x y; calc
        _ = 4*(Real.sqrt β)^2*(x-y)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hb]]
    rw [← Finset.mul_sum,coordinates_distance]
    ring
  simp_rw [hs]
  rw [← Finset.mul_sum]
  apply congrArg (fun x : ℝ => 8*β*x)
  unfold temporalAction temporalWord
  simp only [Pi.one_apply,mul_one,inv_one]

def wilsonFeature (β : ℝ) (U : State) : Lp ℝ 2 (productGaussian (SpatialEdge × Fin 4)) :=
  feature (parameters β U)

theorem wilsonFeature_inner (β : ℝ) (hb : 0 ≤ β) (U V : State) :
    inner ℝ (wilsonFeature β U) (wilsonFeature β V) = Real.exp (-β*temporalAction U V 1) := by
  rw [wilsonFeature,wilsonFeature,feature_inner,parameter_distance β hb]
  congr 1
  ring

theorem wilsonFeature_norm (β : ℝ) (U : State) : ‖wilsonFeature β U‖ = 1 := feature_norm _

theorem wilsonFeature_continuous (β : ℝ) : Continuous (wilsonFeature β) := by
  apply feature_continuous.comp
  apply continuous_pi
  intro q
  exact continuous_const.mul (((continuous_apply q.2).comp coordinates_continuous).comp (continuous_apply q.1))
open PeriodicSlabGround PeriodicPhysicalKineticReduction PeriodicSlabL2 CubeHaarUpper

/-- Actual Bochner integrability; no formal feature symbol substitutes for an L2 vector. -/
theorem weighted_feature_integrable (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ U, |f U| ≤ B) :
    Integrable (fun U => f U • wilsonFeature β U) boundaryHaar := by
  apply Integrable.of_bound
    (hf.aestronglyMeasurable.smul (wilsonFeature_continuous β).aestronglyMeasurable) B
  filter_upwards with U
  change ‖f U • wilsonFeature β U‖ ≤ B
  rw [norm_smul,wilsonFeature_norm,mul_one,Real.norm_eq_abs]
  exact hB U

/-- A genuine Haar quadratic integral is the squared norm of a Gaussian feature integral. -/
theorem haar_gram (β : ℝ) (hb : 0 ≤ β) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ U, |f U| ≤ B) :
    (∫ U, ∫ V, Real.exp (-β*temporalAction U V 1)*(f U*f V) ∂boundaryHaar ∂boundaryHaar) =
      ‖∫ U, f U • wilsonFeature β U ∂boundaryHaar‖^2 := by
  have hi := weighted_feature_integrable β f hf B hB
  let F := fun U => f U • wilsonFeature β U
  calc
    _ = ∫ U, ∫ V, inner ℝ (F U) (F V) ∂boundaryHaar ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      apply integral_congr_ae
      filter_upwards with V
      dsimp [F]
      rw [real_inner_smul_left,inner_smul_right,wilsonFeature_inner β hb]
      ring
    _ = ∫ U, inner ℝ (F U) (∫ V, F V ∂boundaryHaar) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      exact integral_inner hi (F U)
    _ = inner ℝ (∫ U, F U ∂boundaryHaar) (∫ V, F V ∂boundaryHaar) := by
      calc
        _ = ∫ U, inner ℝ (∫ V, F V ∂boundaryHaar) (F U) ∂boundaryHaar :=
          integral_congr_ae (ae_of_all _ (fun U => real_inner_comm _ _))
        _ = _ := integral_inner hi _
    _ = _ := real_inner_self_eq_norm_sq _

private theorem dressed_probe {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    Measurable (fun U => PeriodicLocalGroundHarnack.dressed g U*f U) ∧
      (∀ U,|PeriodicLocalGroundHarnack.dressed g U*f U| ≤ |g.upper| *|B|) := by
  have hM : Measurable (multiplier β) := (((spatial_action_measurable.const_mul (-β)).div_const 2).exp)
  refine ⟨(hM.mul g.measurable).mul hf,?_⟩
  intro U
  have hM1 : multiplier β U ≤ 1 := by
    unfold multiplier
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (spatial_action_bounds U).1) (by norm_num))
  have hd : |PeriodicLocalGroundHarnack.dressed g U| ≤ |g.upper| := by
    unfold PeriodicLocalGroundHarnack.dressed
    rw [abs_mul,abs_of_pos (show 0 < multiplier β U by unfold multiplier; exact Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right hM1 (abs_nonneg _)).trans
      (by simpa using (g.bounds U).2.trans (le_abs_self _))
  rw [abs_mul]
  exact mul_le_mul hd ((hB U).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

/-- The ground, eigenvalue and native normalizer are retained exactly. -/
theorem native_gram {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f) =
      (1/(g.value*g.normalizer))*
        ‖∫ U, (PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U ∂boundaryHaar‖^2 := by
  rw [PeriodicHighActionControl.native_kinetic_pairing hb g f hf hmem B hB hInv]
  have hd := dressed_probe hb g f hf B hB
  have he : (∫ U,∫ V,kineticDensity β U V*((PeriodicLocalGroundHarnack.dressed g U*f U)*
        (PeriodicLocalGroundHarnack.dressed g V*f V)) ∂boundaryHaar ∂boundaryHaar) =
      (∫ U,∫ V,Real.exp (-β*temporalAction U V 1)*((PeriodicLocalGroundHarnack.dressed g U*f U)*
        (PeriodicLocalGroundHarnack.dressed g V*f V)) ∂boundaryHaar ∂boundaryHaar)/(laplace β^192) := by
    unfold kineticDensity
    simp_rw [div_mul_eq_mul_div,integral_div]
  rw [he,haar_gram β hb _ hd.1 _ hd.2]
  field_simp [(laplace_pos β hb).ne',g.value_pos.ne',g.normalizer_pos.ne']

theorem native_nonnegative {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (B : ℝ) (hB : ∀ U,|f U| ≤ B)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    0 ≤ inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f) := by
  rw [native_gram hb g f hf hmem B hB hInv]
  exact mul_nonneg (div_pos (by norm_num) (mul_pos g.value_pos g.normalizer_pos)).le (sq_nonneg _)
end OperatorDerivativeRewrite.Foundation.PeriodicGaussianTransferGram
