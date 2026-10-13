import Foundation.GaussianHilbertProcess
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Concrete real harmonizable kernels. Integrability is proved from bounds at
zero and infinity; fractional covariance and any causal representation are separate results. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalSpectralKernel

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev SpectralSpace := Lp Plane 2 (volume : Measure ℝ)

theorem spectralSpace_secondCountable : SecondCountableTopology SpectralSpace := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

def wave (u : ℝ) : Plane := WithLp.toLp 2 ![Real.cos u - 1, Real.sin u]

theorem wave_norm_sq (u : ℝ) : ‖wave u‖ ^ 2 = 2 - 2 * Real.cos u := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [wave, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem wave_norm_sq_le_four (u : ℝ) : ‖wave u‖ ^ 2 ≤ 4 := by
  rw [wave_norm_sq]
  linarith [Real.neg_one_le_cos u]

theorem wave_norm_sq_le (u : ℝ) : ‖wave u‖ ^ 2 ≤ 2 * u ^ 2 := by
  have hc : |Real.cos u - 1| ≤ |u| := by simpa using Real.abs_cos_sub_cos_le u 0
  have hs := Real.abs_sin_le_abs (x := u)
  have hc2 := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.mpr hc
  have hs2 := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.mpr hs
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [wave, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  nlinarith [sq_abs (Real.cos u - 1), sq_abs (Real.sin u), sq_abs u]

theorem wave_continuous : Continuous wave := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [wave] <;> fun_prop

def raw (H t x : ℝ) : Plane := x ^ (-H - 1/2) • wave (t*x)
def kernel (H t : ℝ) : ℝ → Plane := (Ioi 0).indicator (raw H t)

theorem raw_measurable (H t : ℝ) : Measurable (raw H t) := by
  exact (measurable_id.pow_const _).smul
    (wave_continuous.measurable.comp (measurable_const.mul measurable_id))

theorem kernel_measurable (H t : ℝ) : Measurable (kernel H t) :=
  (raw_measurable H t).indicator measurableSet_Ioi

theorem raw_norm_sq (H t x : ℝ) (hx : 0 < x) :
    ‖raw H t x‖ ^ 2 = x ^ (-2*H-1) * ‖wave (t*x)‖ ^ 2 := by
  rw [raw, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← Real.rpow_mul_natCast hx.le]
  congr 2
  ring

theorem raw_small_bound (H t x : ℝ) (hx : 0 < x) :
    ‖raw H t x‖ ^ 2 ≤ (2*t^2) * x ^ (1-2*H) := by
  rw [raw_norm_sq H t x hx]
  calc
    _ ≤ x ^ (-2*H-1) * (2*(t*x)^2) :=
      mul_le_mul_of_nonneg_left (wave_norm_sq_le _) (Real.rpow_nonneg hx.le _)
    _ = (2*t^2) * x ^ (1-2*H) := by
      rw [mul_pow]
      have he : x ^ (-2*H-1) * x^2 = x ^ (1-2*H) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hx]
        congr 1
        norm_num
        ring
      nlinarith [he]

theorem raw_large_bound (H t x : ℝ) (hx : 0 < x) :
    ‖raw H t x‖ ^ 2 ≤ 4 * x ^ (-2*H-1) := by
  rw [raw_norm_sq H t x hx]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (wave_norm_sq_le_four (t*x)) (Real.rpow_nonneg hx.le (-2*H-1))

theorem raw_sq_integrableOn (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    IntegrableOn (fun x => ‖raw H t x‖ ^ 2) (Ioi 0) volume := by
  have hsmall : IntegrableOn (fun x => ‖raw H t x‖ ^ 2) (Ioc 0 1) volume := by
    have hp : IntegrableOn (fun x : ℝ => x ^ (1-2*H)) (Ioc 0 1) volume := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
    apply (hp.const_mul (2*t^2)).mono' ((raw_measurable H t).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using raw_small_bound H t x hx.1
  have hlarge : IntegrableOn (fun x => ‖raw H t x‖ ^ 2) (Ioi 1) volume := by
    have hp := integrableOn_Ioi_rpow_of_lt (by linarith : -2*H-1 < -1) (by norm_num : (0:ℝ)<1)
    apply (hp.const_mul 4).mono' ((raw_measurable H t).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs, abs_sq] using
      raw_large_bound H t x (lt_trans (by norm_num) hx)
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h; by_cases hx : x ≤ 1
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  rw [← hu]
  exact hsmall.union hlarge

theorem kernel_sq_integrable (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    Integrable (fun x => ‖kernel H t x‖ ^ 2) volume := by
  have he : (fun x => ‖kernel H t x‖ ^ 2) =
      (Ioi 0).indicator (fun x => ‖raw H t x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioi (0:ℝ) <;> simp [kernel, hx]
  rw [he]
  exact (raw_sq_integrableOn H t hH0 hH1).integrable_indicator measurableSet_Ioi

theorem kernel_memLp (H t : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    MemLp (kernel H t) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (kernel_measurable H t).aestronglyMeasurable).mpr
    (kernel_sq_integrable H t hH0 hH1)

def vector (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) : SpectralSpace :=
  (kernel_memLp H t hH0 hH1).toLp (kernel H t)

theorem vector_coeFn (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) :
    vector H hH0 hH1 t =ᵐ[volume] kernel H t := MemLp.coeFn_toLp _

theorem vector_zero (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    vector H hH0 hH1 0 = 0 := by
  apply Lp.ext
  filter_upwards [vector_coeFn H hH0 hH1 0,
    Lp.coeFn_zero (E := Plane) (p := 2) (μ := volume)] with x hk hz
  rw [hk, hz]
  by_cases hx : 0 < x <;> simp [kernel, raw, wave, hx, Set.mem_Ioi]

theorem vector_one_ne_zero (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    vector H hH0 hH1 1 ≠ 0 := by
  intro hz
  have he := vector_coeFn H hH0 hH1 1
  rw [hz] at he
  have hae := he.symm.trans (Lp.coeFn_zero (E := Plane) (p := 2) (μ := volume))
  have hvol : (volume : Measure ℝ) (Ioo 0 Real.pi) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
  obtain ⟨x, hx, he⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol (ae_restrict_of_ae hae)
  have hc := congrArg (fun v : Plane => v 1) he
  simp [kernel, raw, wave, hx.1] at hc
  exact hc.elim (Real.rpow_pos_of_pos hx.1 _).ne' (Real.sin_pos_of_mem_Ioo hx).ne'

theorem vector_norm_sq_integral (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ) :
    ‖vector H hH0 hH1 t‖ ^ 2 = ∫ x, ‖kernel H t x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vector_coeFn H hH0 hH1 t] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end OperatorDerivativeRewrite.Foundation.FractionalSpectralKernel
