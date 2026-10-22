import Foundation.IBMIntrinsicChainEnergy
import Foundation.RealSteklovApprox
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Bounded approximants for the unbounded native C1 chain extension. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainApproximation
open IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

abbrev width := RealSteklovApprox.width

def clip (n : ℕ) (x : ℝ) : ℝ := Real.sin (width n*x) / width n

theorem clip_sinc (n : ℕ) (x : ℝ) : clip n x = x * Real.sinc (width n*x) := by
  have hn := (RealSteklovApprox.width_pos n).ne'
  by_cases hx : x = 0
  · simp [clip,hx]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hn hx), clip]
    field_simp

theorem clip_bound (n : ℕ) (x : ℝ) : ‖clip n x‖ ≤ (width n)⁻¹ := by
  rw [clip,norm_div]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (RealSteklovApprox.width_pos n)]
  exact (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (width n*x))
    (RealSteklovApprox.width_pos n).le).trans_eq (one_div _)

theorem clip_domination (n : ℕ) (x : ℝ) : ‖clip n x‖ ≤ ‖x‖ := by
  rw [clip_sinc,norm_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) (norm_nonneg x)).trans_eq (mul_one _)

theorem width_tendsto : Tendsto width atTop (𝓝 (0 : ℝ)) :=
  tendsto_nhds_of_tendsto_nhdsWithin RealSteklovApprox.width_tendsto

theorem clip_tendsto (x : ℝ) : Tendsto (fun n => clip n x) atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).mul
    (Real.continuous_sinc.continuousAt.tendsto.comp (width_tendsto.mul_const x))
  simpa only [Function.comp_def,mul_zero,zero_mul,Real.sinc_zero,mul_one,← clip_sinc] using h

def approximant (φ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := clip n (φ x)

def approximantDerivative (φ dφ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (width n*φ x) * dφ x

theorem approximant_hasDerivAt (φ dφ : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (dφ x) x) (n : ℕ) (x : ℝ) :
    HasDerivAt (approximant φ n) (approximantDerivative φ dφ n x) x := by
  have h := (((hd x).const_mul (width n)).sin).div_const (width n)
  convert h using 1
  · rfl
  · dsimp [approximantDerivative]
    have hn := (RealSteklovApprox.width_pos n).ne'
    field_simp

theorem approximantDerivative_continuous (φ dφ : ℝ → ℝ)
    (hφ : Continuous φ) (hdφ : Continuous dφ) (n : ℕ) :
    Continuous (approximantDerivative φ dφ n) :=
  (Real.continuous_cos.comp ((continuous_const : Continuous (fun _ : ℝ => width n)).mul hφ)).mul hdφ

theorem approximantDerivative_bound (φ dφ : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x, ‖dφ x‖ ≤ B) (n : ℕ) (x : ℝ) :
    ‖approximantDerivative φ dφ n x‖ ≤ B := by
  rw [approximantDerivative,norm_mul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg (dφ x))).trans
    (by simpa only [one_mul] using hB x)

theorem approximantDerivative_tendsto (φ dφ : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n => approximantDerivative φ dφ n x) atTop (𝓝 (dφ x)) := by
  have h := ((Real.continuous_cos.continuousAt.tendsto.comp
    (width_tendsto.mul_const (φ x))).mul_const (dφ x))
  simpa only [Function.comp_def,approximantDerivative,zero_mul,Real.cos_zero,one_mul] using h

theorem composition_memLp (φ dφ : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (dφ x) x) (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B)
    (f : JointL2) : MemLp (fun ω => φ (f ω)) 2 IBMSourceLaws.jointMeasure := by
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hlip : LipschitzWith ⟨B,hB0⟩ φ :=
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
      (fun x => by change ‖deriv φ x‖ ≤ B; rw [(hd x).deriv]; exact hB x)
  have hm : MemLp (fun ω => φ (f ω)-φ 0) 2 IBMSourceLaws.jointMeasure := by
    apply (Lp.memLp f).of_le_mul (c := B)
    · exact (hlip.continuous.comp_aestronglyMeasurable
        (Lp.memLp f).aestronglyMeasurable).sub aestronglyMeasurable_const
    · exact ae_of_all _ fun ω => by
        have h := hlip.norm_sub_le (f ω) 0
        change ‖φ (f ω)-φ 0‖ ≤ B * ‖f ω-0‖ at h
        simpa only [sub_zero] using h
  have hh := hm.add (memLp_const (φ 0) : MemLp (fun _ : IBMSourceLaws.JointSample => φ 0) 2 IBMSourceLaws.jointMeasure)
  convert hh using 1
  ext ω
  simp only [Pi.add_apply, sub_add_cancel]

def clippedValue (n : ℕ) (f : JointL2) : JointL2 :=
  (MemLp.of_bound
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const (width n)
      |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    ((width n)⁻¹) (ae_of_all _ fun ω => clip_bound n (f ω))).toLp _

theorem clippedValue_ae (n : ℕ) (f : JointL2) :
    clippedValue n f =ᵐ[IBMSourceLaws.jointMeasure] fun ω => clip n (f ω) :=
  MemLp.coeFn_toLp _

theorem clippedValue_tendsto (f : JointL2) :
    Tendsto (fun n => clippedValue n f) atTop (𝓝 f) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ f f
  · intro n
    filter_upwards [clippedValue_ae n f] with ω hω
    rw [hω]
    exact clip_domination n _
  · exact ae_of_all _ fun _ => le_rfl
  · filter_upwards [ae_all_iff.mpr (fun n => clippedValue_ae n f)] with ω hω
    simpa only [hω] using clip_tendsto (f ω)

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainApproximation
