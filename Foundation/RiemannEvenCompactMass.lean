import Foundation.RiemannEvenConcentration

/-! Actual compact contributions are exponentially small relative to a global
maximum of the integer-even amplitude. All constants come from the literal
kernel on a fixed compact interval and one positive comparison point. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenCompactMass
open RiemannQuarticKernel RiemannEvenDomain RiemannEvenRealSaddle

theorem compact_exponent_gap_pos (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    0 < (R+1)^(2*m)-R^(2*m) := by
  exact sub_pos.mpr (pow_lt_pow_left₀ (by linarith : R < R+1) hR (by omega))

theorem exists_compact_amplitude_envelope (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ), 0 ≤ t → u ∈ Ici (0 : ℝ) →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u → ∀ v ∈ Icc (0 : ℝ) R,
        weighted m 0 t 0 v ≤ C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*weighted m 0 t 0 u := by
  obtain ⟨w,hw,hK⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) R).Nonempty from ⟨0,le_rfl,hR⟩)
    (kernel_continuousOn.mono (fun x hx => hx.1))
  have hb : 0 < kernel (R+1) := kernel_pos _ (by linarith)
  have hKpos := kernel_pos w hw.1
  let C := kernel w/kernel (R+1)
  refine ⟨C,div_pos hKpos hb,?_⟩
  intro t u ht hu hmax v hv
  have hbase : weighted m 0 t 0 v ≤ Real.exp (t*R^(2*m))*kernel w := by
    have hp := pow_le_pow_left₀ hv.1 hv.2 (2*m)
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp ht)) (hK hv)
      (kernel_pos v hv.1).le (Real.exp_pos _).le
  have hdom := hmax (show R+1 ∈ Ici (0 : ℝ) from by change 0 ≤ R+1; linarith)
  have hmul := mul_le_mul_of_nonneg_left hdom
    (show 0 ≤ C*Real.exp (-t*((R+1)^(2*m)-R^(2*m))) by dsimp [C]; positivity)
  have hid : C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*weighted m 0 t 0 (R+1) =
      Real.exp (t*R^(2*m))*kernel w := by
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
    calc
      _ = C*(Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*Real.exp (t*(R+1)^(2*m)))*kernel (R+1) := by ring
      _ = C*Real.exp (t*R^(2*m))*kernel (R+1) := by
        rw [← Real.exp_add,show -t*((R+1)^(2*m)-R^(2*m))+t*(R+1)^(2*m) = t*R^(2*m) by ring]
      _ = _ := by dsimp [C]; field_simp
  exact hbase.trans (by rw [← hid]; exact hmul)

theorem exists_compact_mass_envelope (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ), 0 ≤ t → u ∈ Ici (0 : ℝ) →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        (∫ v : ℝ in 0..R, weighted m 0 t 0 v) ≤
          C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*weighted m 0 t 0 u := by
  obtain ⟨C,hC,hbound⟩ := exists_compact_amplitude_envelope m hm R hR
  refine ⟨(R+1)*C,mul_pos (by linarith) hC,?_⟩
  intro t u ht hu hmax
  let D := C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*weighted m 0 t 0 u
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hi := hcont.intervalIntegrable (μ := volume) 0 R
  have hc := (continuous_const : Continuous (fun _ : ℝ => D)).intervalIntegrable (μ := volume) 0 R
  have h := intervalIntegral.integral_mono_on hR hi hc (hbound t u ht hu hmax)
  rw [intervalIntegral.integral_const] at h
  simp only [sub_zero,smul_eq_mul] at h
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (by positivity) (weighted_pos m t u hu).le
  apply h.trans
  dsimp [D]
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannEvenCompactMass
