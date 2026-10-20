import Foundation.RiemannEvenModelPhase
import Foundation.RiemannQuarticComplexModelSaddle

/-! Constructed integer-even high-frequency model saddles. These are roots
of the leading slope, not actual logarithmic saddles or transform zeros. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenFarModelSaddle
open RiemannEvenModelPhase RiemannQuarticQuantitativeSaddle

theorem anchored_complex_saddle (m : ℕ) (hm : 0 < m) (t M : ℝ) (z : ℂ)
    (ht : 0 ≤ t) (hM : 1 ≤ M)
    (hx : 10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1)*M^(2*m-1) ≤ ‖z‖)
    (b : ℂ) (hb : ‖b‖ ≤ M-1)
    (hanchor : 4*(Real.pi : ℂ)*Complex.exp (4*b) = Complex.I*z) :
    ∃! w, w ∈ closedBall b (1/1024) ∧ modelDerivative m t w = -(Complex.I*z) := by
  let n : ℕ := 2*m
  let N : ℝ := n
  let p : ℝ := (N+1)^2
  let core : ℝ := p*(t+1)*M^(n-1)
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hprev : ((n-1 : ℕ) : ℝ) ≤ N := by dsimp [N]; exact_mod_cast Nat.sub_le n 1
  have hp1 : 1 ≤ p := by dsimp [p]; nlinarith
  have hpN : N ≤ p := by dsimp [p]; nlinarith
  have hpNN : N*((n-1 : ℕ) : ℝ) ≤ p := by
    have h := mul_le_mul_of_nonneg_left hprev hN
    dsimp [p]
    nlinarith
  have hpow1 : 1 ≤ M^(n-1) := one_le_pow₀ hM
  have hpow : M^(n-2) ≤ M^(n-1) := pow_le_pow_right₀ hM (by omega)
  have hcore1 : 1 ≤ core := by
    have hbase : 1 ≤ (t+1)*M^(n-1) := by nlinarith
    have h := mul_le_mul_of_nonneg_right hp1 (show 0 ≤ (t+1)*M^(n-1) by positivity)
    dsimp [core]
    nlinarith
  have hx' : 10000*core ≤ ‖z‖ := by change 10000*p*(t+1)*M^(n-1) ≤ ‖z‖ at hx; simpa only [core,mul_assoc] using hx
  have hx0 : 0 < ‖z‖ := by linarith
  have hpolycore : N*((n-1 : ℕ) : ℝ)*t*M^(n-2) ≤ core := by
    dsimp [core]
    gcongr <;> linarith
  have hrescore : N*t*M^(n-1) ≤ core := by
    dsimp [core]
    gcongr <;> linarith
  have hpoly : N*((n-1 : ℕ) : ℝ)*t*M^(n-2) ≤ ‖z‖ := by linarith
  have hres : N*t*M^(n-1)+9 ≤ ‖z‖/512 := by linarith
  let A : ℂ := -(4 : ℂ)*Complex.I*z
  have hA : ‖A‖ = 4*‖z‖ := by simp only [A,norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have hAn : A ≠ 0 := norm_pos_iff.mp (by rw [hA]; positivity)
  have hdiff : ∀ w ∈ closedBall b (1/1024), DifferentiableAt ℂ (modelDerivative m t) w :=
    fun w _ => (modelDerivative_hasDerivAt m t w).differentiableAt
  have hbound : ∀ w ∈ closedBall b (1/1024), ‖deriv (modelDerivative m t) w-A‖ ≤ ‖A‖/2 := by
    intro w hw
    have hd : ‖w-b‖ ≤ (1/1024 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hnorm : ‖w‖ ≤ M := by
      have h := norm_add_le (w-b) b
      rw [sub_add_cancel] at h
      linarith
    have he := Complex.norm_exp_sub_one_le (x := 4*(w-b)) (by
      rw [norm_mul,Complex.norm_ofNat]; linarith : ‖4*(w-b)‖ ≤ 1)
    have hexp : ‖Complex.exp (4*(w-b))-1‖ ≤ (1/128 : ℝ) := by
      rw [norm_mul,Complex.norm_ofNat] at he
      linarith
    have heW : Complex.exp (4*w) = Complex.exp (4*b)*Complex.exp (4*(w-b)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h16 : 16*(Real.pi : ℂ)*Complex.exp (4*w) =
        (4*Complex.I*z)*Complex.exp (4*(w-b)) := by
      calc
        _ = 4*(4*(Real.pi : ℂ)*Complex.exp (4*b))*Complex.exp (4*(w-b)) := by rw [heW]; ring
        _ = _ := by rw [hanchor]; ring
    have hid : deriv (modelDerivative m t) w-A =
        (n : ℂ)*((n-1 : ℕ) : ℂ)*(t : ℂ)*w^(n-2)-
          (4*Complex.I*z)*(Complex.exp (4*(w-b))-1) := by
      rw [(modelDerivative_hasDerivAt m t w).deriv,h16]
      dsimp [A,n]
      ring
    rw [hid,hA]
    have hnrm := norm_sub_le ((n : ℂ)*((n-1 : ℕ) : ℂ)*(t : ℂ)*w^(n-2))
      ((4*Complex.I*z)*(Complex.exp (4*(w-b))-1))
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,Complex.norm_I,mul_one] at hnrm
    have hp := pow_le_pow_left₀ (norm_nonneg w) hnorm (n-2)
    have hm' := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ (n : ℝ)*((n-1 : ℕ) : ℝ)*t by positivity)
    have hg := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 4*‖z‖ by positivity)
    change N*((n-1 : ℕ) : ℝ)*t*‖w‖^(n-2) ≤ N*((n-1 : ℕ) : ℝ)*t*M^(n-2) at hm'
    nlinarith
  have hc : modelDerivative m t b = (n : ℂ)*(t : ℂ)*b^(n-1)+9-Complex.I*z := by
    unfold modelDerivative
    rw [hanchor]
  have htarget : -(Complex.I*z) ∈ closedBall (modelDerivative m t b) (‖A‖*(1/1024)/2) := by
    rw [mem_closedBall,dist_eq_norm,hc,hA]
    have he : -(Complex.I*z)-((n : ℂ)*(t : ℂ)*b^(n-1)+9-Complex.I*z) =
        -((n : ℂ)*(t : ℂ)*b^(n-1)+9) := by ring
    rw [he,norm_neg]
    have hnorm := norm_add_le ((n : ℂ)*(t : ℂ)*b^(n-1)) (9 : ℂ)
    simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at hnorm
    have hp := pow_le_pow_left₀ (norm_nonneg b) (hb.trans (by linarith : M-1 ≤ M)) (n-1)
    have hm' := mul_le_mul_of_nonneg_left hp (show 0 ≤ (n : ℝ)*t by positivity)
    change N*t*‖b‖^(n-1) ≤ N*t*M^(n-1) at hm'
    nlinarith
  obtain ⟨w,hw,hroot⟩ := scalar_ball_surj (modelDerivative m t) b A (1/1024)
    (by norm_num) hAn hdiff hbound htarget
  refine ⟨w,⟨hw,hroot⟩,?_⟩
  intro v hv
  exact scalar_ball_injective (modelDerivative m t) b A (1/1024) hAn hdiff hbound hv.1 hw (hv.2.trans hroot.symm)

theorem lower_half_circle_saddle (m : ℕ) (hm : 0 < m) (t a : ℝ)
    (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hscale : 10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1)*(a+2)^(2*m-1) ≤ 4*Real.pi*Real.exp (4*a))
    (z : ℂ) (hz : z.im ≤ 0) (hn : ‖z‖ = 4*Real.pi*Real.exp (4*a)) :
    ∃! w, w ∈ closedBall (RiemannQuarticComplexModelSaddle.complexAnchor z) (1/1024) ∧
      modelDerivative m t w = -(Complex.I*z) := by
  have hx0 : 0 < ‖z‖ := by rw [hn]; positivity
  exact anchored_complex_saddle m hm t (a+2) z ht (by linarith) (by simpa only [hn] using hscale)
    _ (RiemannQuarticComplexModelSaddle.complexAnchor_geometry a ha z hz hn).2.2
    (RiemannQuarticComplexModelSaddle.complexAnchor_spec z (norm_pos_iff.mp hx0))

theorem eventually_far_scale (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ a : ℝ in atTop,
      10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1)*(a+2)^(2*m-1) ≤ 4*Real.pi*Real.exp (4*a) := by
  let C : ℝ := 10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1)*2^(2*m-1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h := ((isLittleO_pow_exp_pos_mul_atTop (2*m-1) (b := 4) (by norm_num)).const_mul_left C).bound
    (show 0 < 4*Real.pi by positivity)
  filter_upwards [h,eventually_ge_atTop (2 : ℝ)] with a hb ha
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hb
  have hpoly : (a+2)^(2*m-1) ≤ 2^(2*m-1)*a^(2*m-1) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by linarith : 0 ≤ a+2) (by linarith : a+2 ≤ 2*a) (2*m-1)
  have hprod := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ 10000*((((2*m : ℕ) : ℝ)+1)^2)*(t+1) by positivity)
  have hc : C*a^(2*m-1) ≤ 4*Real.pi*Real.exp (4*a) := (le_abs_self _).trans hb
  exact hprod.trans (by convert hc using 1 <;> dsimp [C] <;> ring)

theorem eventually_lower_half_circle_saddle (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∀ z : ℂ, z.im ≤ 0 → ‖z‖ = 4*Real.pi*Real.exp (4*a) →
      ∃! w, w ∈ closedBall (RiemannQuarticComplexModelSaddle.complexAnchor z) (1/1024) ∧
        modelDerivative m t w = -(Complex.I*z) := by
  filter_upwards [eventually_far_scale m t ht,eventually_ge_atTop (0 : ℝ)] with a hs ha
  exact fun z hz hn => lower_half_circle_saddle m hm t a ht ha hs z hz hn

end OperatorDerivativeRewrite.Foundation.RiemannEvenFarModelSaddle
