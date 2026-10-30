import Foundation.CubeLimitComplementGap

/-! A rank-one comparison used only for the actual finite stationary gap bridge. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubeRankOneComparison
open CubeChordOperator

variable (B : ChordL2 →L[ℝ] ChordL2) (h w : ChordL2) (r κ : ℝ)

theorem upper_complement (hs : B.adjoint=B) (hh : ‖h‖=1) (hf : B h=h) (hr : r<1)
    (hu : ∀ x, inner ℝ (B x) x ≤ r*‖x‖^2+κ*(inner ℝ w x)^2)
    (f : ChordL2) (ho : inner ℝ f h=0) : inner ℝ (B f) f ≤ r*‖f‖^2 := by
  have hw : inner ℝ w h ≠ 0 := by
    intro hz
    have hb := hu h
    rw [hf,real_inner_self_eq_norm_sq,hh,hz] at hb
    norm_num at hb
    linarith
  let a : ℝ := inner ℝ w f/inner ℝ w h
  let x := f-a • h
  have hwh : inner ℝ w x=0 := by
    rw [show x=f-a • h from rfl,inner_sub_right,real_inner_smul_right]
    dsimp only [a]
    rw [div_mul_cancel₀ _ hw,sub_self]
  have hfh : inner ℝ h f=0 := by rw [real_inner_comm,ho]
  have hBfh : inner ℝ (B f) h=0 := by
    have he := ContinuousLinearMap.adjoint_inner_right B f h
    rw [hs,hf,ho] at he
    exact he.symm
  have hn : ‖x‖^2=‖f‖^2+a^2 := by
    rw [show x=f-a • h from rfl,norm_sub_sq_real,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,hh,real_inner_smul_right,ho]
    ring
  have hx : inner ℝ (B x) x=inner ℝ (B f) f+a^2 := by
    simp only [x,map_sub,map_smul,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_smul_right,hf,hBfh,hfh,real_inner_self_eq_norm_sq,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs,hh]
    ring
  have hb := hu x
  rw [hwh,hx,hn] at hb
  have hp := mul_nonneg (sub_nonneg.mpr hr.le) (sq_nonneg a)
  nlinarith

def remainder : ChordL2 →L[ℝ] ChordL2 := B-InnerProductSpace.rankOne ℝ h h

theorem remainder_apply (f : ChordL2) : remainder B h f=B f-inner ℝ h f • h := rfl

theorem remainder_symmetric (hs : B.adjoint=B) : (remainder B h).IsSymmetric := by
  intro f g
  have he := ContinuousLinearMap.adjoint_inner_right (remainder B h) f g
  have ha : (remainder B h).adjoint=remainder B h := by
    simp only [remainder,map_sub,InnerProductSpace.adjoint_rankOne,hs]
  rw [ha] at he
  exact he.symm

theorem complement_bound (hs : B.adjoint=B) (hh : ‖h‖=1) (hf : B h=h)
    (hr0 : 0≤r) (hr : r<1)
    (hu : ∀ x, inner ℝ (B x) x ≤ r*‖x‖^2+κ*(inner ℝ w x)^2)
    (hl : ∀ x, -r*‖x‖^2 ≤ inner ℝ (B x) x)
    (f : ChordL2) (ho : inner ℝ f h=0) : ‖B f‖ ≤ r*‖f‖ := by
  have hq (x : ChordL2) (hx : inner ℝ x h=0) : |inner ℝ (B x) x| ≤ r*‖x‖^2 := by
    apply abs_le.mpr
    exact ⟨by simpa using hl x,upper_complement B h w r κ hs hh hf hr hu x hx⟩
  have hform (v : ChordL2) : |inner ℝ (remainder B h v) v| ≤ r*‖v‖^2 := by
    let a := inner ℝ h v
    let e := v-a • h
    have hcomm : inner ℝ v h=a := (real_inner_comm v h).symm
    have he : inner ℝ e h=0 := by
      rw [show e=v-a • h from rfl,inner_sub_left,real_inner_smul_left,
        real_inner_self_eq_norm_sq,hh,hcomm]
      ring
    have hBvh : inner ℝ (B v) h=a := by
      have ht := ContinuousLinearMap.adjoint_inner_right B v h
      rw [hs,hf,hcomm] at ht
      exact ht.symm
    have hnorm : ‖e‖^2=‖v‖^2-a^2 := by
      rw [show e=v-a • h from rfl,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
        mul_pow,sq_abs,hh,real_inner_smul_right,hcomm]
      ring
    have heq : inner ℝ (remainder B h v) v=inner ℝ (B e) e := by
      simp only [remainder_apply,e,map_sub,map_smul,inner_sub_left,inner_sub_right,
        real_inner_smul_left,real_inner_smul_right,hf,hBvh,real_inner_self_eq_norm_sq,
        norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hh]
      change inner ℝ (B v) v-a*a=inner ℝ (B v) v-a*a-(a*a-a^2*1^2)
      ring
    rw [heq]
    exact (hq e he).trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a] : ‖e‖^2≤‖v‖^2) hr0)
  have hnorm : ‖remainder B h‖ ≤ r := by
    rw [(remainder B h).norm_eq_iSup_rayleighQuotient (remainder_symmetric B h hs)]
    apply ciSup_le
    intro v
    by_cases hv : v=0
    · simp [hv,ContinuousLinearMap.rayleighQuotient,hr0]
    · have hn : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
      simpa only [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
        RCLike.re_to_real,abs_div,abs_of_pos hn,div_le_iff₀ hn] using hform v
  have hfo : inner ℝ h f=0 := by rw [real_inner_comm]; exact ho
  have he : remainder B h f=B f := by rw [remainder_apply,hfo,zero_smul,sub_zero]
  rw [← he]
  exact ((remainder B h).le_opNorm f).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg f))

end OperatorDerivativeRewrite.Foundation.CubeRankOneComparison
