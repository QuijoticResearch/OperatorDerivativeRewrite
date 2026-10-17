import Foundation.SpectralShearHeatFlow
import Foundation.NormalizedShellHeat

/-! Actual Fourier coefficient energies of the exact shear solution, with a
two-sector centroid ratio strictly above one at every finite time. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ShearSpectralCentroid
open FiniteFourierDifferentialTrace FiniteFourierSynthesis ABCFourierProfile
open SpectralShearHeatFlow
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def sector (k : Wave) : Fin 2 := if k 2 = 0 then 0 else 1

theorem sector_wave (n : ℕ) : sector (wave n) = 0 := by simp [sector, wave]

theorem sector_other : sector (frequency 2) = 1 := by norm_num [sector, frequency]

theorem sector_antipodal (k : Wave) : sector (-k) = sector k := by
  simp [sector, Pi.neg_apply]

theorem profile_coeff_outside (n : ℕ) (a b c : ℝ) (k : Wave)
    (h1 : wave 1 ≠ k) (h2 : -wave 1 ≠ k) (h3 : frequency 2 ≠ k)
    (h4 : -frequency 2 ≠ k) (h5 : wave n ≠ k) (h6 : -wave n ≠ k) :
    (profile n a b c).coeff k = 0 := by
  have he : frequency 1 = wave 1 := rfl
  simp [profile, sine, highSine, he, Finsupp.single_apply, h1, h2, h3, h4, h5, h6]

theorem wave_injective : Function.Injective wave := by
  intro n m h
  have hh := congrArg (fun k : Wave => k 1) h
  simpa [wave] using hh

theorem wave_neg_ne (n m : ℕ) (hm : 0 < m) : -wave n ≠ wave m := by
  intro h
  have hh := congrArg (fun k : Wave => k 1) h
  simp [wave, Pi.neg_apply] at hh
  omega

theorem wave_other_ne (n : ℕ) : wave n ≠ frequency 2 := by
  intro h
  have hh := congrArg (fun k : Wave => k 2) h
  norm_num [wave, frequency] at hh

theorem neg_wave_other_ne (n : ℕ) : -wave n ≠ frequency 2 := by
  intro h
  have hh := congrArg (fun k : Wave => k 2) h
  norm_num [wave, frequency, Pi.neg_apply] at hh

theorem high_coeff (n m : ℕ) (hm : 0 < m) :
    (highSine n).coeff (wave m) = if n = m then -Complex.I/2 else 0 := by
  simp [highSine, Finsupp.single_apply, wave_injective.eq_iff, wave_neg_ne n m hm]

theorem other_coeff_wave (m : ℕ) : (sine 2).coeff (wave m) = 0 := by
  have h1 : frequency 2 ≠ wave m := (wave_other_ne m).symm
  have h2 : -frequency 2 ≠ wave m := by
    intro h
    have hh := congrArg (fun k : Wave => k 2) h
    norm_num [frequency, wave, Pi.neg_apply] at hh
  simp [sine, Finsupp.single_apply, h1, h2]

theorem profile_coeff_low (n : ℕ) (hn : 2 ≤ n) (a b c : ℝ) :
    (profile n a b c).coeff (wave 1) = (a : ℂ)*(-Complex.I/2) := by
  have hs : sine 1 = highSine 1 := rfl
  have hn1 : n ≠ 1 := by omega
  simp [profile, hs, high_coeff _ _ (by omega : 0 < (1 : ℕ)),
    other_coeff_wave, hn1, smul_eq_mul]

theorem profile_coeff_high (n : ℕ) (hn : 2 ≤ n) (a b c : ℝ) :
    (profile n a b c).coeff (wave n) = (c : ℂ)*(-Complex.I/2) := by
  have hs : sine 1 = highSine 1 := rfl
  have hn1 : 1 ≠ n := by omega
  have hn0 : 0 < n := by omega
  simp [profile, hs, high_coeff _ _ hn0, other_coeff_wave, hn1, smul_eq_mul]

theorem profile_coeff_other (n : ℕ) (a b c : ℝ) :
    (profile n a b c).coeff (frequency 2) = (b : ℂ)*(-Complex.I/2) := by
  have hs : sine 1 = highSine 1 := rfl
  have h2 : -frequency 2 ≠ frequency 2 := by
    intro h
    have hh := congrArg (fun k : Wave => k 2) h
    norm_num [frequency, Pi.neg_apply] at hh
  have h12 : frequency 1 ≠ frequency 2 := by decide
  have hn12 : -frequency 1 ≠ frequency 2 := by decide
  simp [profile, hs, highSine, sine, Finsupp.single_apply,
    wave_other_ne, neg_wave_other_ne, h2, h12, hn12, smul_eq_mul]

def twicePairEnergy (f : Fourier) (k : Wave) : ℝ :=
  4*((k 0 : ℝ)^2+(k 1 : ℝ)^2+(k 2 : ℝ)^2)*Complex.normSq (f.coeff k)

theorem coefficient_normSq (a : ℝ) : Complex.normSq ((a : ℂ)*(-Complex.I/2)) = a^2/4 := by
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem twice_pair_identity (f : Fourier) (hf : FiniteFourierReality.Hermitian f) (k : Wave) :
    twicePairEnergy f k =
      2*((k 0 : ℝ)^2+(k 1 : ℝ)^2+(k 2 : ℝ)^2)*
        (Complex.normSq (f.coeff k)+Complex.normSq (f.coeff (-k))) := by
  rw [hf k]
  simp [twicePairEnergy, Complex.normSq, Complex.conj_re, Complex.conj_im]
  ring

theorem low_energy (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    twicePairEnergy (state n nu t 0) (wave 1) = 4*(decay nu 1 t)^2 := by
  change twicePairEnergy (profile n _ _ _) (wave 1) = _
  rw [twicePairEnergy, profile_coeff_low n hn, coefficient_normSq]
  norm_num [wave]
  ring

theorem other_energy (n : ℕ) (nu t : ℝ) :
    twicePairEnergy (state n nu t 0) (frequency 2) = (decay nu 1 t)^2 := by
  change twicePairEnergy (profile n _ _ _) (frequency 2) = _
  rw [twicePairEnergy, profile_coeff_other, coefficient_normSq]
  norm_num [frequency]
  ring

theorem high_energy (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    twicePairEnergy (state n nu t 0) (wave n) = (n : ℝ)^2*(decay nu n t)^2 := by
  change twicePairEnergy (profile n _ _ _) (wave n) = _
  rw [twicePairEnergy, profile_coeff_high n hn, coefficient_normSq]
  norm_num [wave]
  ring

def lowA (n : ℕ) (nu t : ℝ) : ℝ := twicePairEnergy (state n nu t 0) (wave 1)
def lowB (n : ℕ) (nu t : ℝ) : ℝ := twicePairEnergy (state n nu t 0) (frequency 2)
def high (n : ℕ) (nu t : ℝ) : ℝ := twicePairEnergy (state n nu t 0) (wave n)

def centroidRatio (a b c K : ℝ) : ℝ :=
  (a+b+c)*(a+K*c-b)/((a+b+K*c)*(a+c-b))

theorem centroid_gt_one (a b c K : ℝ) (hb : 0 < b) (hba : b < a)
    (hc : 0 < c) (hK : 1 < K) : 1 < centroidRatio a b c K := by
  have ha : 0 < a := hb.trans hba
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hdiff : 0 < a+c-b := by linarith
  have hden : 0 < (a+b+K*c)*(a+c-b) := mul_pos (by positivity) hdiff
  rw [centroidRatio, lt_div_iff₀ hden]
  have hp : 0 < 2*b*c*(K-1) := by positivity
  nlinarith

theorem actual_centroid_gt_one (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    1 < centroidRatio (lowA n nu t) (lowB n nu t) (high n nu t) ((n : ℝ)^2) := by
  have hq : 0 < decay nu 1 t := Real.exp_pos _
  have hr : 0 < decay nu n t := Real.exp_pos _
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [lowA, lowB, high, low_energy n hn, other_energy, high_energy n hn]
  refine centroid_gt_one _ _ _ _ ?_ ?_ ?_ ?_
  · positivity
  · nlinarith [sq_pos_of_pos hq]
  · positivity
  · nlinarith

theorem low_normalized_excess (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    lowA n nu t/(lowA n nu t+lowB n nu t)-1/2 = (3 : ℝ)/10 := by
  have hq : decay nu 1 t ≠ 0 := ne_of_gt (Real.exp_pos _)
  simp only [lowA, lowB, low_energy n hn, other_energy]
  field_simp
  <;> ring

theorem high_normalized_share (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    high n nu t/(high n nu t+0) = 1 := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < high n nu t := by
    rw [high, high_energy n hn]
    have hp : 0 < decay nu n t := Real.exp_pos _
    positivity
  simp [ne_of_gt hh]

theorem low_anisotropy_exact (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    NormalizedShellHeat.anisotropy (![lowA n nu t, lowB n nu t] : Fin 2 → ℝ) =
      (9 : ℝ)/50 := by
  have hq : decay nu 1 t ≠ 0 := ne_of_gt (Real.exp_pos _)
  simp [NormalizedShellHeat.anisotropy, NormalizedShellHeat.excess,
    NormalizedShellHeat.share, NormalizedShellHeat.total, Fin.sum_univ_succ,
    lowA, lowB, low_energy n hn, other_energy]
  field_simp
  <;> ring

theorem high_anisotropy_exact (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    NormalizedShellHeat.anisotropy (![high n nu t, 0] : Fin 2 → ℝ) = (1 : ℝ)/2 := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < high n nu t := by
    rw [high, high_energy n hn]
    have hp : 0 < decay nu n t := Real.exp_pos _
    positivity
  simp [NormalizedShellHeat.anisotropy, NormalizedShellHeat.excess,
    NormalizedShellHeat.share, NormalizedShellHeat.total, Fin.sum_univ_succ, ne_of_gt hh]
  <;> norm_num

def sourceRatio (a b c K : ℝ) : ℝ :=
  let T := a+b+c
  let e0 := (a+c)/T-1/2
  let e1 := b/T-1/2
  (e0*(a+K*c)/T+e1*b/T)/(((a+b+K*c)/T)*(e0^2+e1^2))

theorem sourceRatio_eq (a b c K : ℝ) (hb : 0 < b) (hba : b < a)
    (hc : 0 < c) (hK : 1 < K) : sourceRatio a b c K = centroidRatio a b c K := by
  have ha : 0 < a := hb.trans hba
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  have hT : a+b+c ≠ 0 := ne_of_gt (by positivity)
  have hD : a+b+K*c ≠ 0 := ne_of_gt (by positivity)
  have hd : a+c-b ≠ 0 := ne_of_gt (by linarith : 0 < a+c-b)
  unfold sourceRatio centroidRatio
  dsimp only
  have he0 : (a+c)/(a+b+c)-1/2 = (a+c-b)/(2*(a+b+c)) := by
    field_simp
    <;> ring
  have he1 : b/(a+b+c)-1/2 = -(a+c-b)/(2*(a+b+c)) := by
    field_simp
    <;> ring
  rw [he0, he1]
  field_simp
  <;> ring

theorem actual_sourceRatio_gt_one (n : ℕ) (hn : 2 ≤ n) (nu t : ℝ) :
    1 < sourceRatio (lowA n nu t) (lowB n nu t) (high n nu t) ((n : ℝ)^2) := by
  have hq : 0 < decay nu 1 t := Real.exp_pos _
  have hr : 0 < decay nu n t := Real.exp_pos _
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 < lowB n nu t := by rw [lowB, other_energy]; positivity
  have hba : lowB n nu t < lowA n nu t := by
    rw [lowA, lowB, low_energy n hn, other_energy]
    nlinarith [sq_pos_of_pos hq]
  have hc : 0 < high n nu t := by rw [high, high_energy n hn]; positivity
  have hK : 1 < (n : ℝ)^2 := by nlinarith
  rw [sourceRatio_eq _ _ _ _ hb hba hc hK]
  exact actual_centroid_gt_one n hn nu t

theorem initial_ratio_exact (nu : ℝ) :
    sourceRatio (lowA 2 nu 0) (lowB 2 nu 0) (high 2 nu 0) 4 = (57 : ℝ)/49 := by
  simp only [lowA, lowB, high, low_energy 2 (by omega), other_energy,
    high_energy 2 (by omega)]
  norm_num [sourceRatio, decay]

theorem two_shell_identity (w low high phiLow phiHigh : ℝ) :
    (w*low+(1-w)*high)*(w*phiLow+(1-w)*phiHigh)-
      (w*low*phiLow+(1-w)*high*phiHigh) =
        w*(1-w)*(high-low)*(phiLow-phiHigh) := by ring

end OperatorDerivativeRewrite.Foundation.ShearSpectralCentroid
