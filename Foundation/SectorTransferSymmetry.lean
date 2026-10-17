import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Finite Fourier versions of the source's sector transfer: homogeneity and a transverse shear. -/
noncomputable section
open Finset
namespace OperatorDerivativeRewrite.Foundation.SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
abbrev Wave := Fin 3 → ℤ
abbrev Vector := Fin 3 → ℝ
abbrev Field := Wave → Vector

def waveSquare (k : Wave) : ℝ := ∑ i : Fin 3, (k i : ℝ)^2
def dotWave (k : Wave) (v : Vector) : ℝ := ∑ i : Fin 3, (k i : ℝ)*v i
def dotVector (v w : Vector) : ℝ := ∑ i : Fin 3, v i*w i
def scale (a : ℝ) (V : Field) : Field := fun k i => a*V k i
def modeEnergy (V : Field) (k : Wave) : ℝ := waveSquare k*dotVector (V k) (V k)
def energy (K : Finset Wave) (V : Field) : ℝ := ∑ k ∈ K, modeEnergy V k
def sectorEnergy {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) (j : Fin J) : ℝ :=
  ∑ k ∈ K, if s k=j then modeEnergy V k else 0
def fraction {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) (j : Fin J) : ℝ :=
  sectorEnergy K s V j/energy K V
def concentration {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) : ℝ :=
  ∑ j, (fraction K s V j)^2
def triadTerm (V : Field) (k p q : Wave) : ℝ :=
  if p+q=k then dotWave q (V p)*dotVector (V k) (V q) else 0
def transfer (K : Finset Wave) (V : Field) (k : Wave) : ℝ :=
  2*waveSquare k*∑ p ∈ K, ∑ q ∈ K, triadTerm V k p q
def fullTransfer (V : Field) (k : Wave) : ℝ :=
  2*waveSquare k*∑' p : Wave, dotWave (k-p) (V p)*dotVector (V k) (V (k-p))
def totalTransfer (K : Finset Wave) (V : Field) : ℝ := ∑ k ∈ K, transfer K V k
def sectorTransfer {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) (j : Fin J) : ℝ :=
  ∑ k ∈ K, if s k=j then transfer K V k else 0
def sigma {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) : ℝ :=
  (2/energy K V)*∑ j, fraction K s V j*(sectorTransfer K s V j-fraction K s V j*totalTransfer K V)
def rate {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) : ℝ :=
  -sigma K s V/(concentration K s V-1/(J : ℝ))

theorem dotWave_scale (a : ℝ) (V : Field) (q p : Wave) :
    dotWave q (scale a V p) = a*dotWave q (V p) := by
  simp only [dotWave,scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dotVector_scale (a : ℝ) (V : Field) (p q : Wave) :
    dotVector (scale a V p) (scale a V q) = a^2*dotVector (V p) (V q) := by
  simp only [dotVector,scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modeEnergy_scale (a : ℝ) (V : Field) (k : Wave) :
    modeEnergy (scale a V) k = a^2*modeEnergy V k := by
  rw [modeEnergy,dotVector_scale]
  unfold modeEnergy
  ring

theorem energy_scale (K : Finset Wave) (a : ℝ) (V : Field) :
    energy K (scale a V) = a^2*energy K V := by
  simp only [energy,modeEnergy_scale,Finset.mul_sum]

theorem sectorEnergy_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (V : Field) (j : Fin J) :
    sectorEnergy K s (scale a V) j = a^2*sectorEnergy K s V j := by
  simp only [sectorEnergy,modeEnergy_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem fraction_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (ha : a≠0) (V : Field) (j : Fin J) :
    fraction K s (scale a V) j = fraction K s V j := by
  rw [fraction,sectorEnergy_scale,energy_scale]
  by_cases he : energy K V=0
  · simp [he,fraction]
  · unfold fraction
    field_simp [ha,he]

theorem concentration_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (ha : a≠0) (V : Field) :
    concentration K s (scale a V) = concentration K s V := by
  simp only [concentration,fraction_scale K s a ha]

theorem triadTerm_scale (a : ℝ) (V : Field) (k p q : Wave) :
    triadTerm (scale a V) k p q = a^3*triadTerm V k p q := by
  unfold triadTerm
  rw [dotWave_scale,dotVector_scale]
  split_ifs <;> ring

theorem transfer_scale (K : Finset Wave) (a : ℝ) (V : Field) (k : Wave) :
    transfer K (scale a V) k = a^3*transfer K V k := by
  simp only [transfer,triadTerm_scale,← Finset.mul_sum]
  ring

theorem totalTransfer_scale (K : Finset Wave) (a : ℝ) (V : Field) :
    totalTransfer K (scale a V) = a^3*totalTransfer K V := by
  simp only [totalTransfer,transfer_scale,Finset.mul_sum]

theorem sectorTransfer_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (V : Field) (j : Fin J) :
    sectorTransfer K s (scale a V) j = a^3*sectorTransfer K s V j := by
  simp only [sectorTransfer,transfer_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem sigma_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (ha : a≠0) (V : Field) : sigma K s (scale a V) = a*sigma K s V := by
  unfold sigma
  simp_rw [energy_scale,fraction_scale K s a ha,sectorTransfer_scale,totalTransfer_scale]
  have hs : (∑ j, fraction K s V j*(a^3*sectorTransfer K s V j-
      fraction K s V j*(a^3*totalTransfer K V))) =
      a^3*∑ j, fraction K s V j*(sectorTransfer K s V j-fraction K s V j*totalTransfer K V) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  by_cases he : energy K V=0
  · simp [he]
  · field_simp [ha,he] <;> ring_nf <;>
      (apply Finset.sum_congr rfl; intro j _; ring)

theorem rate_scale {J : ℕ} (K : Finset Wave) (s : Wave → Fin J)
    (a : ℝ) (ha : a≠0) (V : Field) : rate K s (scale a V) = a*rate K s V := by
  rw [rate,sigma_scale K s a ha,concentration_scale K s a ha]
  unfold rate
  ring

theorem rate_neg {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field) :
    rate K s (fun k i => -V k i) = -rate K s V := by
  have hs : scale (-1) V = (fun k i => -V k i) := by funext k i; simp [scale]
  have h := rate_scale K s (-1) (by norm_num) V
  rw [hs] at h
  simpa only [neg_one_mul] using h

theorem not_both_positive {J : ℕ} (K : Finset Wave) (s : Wave → Fin J) (V : Field)
    (c : ℝ) (hc : 0<c) : ¬ (c≤rate K s V ∧ c≤rate K s (fun k i => -V k i)) := by
  rw [rate_neg]
  rintro ⟨h1,h2⟩
  linarith

def plus : Wave := ![1,0,0]
def modes : Finset Wave := {plus,-plus}
def polarization (k : Wave) : Vector :=
  ((if k=plus then (1 : ℝ) else 0)-(if k= -plus then 1 else 0)) • ![0,1,0]

theorem plus_ne_neg : plus ≠ -plus := by
  intro h
  have h0 := congrFun h 0
  norm_num [plus] at h0

theorem polarization_plus : polarization plus = ![0,1,0] := by
  simp [polarization,plus_ne_neg]

theorem polarization_minus : polarization (-plus) = ![0,-1,0] := by
  ext i
  fin_cases i <;> simp [polarization,Ne.symm plus_ne_neg]

theorem polarization_off (k : Wave) (hp : k≠plus) (hm : k≠ -plus) : polarization k = 0 := by
  simp [polarization,hp,hm]

theorem polarization_odd (k : Wave) : polarization (-k) = -polarization k := by
  by_cases hp : k=plus
  · subst k
    rw [polarization_plus,polarization_minus]
    ext i
    fin_cases i <;> norm_num
  · by_cases hm : k= -plus
    · subst k
      rw [neg_neg,polarization_plus,polarization_minus]
      ext i
      fin_cases i <;> norm_num
    · have hnp : -k≠plus := by intro h; apply hm; simpa using congrArg Neg.neg h
      have hnm : -k≠ -plus := by intro h; apply hp; simpa using congrArg Neg.neg h
      rw [polarization_off k hp hm,polarization_off (-k) hnp hnm,neg_zero]

theorem transverse (k : Wave) : dotWave k (polarization k) = 0 := by
  by_cases hp : k=plus
  · subst k
    rw [polarization_plus]
    norm_num [dotWave,plus,Fin.sum_univ_succ]
  · by_cases hm : k= -plus
    · subst k
      rw [polarization_minus]
      norm_num [dotWave,plus,Fin.sum_univ_succ]
    · simp [polarization_off k hp hm,dotWave]

theorem shear_cross_dot (p q : Wave) (hp : p∈modes) (hq : q∈modes) :
    dotWave q (polarization p) = 0 := by
  simp only [modes,mem_insert,mem_singleton] at hp hq
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;>
    (first | rw [polarization_plus] | rw [polarization_minus]) <;>
    norm_num [dotWave,plus,Fin.sum_univ_succ]

theorem polarization_off_modes (k : Wave) (hk : k∉modes) : polarization k = 0 := by
  simp only [modes,Finset.mem_insert,Finset.mem_singleton,not_or] at hk
  exact polarization_off k hk.1 hk.2

theorem shear_product_zero (k p q : Wave) :
    dotWave q (polarization p)*dotVector (polarization k) (polarization q) = 0 := by
  by_cases hp : p∈modes
  · by_cases hq : q∈modes
    · rw [shear_cross_dot p q hp hq,zero_mul]
    · simp [polarization_off_modes q hq,dotVector]
  · simp [polarization_off_modes p hp,dotWave]

theorem shear_fullTransfer_zero (k : Wave) : fullTransfer polarization k = 0 := by
  simp [fullTransfer,shear_product_zero]

theorem shear_transfer_zero (k : Wave) : transfer modes polarization k = 0 := by
  unfold transfer
  have hz : (∑ p ∈ modes, ∑ q ∈ modes, triadTerm polarization k p q) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    simp [triadTerm,shear_cross_dot p q hp hq]
  rw [hz,mul_zero]

theorem modeEnergy_plus : modeEnergy polarization plus = 1 := by
  unfold modeEnergy
  rw [polarization_plus]
  norm_num [waveSquare,dotVector,plus,Fin.sum_univ_succ]

theorem modeEnergy_minus : modeEnergy polarization (-plus) = 1 := by
  unfold modeEnergy
  rw [polarization_minus]
  norm_num [waveSquare,dotVector,plus,Fin.sum_univ_succ]

theorem shear_energy : energy modes polarization = 2 := by
  norm_num [energy,modes,plus_ne_neg,modeEnergy_plus,modeEnergy_minus]

theorem shear_sectorEnergy {J : ℕ} (s : Wave → Fin J) (j : Fin J) :
    sectorEnergy modes s polarization j =
      (if s plus=j then 1 else 0)+(if s (-plus)=j then 1 else 0) := by
  simp [sectorEnergy,modes,plus_ne_neg,modeEnergy_plus,modeEnergy_minus]

theorem shear_concentration {J : ℕ} (s : Wave → Fin J) :
    concentration modes s polarization = if s plus=s (-plus) then 1 else 1/2 := by
  classical
  simp only [concentration,fraction,shear_energy,shear_sectorEnergy]
  by_cases hab : s plus=s (-plus)
  · simp [hab,Finset.sum_ite_eq']
  · have hterm (j : Fin J) :
        (((if s plus=j then (1 : ℝ) else 0)+(if s (-plus)=j then 1 else 0))/2)^2 =
          (if s plus=j then 1/4 else 0)+(if s (-plus)=j then 1/4 else 0) := by
      split_ifs with h1 h2 <;> norm_num <;> aesop
    simp_rw [hterm]
    simp [Finset.sum_add_distrib,Finset.sum_ite_eq',hab] <;> norm_num

theorem shear_rate_zero {J : ℕ} (s : Wave → Fin J) : rate modes s polarization = 0 := by
  simp [rate,sigma,sectorTransfer,totalTransfer,shear_transfer_zero]

theorem shear_concentrated (s : Wave → Fin 32) :
    1/(32 : ℝ) < concentration modes s polarization := by
  rw [shear_concentration]
  split_ifs <;> norm_num

theorem no_positive_shear_bound (s : Wave → Fin 32) (c : ℝ) (hc : 0<c) :
    ¬ c≤rate modes s polarization := by
  rw [shear_rate_zero]
  exact not_le_of_gt hc

theorem transverse_scale (a : ℝ) (V : Field) (hV : ∀ k, dotWave k (V k)=0) :
    ∀ k, dotWave k (scale a V k)=0 := by
  intro k
  rw [dotWave_scale,hV k,mul_zero]

theorem odd_scale (a : ℝ) (V : Field) (hV : ∀ k, V (-k)= -V k) :
    ∀ k, scale a V (-k)= -scale a V k := by
  intro k
  ext i
  have h := congrFun (hV k) i
  simp only [Pi.neg_apply] at h
  simp [scale,h]

theorem no_universal_positive_bound (s : Wave → Fin 32) (c : ℝ) (hc : 0<c) :
    ¬ ∀ V : Field,
      (∀ k, k∉modes → V k=0) →
      (∀ k, dotWave k (V k)=0) →
      (∀ k, V (-k)= -V k) →
      0<energy modes V →
      1/(32 : ℝ)<concentration modes s V → c≤rate modes s V := by
  intro h
  have hh := h polarization polarization_off_modes transverse polarization_odd
    (by rw [shear_energy]; norm_num) (shear_concentrated s)
  exact no_positive_shear_bound s c hc hh

end OperatorDerivativeRewrite.Foundation.SectorTransferSymmetry
