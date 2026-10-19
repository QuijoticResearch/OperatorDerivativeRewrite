import Foundation.RiemannQuarticCellPhase
import Foundation.RiemannQuarticCellDomain
import Foundation.RiemannQuarticChannelJets
import Foundation.RiemannQuarticStoredJets

/-! Uniform interval coefficients of the actual four-term, three-channel
integrands on quadrature cell50. No numerical derivative bound is assumed. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFullCell
open RiemannQuarticDyadic RiemannQuarticIntervalExp RiemannQuarticIntervalChecks
open RiemannQuarticPhaseJets RiemannQuarticArithmeticJets RiemannQuarticChannelJets
open RiemannQuarticCellDomain RiemannQuarticTaylorJets RiemannQuarticRealCertificate
open RiemannQuarticStoredJets

abbrev U : Box := RiemannQuarticCellPhase.cellU
abbrev E : Box := RiemannQuarticCellPhase.cellE
def P : Box := piBox 160
def X : Box := rational (632083/10000) 160
def B (m a : ℕ) : Box :=
  scaledExpHorner (phaseJet U E P (rational a 160) m 160 0) 160 48 16
def G (m a n : ℕ) : Box :=
  expJetStored (fun i => phaseJet U E P (rational a 160) m 160 i) (B m a) 160 n
def W (n : ℕ) : Box := weightJet P (fun m => G m 9 n) (fun m => G m 5 n) 4 160
def I (k n : ℕ) : Box :=
  integrandJet U X (range (-1) 1 160, range (-1) 1 160) W k 160 n

theorem G_eq_original (m a n : ℕ) :
    G m a n=phaseExpJet U E P (rational a 160) (B m a) m 160 n :=
  expJetStored_eq (fun i => phaseJet U E P (rational a 160) m 160 i) (B m a) 160 n

theorem uniform_G (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100))
    (m a n : ℕ) (hm : m ≤ 4) (ha : a ≤ 9) :
    coefficient (fun v => Real.exp (phase m a v)) n u ∈ G m a n := by
  have h := RiemannQuarticCellPhase.uniform_inputs u hu
  have huWhole : u ∈ Icc (0 : ℝ) (8/5) := by constructor <;> linarith [hu.1, hu.2]
  have ha' : (a : ℝ) ∈ Icc (0 : ℝ) 9 := by
    constructor
    · exact Nat.cast_nonneg a
    · exact_mod_cast ha
  have haBox : (a : ℝ) ∈ rational a 160 := by
    simpa only [Rat.cast_natCast] using rational_mem (a : ℚ) 160
  have hpBox : Real.pi ∈ P := pi_mem 160
  have hf0 : phase m a u ∈ phaseJet U E P (rational a 160) m 160 0 := by
    simpa only [coefficient_zero] using phaseJet_mem h.1 h.2.1 hpBox haBox m 160 0
  have hb : Real.exp (phase m a u) ∈ B m a :=
    scaledExpHorner_mem hf0 160 48 16 (by norm_num)
      (phase_scaled_small m hm a u ha' huWhole)
  rw [G_eq_original]
  exact phaseExpJet_mem h.1 h.2.1 (pi_mem 160) haBox m 160 n hb

theorem uniform_W (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100)) (n : ℕ) :
    coefficient (weight 4) n u ∈ W n := by
  apply weightJet_mem (pi_mem 160)
  · intro m hm0 hm4
    exact uniform_G u hu m 9 n hm4 (by norm_num)
  · intro m hm0 hm4
    exact uniform_G u hu m 5 n hm4 (by norm_num)

theorem uniform_I (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100))
    (k n : ℕ) (hk : k ≤ 2) :
    coefficient (realIntegrand 4 k (632083/10000)) n u ∈ I k n := by
  have h := RiemannQuarticCellPhase.uniform_inputs u hu
  have hx : (632083/10000 : ℝ) ∈ X := by simpa [X] using rational_mem (632083/10000) 160
  have hc : Real.cos ((632083/10000 : ℝ)*u) ∈ range (-1) 1 160 := by
    apply range_mem
    · simpa using Real.neg_one_le_cos ((632083/10000 : ℝ)*u)
    · simpa using Real.cos_le_one ((632083/10000 : ℝ)*u)
  have hs : Real.sin ((632083/10000 : ℝ)*u) ∈ range (-1) 1 160 := by
    apply range_mem
    · simpa using Real.neg_one_le_sin ((632083/10000 : ℝ)*u)
    · simpa using Real.sin_le_one ((632083/10000 : ℝ)*u)
  exact integrandJet_mem hx h.1 hc hs 4 k 160 n hk W
    (fun i _ => uniform_W u hu i)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFullCell
