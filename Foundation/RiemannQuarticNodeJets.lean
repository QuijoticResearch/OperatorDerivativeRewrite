import Foundation.RiemannQuarticBatchJets
import Foundation.RiemannQuarticCellDomain
import Foundation.RiemannQuarticChannelJets

/-! Shared finite coefficient tables for either a whole integration cell or
a point center. All membership statements concern the actual integrand. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticNodeJets
open RiemannQuarticDyadic RiemannQuarticIntervalExp RiemannQuarticIntervalChecks
open RiemannQuarticPhaseJets RiemannQuarticArithmeticJets RiemannQuarticChannelJets
open RiemannQuarticCellDomain RiemannQuarticTaylorJets RiemannQuarticRealCertificate
open RiemannQuarticStoredJets RiemannQuarticBatchJets RiemannQuarticIntervalJets

def P : Box := piBox 192
def X : Box := rational (632083/10000) 192
def zeroBox : Box := rational 0 192
def expFour (U : Box) : Box :=
  scaledExpHorner (mul (rational 4 192) U 192) 192 48 4
def base (U E : Box) (m a : ℕ) : Box :=
  scaledExpHorner (phaseJet U E P (rational a 192) m 192 0) 192 48 16
def phaseTable (U E : Box) (m a q : ℕ) : List Box :=
  stored (fun i => phaseJet U E P (rational a 192) m 192 i) (base U E m a) 192 q
def branches (U E : Box) (a q : ℕ) : List (List Box) :=
  (List.range 4).map (fun i => phaseTable U E (i+1) a q)
def branch (L : List (List Box)) (m n : ℕ) : Box :=
  (L.getD (m-1) []).getD n zeroBox
def weightTable (U : Box) (q : ℕ) : List Box :=
  let E := expFour U
  let L9 := branches U E 9 q
  let L5 := branches U E 5 q
  (List.range (q+1)).map (fun n =>
    weightJet P (fun m => branch L9 m n) (fun m => branch L5 m n) 4 192)
def weights (L : List Box) (n : ℕ) : Box := L.getD n zeroBox
def nodeJet (U : Box) (J : Box × Box) (q k n : ℕ) : Box :=
  let W := weightTable U q
  integrandJet U X J (weights W) k 192 n

theorem getD_map_range {α : Type} (f : ℕ → α) (N n : ℕ) (d : α) (hn : n < N) :
    ((List.range N).map f).getD n d=f n := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hn, Option.map_some, Option.getD_some]

theorem branch_eq (U E : Box) (a q m n : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ 4)
    (hn : n ≤ q) :
    branch (branches U E a q) m n=
      phaseExpJet U E P (rational a 192) (base U E m a) m 192 n := by
  have hm' : m-1 < 4 := by omega
  have heq : m-1+1=m := by omega
  unfold branch branches
  rw [getD_map_range _ 4 (m-1) [] hm', heq]
  exact stored_lower_default_eq _ _ _ 192 q n hn

theorem expFour_mem {u : ℝ} {U : Box} (hu : u ∈ U)
    (hwhole : u ∈ Icc (0 : ℝ) (8/5)) : Real.exp (4*u) ∈ expFour U := by
  have h4 : (4 : ℝ) ∈ rational 4 192 := by simpa using rational_mem 4 192
  exact scaledExpHorner_mem (mul_mem h4 hu 192) 192 48 4 (by norm_num)
    (four_scaled_small u hwhole)

theorem phaseTable_mem {u : ℝ} {U E : Box} (hu : u ∈ U)
    (he : Real.exp (4*u) ∈ E) (hwhole : u ∈ Icc (0 : ℝ) (8/5))
    (m a q n : ℕ) (hm : m ≤ 4) (ha : a ≤ 9) (hn : n ≤ q) :
    coefficient (fun v => Real.exp (phase m a v)) n u ∈
      (phaseTable U E m a q).getD n zeroBox := by
  have ha' : (a : ℝ) ∈ Icc (0 : ℝ) 9 := by
    constructor
    · exact Nat.cast_nonneg a
    · exact_mod_cast ha
  have haBox : (a : ℝ) ∈ rational a 192 := by
    simpa only [Rat.cast_natCast] using rational_mem (a : ℚ) 192
  have hp : Real.pi ∈ P := pi_mem 192
  have hf0 : phase m a u ∈ phaseJet U E P (rational a 192) m 192 0 := by
    simpa only [coefficient_zero] using phaseJet_mem hu he hp haBox m 192 0
  have hb : Real.exp (phase m a u) ∈ base U E m a :=
    scaledExpHorner_mem hf0 192 48 16 (by norm_num)
      (phase_scaled_small m hm a u ha' hwhole)
  rw [phaseTable, stored_lower_default_eq _ _ _ 192 q n hn]
  exact phaseExpJet_mem hu he hp haBox m 192 n hb

theorem weightTable_mem {u : ℝ} {U : Box} (hu : u ∈ U)
    (hwhole : u ∈ Icc (0 : ℝ) (8/5)) (q n : ℕ) (hn : n ≤ q) :
    coefficient (weight 4) n u ∈ weights (weightTable U q) n := by
  have he := expFour_mem hu hwhole
  have hg (m a : ℕ) (hm0 : 1 ≤ m) (hm : m ≤ 4) (ha : a ≤ 9) :
      coefficient (fun v => Real.exp (phase m a v)) n u ∈
        branch (branches U (expFour U) a q) m n := by
    unfold branch branches
    rw [getD_map_range _ 4 (m-1) [] (by omega), show m-1+1=m by omega]
    exact phaseTable_mem hu he hwhole m a q n hm ha hn
  unfold weights weightTable
  rw [getD_map_range _ (q+1) n zeroBox (by omega)]
  exact weightJet_mem (pi_mem 192) _ _ 4 n 192
    (fun m hm0 hm => hg m 9 hm0 hm (by norm_num))
    (fun m hm0 hm => hg m 5 hm0 hm (by norm_num))

theorem nodeJet_mem {u : ℝ} {U : Box} {J : Box × Box} (hu : u ∈ U)
    (hwhole : u ∈ Icc (0 : ℝ) (8/5))
    (hc : Real.cos ((632083/10000 : ℝ)*u) ∈ J.1)
    (hs : Real.sin ((632083/10000 : ℝ)*u) ∈ J.2)
    (q k n : ℕ) (hk : k ≤ 2) (hn : n ≤ q) :
    coefficient (realIntegrand 4 k (632083/10000)) n u ∈ nodeJet U J q k n := by
  have hx : (632083/10000 : ℝ) ∈ X := by
    simpa [X] using rational_mem (632083/10000) 192
  exact integrandJet_mem hx hu hc hs 4 k 192 n hk _
    (fun i hi => weightTable_mem hu hwhole q i (by omega))

end OperatorDerivativeRewrite.Foundation.RiemannQuarticNodeJets
