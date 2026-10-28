import Foundation.FiniteWilsonTorusKernel

/-! Microscopic periodic2-by-2 Z2 Wilson noise certificate. All eight links use
same/flip weights3/1. The five labels are three plaquettes and two windings. -/
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusNoise
open FiniteWilsonTorusKernel

def parity4 (u : Fin 256) (a b c d : ℕ) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (u.val.testBit a) (u.val.testBit b)) (u.val.testBit c)) (u.val.testBit d)
def noiseLabel (u : Fin 256) : ℕ :=
  (if parity4 u 0 1 2 5 then 1 else 0)+(if parity4 u 0 2 3 7 then 2 else 0)+
  (if parity4 u 1 4 5 6 then 4 else 0)+
  (if Bool.xor (u.val.testBit 0) (u.val.testBit 4) then 8 else 0)+
  (if Bool.xor (u.val.testBit 1) (u.val.testBit 3) then 16 else 0)
def weight (u : Fin 256) : ℕ :=
  (if u.val.testBit 0 then 1 else 3)*(if u.val.testBit 1 then 1 else 3)*
  (if u.val.testBit 2 then 1 else 3)*(if u.val.testBit 3 then 1 else 3)*
  (if u.val.testBit 4 then 1 else 3)*(if u.val.testBit 5 then 1 else 3)*
  (if u.val.testBit 6 then 1 else 3)*(if u.val.testBit 7 then 1 else 3)
def index (b r : Fin 16) : Fin 256 := ⟨16*b.val+r.val, by omega⟩
def fiberCount (j : State) : ℕ := ∑ b : Fin 16, ∑ r : Fin 16,
  if noiseLabel (index b r)=j.val then weight (index b r) else 0
private theorem count_0 : fiberCount 0=count 0 := by decide
private theorem count_1 : fiberCount 1=count 1 := by decide
private theorem count_2 : fiberCount 2=count 2 := by decide
private theorem count_3 : fiberCount 3=count 3 := by decide
private theorem count_4 : fiberCount 4=count 4 := by decide
private theorem count_5 : fiberCount 5=count 5 := by decide
private theorem count_6 : fiberCount 6=count 6 := by decide
private theorem count_7 : fiberCount 7=count 7 := by decide
private theorem count_8 : fiberCount 8=count 8 := by decide
private theorem count_9 : fiberCount 9=count 9 := by decide
private theorem count_10 : fiberCount 10=count 10 := by decide
private theorem count_11 : fiberCount 11=count 11 := by decide
private theorem count_12 : fiberCount 12=count 12 := by decide
private theorem count_13 : fiberCount 13=count 13 := by decide
private theorem count_14 : fiberCount 14=count 14 := by decide
private theorem count_15 : fiberCount 15=count 15 := by decide
private theorem count_16 : fiberCount 16=count 16 := by decide
private theorem count_17 : fiberCount 17=count 17 := by decide
private theorem count_18 : fiberCount 18=count 18 := by decide
private theorem count_19 : fiberCount 19=count 19 := by decide
private theorem count_20 : fiberCount 20=count 20 := by decide
private theorem count_21 : fiberCount 21=count 21 := by decide
private theorem count_22 : fiberCount 22=count 22 := by decide
private theorem count_23 : fiberCount 23=count 23 := by decide
private theorem count_24 : fiberCount 24=count 24 := by decide
private theorem count_25 : fiberCount 25=count 25 := by decide
private theorem count_26 : fiberCount 26=count 26 := by decide
private theorem count_27 : fiberCount 27=count 27 := by decide
private theorem count_28 : fiberCount 28=count 28 := by decide
private theorem count_29 : fiberCount 29=count 29 := by decide
private theorem count_30 : fiberCount 30=count 30 := by decide
private theorem count_31 : fiberCount 31=count 31 := by decide

theorem microscopic_count_certificate (j : State) : fiberCount j=count j := by
  fin_cases j
  · exact count_0
  · exact count_1
  · exact count_2
  · exact count_3
  · exact count_4
  · exact count_5
  · exact count_6
  · exact count_7
  · exact count_8
  · exact count_9
  · exact count_10
  · exact count_11
  · exact count_12
  · exact count_13
  · exact count_14
  · exact count_15
  · exact count_16
  · exact count_17
  · exact count_18
  · exact count_19
  · exact count_20
  · exact count_21
  · exact count_22
  · exact count_23
  · exact count_24
  · exact count_25
  · exact count_26
  · exact count_27
  · exact count_28
  · exact count_29
  · exact count_30
  · exact count_31

theorem microscopic_total : (∑ b : Fin 16, ∑ r : Fin 16,weight (index b r))=65536 := by decide

theorem index_bijective : Function.Bijective (fun p : Fin 16 × Fin 16 => index p.1 p.2) := by
  constructor
  · intro p q he
    have hv := congrArg Fin.val he
    change 16*p.1.val+p.2.val=16*q.1.val+q.2.val at hv
    have hb : p.1=q.1 := Fin.ext (by omega)
    have hr : p.2=q.2 := Fin.ext (by omega)
    exact Prod.ext hb hr
  · intro y
    refine ⟨(⟨y.val/16,by omega⟩,⟨y.val%16,by omega⟩),?_⟩
    apply Fin.ext
    change 16*(y.val/16)+y.val%16=y.val
    omega

def labelState (u : Fin 256) : State := ⟨noiseLabel u%32,Nat.mod_lt _ (by decide)⟩
def plaquetteScore (u : Fin 256) : ℤ :=
  (if parity4 u 0 1 2 5 then -1 else 1)+(if parity4 u 0 2 3 7 then -1 else 1)+
  (if parity4 u 1 4 5 6 then -1 else 1)+(if parity4 u 3 4 6 7 then -1 else 1)

private theorem score_by_index (b r : Fin 16) :
    plaquetteScore (index b r)=(![4,0,0,-4] : Fin 4 → ℤ) (orbit (labelState (index b r))) := by
  fin_cases b <;> fin_cases r <;> decide

theorem score_certificate (u : Fin 256) :
    plaquetteScore u=(![4,0,0,-4] : Fin 4 → ℤ) (orbit (labelState u)) := by
  obtain ⟨⟨b,r⟩,rfl⟩ := index_bijective.surjective u
  exact score_by_index b r

noncomputable def beta : ℝ := Real.log 3/2

theorem temporal_odds : Real.exp (2*beta)=3 := by
  rw [show 2*beta=Real.log 3 by unfold beta; ring,Real.exp_log (by norm_num : (0:ℝ)<3)]

/-- Literal homogeneous spatial half weight, with the SAME beta as all eight
independent temporal Wilson link increments. No orbit-dependent coupling. -/
theorem amplitude_wilson_form (u : Fin 256) :
    amplitude (labelState u)=Real.exp ((beta/2)*(plaquetteScore u:ℝ)) := by
  unfold amplitude
  rw [score_certificate]
  generalize orbit (labelState u)=i
  fin_cases i <;> norm_num [beta]
  · rw [show Real.log 3/2/2*4=Real.log 3 by ring,Real.exp_log (by norm_num : (0:ℝ)<3)]
  · rw [show -(Real.log 3/2/2*4)= -(Real.log 3) by ring,Real.exp_neg,
      Real.exp_log (by norm_num : (0:ℝ)<3)]
    norm_num

/-- Three independent vertex flips; the fourth equals their product because
the common global Z2 gauge element acts trivially. -/
def gaugeMask (g : Fin 8) : ℕ := Nat.xor (if g.val.testBit 0 then 27 else 0)
  (Nat.xor (if g.val.testBit 1 then 78 else 0) (if g.val.testBit 2 then 177 else 0))
def gaugeAction (g : Fin 8) (u : Fin 256) : Fin 256 :=
  ⟨Nat.xor u.val (gaugeMask g)%256,Nat.mod_lt _ (by decide)⟩
def canonical : State → Fin 256 := ![0,46,42,4,14,32,36,10,5,43,47,1,11,37,33,15,34,12,8,38,44,2,6,40,39,9,13,35,41,7,3,45]

theorem canonical_label (i : State) : labelState (canonical i)=i := by fin_cases i <;> decide

private theorem label_gauge_by_index (g : Fin 8) (b : Fin 16) : ∀ r : Fin 16,
    labelState (gaugeAction g (index b r))=labelState (index b r) := by
  fin_cases g <;> fin_cases b <;> decide

theorem label_gauge (g : Fin 8) (u : Fin 256) : labelState (gaugeAction g u)=labelState u := by
  obtain ⟨⟨b,r⟩,rfl⟩ := index_bijective.surjective u
  exact label_gauge_by_index g b r

private theorem canonical_by_index (b r : Fin 16) :
    ∃ g : Fin 8, gaugeAction g (index b r)=canonical (labelState (index b r)) := by
  fin_cases b <;> fin_cases r <;> decide

theorem canonical_gauge (u : Fin 256) : ∃ g : Fin 8, gaugeAction g u=canonical (labelState u) := by
  obtain ⟨⟨b,r⟩,rfl⟩ := index_bijective.surjective u
  exact canonical_by_index b r

/-- Every invariant microscopic observable factors through the actual labels;
this is not an assertion that arbitrary open-link probes are physical. -/
theorem invariant_factorization (f : Fin 256 → ℝ)
    (hf : ∀ g u, f (gaugeAction g u)=f u) (u : Fin 256) :
    f u=f (canonical (labelState u)) := by
  obtain ⟨g,hg⟩ := canonical_gauge u
  rw [← hg,hf]

def relative (u v : Fin 256) : Fin 256 := ⟨Nat.xor u.val v.val%256,Nat.mod_lt _ (by decide)⟩
/-- Sum over the eight effective vertex gauges of the target representative. -/
def projectedCount (i j : State) : ℕ :=
  ∑ g : Fin 8,weight (relative (canonical i) (gaugeAction g (canonical j)))
private theorem projected_row_0 : ∀ j : State, projectedCount 0 j=count (difference 0 j) := by decide
private theorem projected_row_1 : ∀ j : State, projectedCount 1 j=count (difference 1 j) := by decide
private theorem projected_row_2 : ∀ j : State, projectedCount 2 j=count (difference 2 j) := by decide
private theorem projected_row_3 : ∀ j : State, projectedCount 3 j=count (difference 3 j) := by decide
private theorem projected_row_4 : ∀ j : State, projectedCount 4 j=count (difference 4 j) := by decide
private theorem projected_row_5 : ∀ j : State, projectedCount 5 j=count (difference 5 j) := by decide
private theorem projected_row_6 : ∀ j : State, projectedCount 6 j=count (difference 6 j) := by decide
private theorem projected_row_7 : ∀ j : State, projectedCount 7 j=count (difference 7 j) := by decide
private theorem projected_row_8 : ∀ j : State, projectedCount 8 j=count (difference 8 j) := by decide
private theorem projected_row_9 : ∀ j : State, projectedCount 9 j=count (difference 9 j) := by decide
private theorem projected_row_10 : ∀ j : State, projectedCount 10 j=count (difference 10 j) := by decide
private theorem projected_row_11 : ∀ j : State, projectedCount 11 j=count (difference 11 j) := by decide
private theorem projected_row_12 : ∀ j : State, projectedCount 12 j=count (difference 12 j) := by decide
private theorem projected_row_13 : ∀ j : State, projectedCount 13 j=count (difference 13 j) := by decide
private theorem projected_row_14 : ∀ j : State, projectedCount 14 j=count (difference 14 j) := by decide
private theorem projected_row_15 : ∀ j : State, projectedCount 15 j=count (difference 15 j) := by decide
private theorem projected_row_16 : ∀ j : State, projectedCount 16 j=count (difference 16 j) := by decide
private theorem projected_row_17 : ∀ j : State, projectedCount 17 j=count (difference 17 j) := by decide
private theorem projected_row_18 : ∀ j : State, projectedCount 18 j=count (difference 18 j) := by decide
private theorem projected_row_19 : ∀ j : State, projectedCount 19 j=count (difference 19 j) := by decide
private theorem projected_row_20 : ∀ j : State, projectedCount 20 j=count (difference 20 j) := by decide
private theorem projected_row_21 : ∀ j : State, projectedCount 21 j=count (difference 21 j) := by decide
private theorem projected_row_22 : ∀ j : State, projectedCount 22 j=count (difference 22 j) := by decide
private theorem projected_row_23 : ∀ j : State, projectedCount 23 j=count (difference 23 j) := by decide
private theorem projected_row_24 : ∀ j : State, projectedCount 24 j=count (difference 24 j) := by decide
private theorem projected_row_25 : ∀ j : State, projectedCount 25 j=count (difference 25 j) := by decide
private theorem projected_row_26 : ∀ j : State, projectedCount 26 j=count (difference 26 j) := by decide
private theorem projected_row_27 : ∀ j : State, projectedCount 27 j=count (difference 27 j) := by decide
private theorem projected_row_28 : ∀ j : State, projectedCount 28 j=count (difference 28 j) := by decide
private theorem projected_row_29 : ∀ j : State, projectedCount 29 j=count (difference 29 j) := by decide
private theorem projected_row_30 : ∀ j : State, projectedCount 30 j=count (difference 30 j) := by decide
private theorem projected_row_31 : ∀ j : State, projectedCount 31 j=count (difference 31 j) := by decide

theorem gauge_projected_count (i j : State) : projectedCount i j=count (difference i j) := by
  fin_cases i
  · exact projected_row_0 j
  · exact projected_row_1 j
  · exact projected_row_2 j
  · exact projected_row_3 j
  · exact projected_row_4 j
  · exact projected_row_5 j
  · exact projected_row_6 j
  · exact projected_row_7 j
  · exact projected_row_8 j
  · exact projected_row_9 j
  · exact projected_row_10 j
  · exact projected_row_11 j
  · exact projected_row_12 j
  · exact projected_row_13 j
  · exact projected_row_14 j
  · exact projected_row_15 j
  · exact projected_row_16 j
  · exact projected_row_17 j
  · exact projected_row_18 j
  · exact projected_row_19 j
  · exact projected_row_20 j
  · exact projected_row_21 j
  · exact projected_row_22 j
  · exact projected_row_23 j
  · exact projected_row_24 j
  · exact projected_row_25 j
  · exact projected_row_26 j
  · exact projected_row_27 j
  · exact projected_row_28 j
  · exact projected_row_29 j
  · exact projected_row_30 j
  · exact projected_row_31 j

theorem gauge_projected_kernel (i j : State) : (projectedCount i j:ℝ)/65536=kinetic i j := by
  rw [gauge_projected_count]
  rfl

end OperatorDerivativeRewrite.Foundation.FiniteWilsonTorusNoise
