import Foundation.PeriodicTemporalCycleMoment
/-! Exact center-character selection for actual temporal Haar moments.
The measure here is the reference vertex Haar law, not a nonzero Gibbs law. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalParity
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab SU2WilsonConvolution
attribute [local irreducible] gaugeHaar

def bit (b : Bool) : ℕ := if b then 1 else 0

def character (x : ZMod 2) : ℝ := if x=0 then 1 else -1

private theorem binary (x : ZMod 2) : x=0 ∨ x=1 := by
  have hh : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide
  exact hh x

theorem character_add (x y : ZMod 2) : character (x+y)=character x*character y := by
  have h11 : (1 : ZMod 2)+1=0 := by decide
  rcases binary x with rfl|rfl <;> rcases binary y with rfl|rfl
  all_goals simp only [zero_add,add_zero,h11]
  all_goals norm_num [character]

theorem character_zero : character 0=1 := by norm_num [character]

def center (b : SpatialVertex → Bool) (v : SpatialVertex) : SU2 :=
  if b v then SU2StapleExtremes.minusOne else 1

def transform (b : SpatialVertex → Bool) (a : Gauge) : Gauge := center b*a

theorem transform_preserving (b : SpatialVertex → Bool) :
    MeasurePreserving (transform b) gaugeHaar gaugeHaar := by
  unfold transform gaugeHaar
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun v => measurePreserving_mul_left law (center b v))

private theorem center_inv : (SU2StapleExtremes.minusOne)⁻¹=SU2StapleExtremes.minusOne := by
  exact inv_eq_of_mul_eq_one_left PeriodicCenterSeam.center_square

private theorem target_trace (U V t s : SU2) :
    halfTrace (U*(SU2StapleExtremes.minusOne*t)*V⁻¹*s⁻¹) =
      -halfTrace (U*t*V⁻¹*s⁻¹) := by
  have hg : U*(SU2StapleExtremes.minusOne*t)*V⁻¹*s⁻¹ =
      SU2StapleExtremes.minusOne*(U*t*V⁻¹*s⁻¹) := by
    rw [← mul_assoc U SU2StapleExtremes.minusOne t,
      ← PeriodicCenterSeam.center_commute U]
    group
  rw [hg,SU2StrongCouplingCovariance.halfTrace_center_neg]

private theorem source_trace (U V t s : SU2) :
    halfTrace (U*t*V⁻¹*(SU2StapleExtremes.minusOne*s)⁻¹) =
      -halfTrace (U*t*V⁻¹*s⁻¹) := by
  rw [mul_inv_rev,center_inv,← mul_assoc,
    halfTrace_mul_comm (U*t*V⁻¹*s⁻¹) SU2StapleExtremes.minusOne,
    SU2StrongCouplingCovariance.halfTrace_center_neg]

def edgeParity (b : SpatialVertex → Bool) (e : SpatialEdge) : ZMod 2 :=
  (bit (b e.1) : ZMod 2)+(bit (b (shift e.1 e.2)) : ZMod 2)

private theorem two_center_trace (U V t s : SU2) (b c : Bool) :
    halfTrace (U*((if c then SU2StapleExtremes.minusOne else 1)*t)*V⁻¹*
      ((if b then SU2StapleExtremes.minusOne else 1)*s)⁻¹) =
    character ((bit b : ZMod 2)+(bit c : ZMod 2))*halfTrace (U*t*V⁻¹*s⁻¹) := by
  have h11 : (1 : ZMod 2)+1=0 := by decide
  cases b <;> cases c
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,bit,
    Nat.cast_one,Nat.cast_zero,zero_add,add_zero,h11,character]
  · simpa using target_trace U V t s
  · simpa using source_trace U V t s
  · rw [source_trace,target_trace,neg_neg]

theorem trace_transform (b : SpatialVertex → Bool) (U V : State) (e : SpatialEdge)
    (a : Gauge) :
    halfTrace (temporalWord U V (transform b a) e) =
      character (edgeParity b e)*halfTrace (temporalWord U V a e) := by
  exact two_center_trace (U e) (V e) (a (shift e.1 e.2)) (a e.1)
    (b e.1) (b (shift e.1 e.2))

def parity {n : ℕ} (b : SpatialVertex → Bool) (E : Fin n → SpatialEdge) : ZMod 2 :=
  ∑ j, edgeParity b (E j)

def product {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) (a : Gauge) : ℝ :=
  ∏ j, halfTrace (temporalWord U V a (E j))

theorem product_measurable {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) :
    Measurable (product U V E) := by
  unfold product
  apply Finset.measurable_prod
  intro j _
  exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)

private theorem character_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ZMod 2) : character (∑ j ∈ s, p j)=∏ j ∈ s, character (p j) := by
  induction s using Finset.induction_on with
  | empty => simp [character_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Finset.prod_insert ha,
      character_add,ih]

theorem product_transform {n : ℕ} (b : SpatialVertex → Bool) (U V : State)
    (E : Fin n → SpatialEdge) (a : Gauge) :
    product U V E (transform b a) = character (parity b E)*product U V E a := by
  unfold product parity
  simp_rw [trace_transform]
  rw [Finset.prod_mul_distrib,character_sum]

def moment {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) : ℝ :=
  ∫ a, product U V E a ∂gaugeHaar

theorem moment_selection {n : ℕ} (b : SpatialVertex → Bool) (U V : State)
    (E : Fin n → SpatialEdge) : moment U V E = character (parity b E)*moment U V E := by
  have hp := transform_preserving b
  have hi := integral_map (μ := gaugeHaar) hp.measurable.aemeasurable
    (product_measurable U V E).aestronglyMeasurable
  rw [hp.map_eq] at hi
  simp_rw [product_transform] at hi
  rw [integral_const_mul] at hi
  exact hi

theorem odd_moment_zero {n : ℕ} (b : SpatialVertex → Bool) (U V : State)
    (E : Fin n → SpatialEdge) (ho : parity b E = 1) : moment U V E=0 := by
  have hh := moment_selection b U V E
  rw [ho] at hh
  norm_num [character] at hh
  linarith

theorem nonzero_moment_parity {n : ℕ} (b : SpatialVertex → Bool) (U V : State)
    (E : Fin n → SpatialEdge) (hm : moment U V E ≠ 0) : parity b E=0 := by
  rcases binary (parity b E) with hh|hh
  · exact hh
  · exact (hm (odd_moment_zero b U V E hh)).elim

def layerCount {n : ℕ} (E : Fin n → SpatialEdge) (l : Fin 4) : ℕ :=
  (Finset.univ.filter (fun j => (E j).2=1 ∧ (E j).1 1=(l.val : ZMod 4))).card

def cut (l : Fin 3) (v : SpatialVertex) : Bool := decide ((v 1).val ≤ l.val)

private theorem cut_certificate : ∀ (x : ZMod 4) (d : Fin 3) (l : Fin 3),
    (bit (decide (x.val ≤ l.val)) : ZMod 2)+
      (bit (decide ((x+if (1 : Fin 3)=d then 1 else 0).val ≤ l.val)) : ZMod 2) =
      (if d=1 ∧ x=(l.val : ZMod 4) then 1 else 0)+
        (if d=1 ∧ x=3 then 1 else 0) := by decide

theorem cut_edge (l : Fin 3) (e : SpatialEdge) : edgeParity (cut l) e =
    (if e.2=1 ∧ e.1 1=(l.val : ZMod 4) then 1 else 0)+
      (if e.2=1 ∧ e.1 1=3 then 1 else 0) := by
  exact cut_certificate (e.1 1) e.2 l

theorem cut_parity {n : ℕ} (E : Fin n → SpatialEdge) (l : Fin 3) :
    parity (cut l) E = (layerCount E l.castSucc : ZMod 2)+(layerCount E 3 : ZMod 2) := by
  unfold parity
  simp_rw [cut_edge]
  rw [Finset.sum_add_distrib]
  simp only [layerCount,Finset.natCast_card_filter,Fin.val_castSucc]
  rfl

private theorem layer_sum_certificate : ∀ (x : ZMod 4) (d : Fin 3),
    (∑ l : Fin 4, if d=1 ∧ x=(l.val : ZMod 4) then (1 : ℕ) else 0) ≤ 1 := by decide

theorem layer_sum_le {n : ℕ} (E : Fin n → SpatialEdge) :
    (∑ l : Fin 4, layerCount E l) ≤ n := by
  unfold layerCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin n, (1 : ℕ) := Finset.sum_le_sum (fun j _ =>
      layer_sum_certificate ((E j).1 1) (E j).2)
    _ = n := by simp

theorem nonzero_odd_seam_layers {n : ℕ} (U V : State) (E : Fin n → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) :
    ∀ l : Fin 4, 1 ≤ layerCount E l := by
  have hp (l : Fin 3) := nonzero_moment_parity (cut l) U V E hm
  simp_rw [cut_parity,hs] at hp
  intro l
  by_contra hn
  have hz : layerCount E l=0 := by omega
  by_cases hl : l=3
  · subst l
    rw [hz] at hs
    norm_num at hs
  · have hb : l.val<3 := by
      have hv := l.isLt
      have he : l.val ≠ 3 := by intro hh; apply hl; exact Fin.ext hh
      omega
    have hh := hp ⟨l.val,hb⟩
    have he : (⟨l.val,hb⟩ : Fin 3).castSucc=l := Fin.ext rfl
    rw [he,hz] at hh
    norm_num at hh

theorem nonzero_odd_seam_min_order {n : ℕ} (U V : State) (E : Fin n → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) : 4 ≤ n := by
  have hlo := nonzero_odd_seam_layers U V E hm hs
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun l _ => hlo l)
  have hu := layer_sum_le E
  have hc : (∑ _l : Fin 4, (1 : ℕ))=4 := by simp
  rw [hc] at hh
  omega

theorem trace_twist (U V : State) (e : SpatialEdge) (a : Gauge) :
    halfTrace (temporalWord U (PeriodicCenterSeam.flip 1 V) a e) =
      character (if e.2=1 ∧ e.1 1=3 then 1 else 0)*halfTrace (temporalWord U V a e) := by
  have hw := PeriodicCenterSeam.temporal_word 1 (PeriodicCenterSeam.flip 1 U) V a e
  rw [PeriodicCenterSeam.flip_involutive] at hw
  rw [hw]
  by_cases he : e.2=1 ∧ e.1 1=3
  · have hh : temporalWord (PeriodicCenterSeam.flip 1 U) V a e =
        SU2StapleExtremes.minusOne*temporalWord U V a e := by
      simp only [temporalWord,PeriodicCenterSeam.flip,Pi.mul_apply]
      rw [show PeriodicCenterSeam.seam 1 e=SU2StapleExtremes.minusOne by
        simp [PeriodicCenterSeam.seam,he]]
      group
    rw [hh,SU2StrongCouplingCovariance.halfTrace_center_neg]
    norm_num [he,character]
  · simp only [temporalWord,PeriodicCenterSeam.flip,Pi.mul_apply,
      PeriodicCenterSeam.seam,he,ite_false,one_mul,character_zero]

theorem product_twist {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) (a : Gauge) :
    product U (PeriodicCenterSeam.flip 1 V) E a =
      character (layerCount E 3)*product U V E a := by
  unfold product
  simp_rw [trace_twist]
  rw [Finset.prod_mul_distrib,← character_sum]
  congr 1
  simp only [layerCount,Finset.natCast_card_filter]
  rfl

theorem moment_twist {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) :
    moment U (PeriodicCenterSeam.flip 1 V) E = character (layerCount E 3)*moment U V E := by
  unfold moment
  simp_rw [product_twist]
  rw [integral_const_mul]

theorem moment_twist_low_order {n : ℕ} (hn : n < 4) (U V : State)
    (E : Fin n → SpatialEdge) : moment U (PeriodicCenterSeam.flip 1 V) E=moment U V E := by
  rw [moment_twist]
  rcases binary (layerCount E 3) with hh|hh
  · rw [hh,character_zero,one_mul]
  · have hm : moment U V E=0 := by
      by_contra hm
      have hb := nonzero_odd_seam_min_order U V E hm hh
      omega
    rw [hm,mul_zero]

theorem product_bound {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) (a : Gauge) :
    |product U V E a| ≤ 1 := by
  unfold product
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => halfTrace_bound _)

theorem product_integrable {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) :
    Integrable (product U V E) gaugeHaar := by
  apply Integrable.of_bound (product_measurable U V E).aestronglyMeasurable 1
  filter_upwards with a
  simpa only [Real.norm_eq_abs] using product_bound U V E a

def traceSum (U V : State) (a : Gauge) : ℝ := ∑ e, halfTrace (temporalWord U V a e)
def powerMoment (n : ℕ) (U V : State) : ℝ := ∫ a, (traceSum U V a)^n ∂gaugeHaar

theorem power_moment_expansion (n : ℕ) (U V : State) :
    powerMoment n U V = ∑ E : Fin n → SpatialEdge, moment U V E := by
  unfold powerMoment traceSum moment product
  simp_rw [Fintype.sum_pow]
  rw [integral_finsetSum]
  intro E _
  exact product_integrable U V E

theorem power_moment_twist_low_order {n : ℕ} (hn : n < 4) (U V : State) :
    powerMoment n U (PeriodicCenterSeam.flip 1 V)=powerMoment n U V := by
  rw [power_moment_expansion,power_moment_expansion]
  apply Finset.sum_congr rfl
  intro E _
  exact moment_twist_low_order hn U V E

theorem quartic_layer_count (U V : State) (E : Fin 4 → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) :
    ∀ l : Fin 4, layerCount E l=1 := by
  have hh := nonzero_odd_seam_layers U V E hm hs
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have hu := layer_sum_le E
  rw [Fin.sum_univ_four] at hu
  intro l
  fin_cases l
  · change layerCount E 0=1; omega
  · change layerCount E 1=1; omega
  · change layerCount E 2=1; omega
  · change layerCount E 3=1; omega

private theorem parallel_certificate : ∀ (x : ZMod 4) (d : Fin 3),
    (∑ l : Fin 4, if d=1 ∧ x=(l.val : ZMod 4) then (1 : ℕ) else 0) =
      if d=1 then 1 else 0 := by decide

theorem layer_sum_parallel {n : ℕ} (E : Fin n → SpatialEdge) :
    (∑ l : Fin 4, layerCount E l) = ∑ j : Fin n, if (E j).2=1 then 1 else 0 := by
  unfold layerCount
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact parallel_certificate ((E j).1 1) (E j).2

theorem quartic_parallel (U V : State) (E : Fin 4 → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) :
    ∀ j, (E j).2=1 := by
  have hl := quartic_layer_count U V E hm hs
  have he : (∑ j : Fin 4, if (E j).2=1 then (1 : ℕ) else 0)=4 := by
    rw [← layer_sum_parallel]
    simp_rw [hl]
    simp
  intro j
  by_contra hn
  have hb : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      (if (E k).2=1 then (1 : ℕ) else 0) ≤ 1 := by intro k _; split_ifs <;> omega
  have hh := Finset.sum_lt_sum hb ⟨j,Finset.mem_univ j,by simp [hn]⟩
  rw [he] at hh
  norm_num at hh

open PeriodicTemporalCycleMoment (Row vertex edge)

private theorem vertex_layer_injective :
    Function.Injective (fun j : Fin 4 => (j.val : ZMod 4)) := by decide

private theorem vertex_eq_iff (r s : Row) (i j : Fin 4) :
    vertex r i=vertex s j ↔ r=s ∧ i=j := by
  constructor
  · intro hh
    constructor
    · funext k
      fin_cases k
      · exact congrArg (fun v : SpatialVertex => v 0) hh
      · exact congrArg (fun v : SpatialVertex => v 2) hh
    · exact vertex_layer_injective (congrArg (fun v : SpatialVertex => v 1) hh)
  · rintro ⟨rfl,rfl⟩
    rfl

private theorem vertex_shift : ∀ (r : Row) (j : Fin 4),
    shift (vertex r j) 1=vertex r (j+1) := by decide

def vertexMask (v w : SpatialVertex) : Bool := decide (w=v)

theorem ordered_row_parity (b : Fin 4 → Row) (j : Fin 4) :
    parity (vertexMask (vertex (b j) (j+1))) (fun k => edge (b k) k) =
      1+(if b (j+1)=b j then 1 else 0) := by
  fin_cases j
  all_goals simp [parity,Fin.sum_univ_four,edgeParity,edge,vertex_shift,
    vertexMask,vertex_eq_iff,bit]
  all_goals ring

theorem ordered_row_nonzero (U V : State) (b : Fin 4 → Row)
    (hm : moment U V (fun j => edge (b j) j) ≠ 0) : ∀ j, b j=b 0 := by
  have hh (j : Fin 4) : b (j+1)=b j := by
    have hp := nonzero_moment_parity (vertexMask (vertex (b j) (j+1))) U V _ hm
    rw [ordered_row_parity] at hp
    by_contra hn
    norm_num [hn] at hp
  have h0 : b 1=b 0 := by simpa using hh 0
  have h1 : b 2=b 1 := by simpa using hh 1
  have h2 : b 3=b 2 := by simpa using hh 2
  intro j
  fin_cases j
  · rfl
  · exact h0
  · exact h1.trans h0
  · exact h2.trans (h1.trans h0)

def layerIndex (e : SpatialEdge) : Fin 4 := ⟨(e.1 1).val,ZMod.val_lt _⟩
def rowOf (e : SpatialEdge) : Row := ![e.1 0,e.1 2]

theorem edge_reconstruction (e : SpatialEdge) (hd : e.2 = 1) :
    e=edge (rowOf e) (layerIndex e) := by
  apply Prod.ext
  · funext k
    fin_cases k
    · rfl
    · exact (ZMod.natCast_zmod_val (e.1 1)).symm
    · rfl
  · exact hd

theorem quartic_layer_injective (U V : State) (E : Fin 4 → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) :
    Function.Injective (fun j => layerIndex (E j)) := by
  have hc := quartic_layer_count U V E hm hs
  have hd := quartic_parallel U V E hm hs
  intro i j hij
  let l := layerIndex (E i)
  have hh : (Finset.univ.filter
      (fun k : Fin 4 => (E k).2=1 ∧ (E k).1 1=(l.val : ZMod 4))).card ≤ 1 := by
    exact le_of_eq (hc l)
  apply Finset.card_le_one.mp hh i ?_ j ?_
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,hd i, true_and]
    exact (ZMod.natCast_zmod_val ((E i).1 1)).symm
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,hd j,true_and]
    have he : (E j).1 1=(E i).1 1 := by
      have ht := congrArg (fun q : Fin 4 => (q.val : ZMod 4)) hij
      simpa only [layerIndex,ZMod.natCast_zmod_val] using ht.symm
    rw [he]
    exact (ZMod.natCast_zmod_val ((E i).1 1)).symm

theorem moment_reindex {n : ℕ} (U V : State) (E : Fin n → SpatialEdge)
    (q : Equiv.Perm (Fin n)) : moment U V (fun j => E (q j))=moment U V E := by
  unfold moment product
  apply integral_congr_ae
  filter_upwards with a
  exact Equiv.prod_comp q (fun j => halfTrace (temporalWord U V a (E j)))

/-- Every surviving seam-odd quartic tuple is a permutation of ONE genuine
periodic winding row. No external finite-enumeration certificate is assumed. -/
theorem quartic_winding_support (U V : State) (E : Fin 4 → SpatialEdge)
    (hm : moment U V E ≠ 0) (hs : (layerCount E 3 : ZMod 2) = 1) :
    ∃ (r : Row) (q : Equiv.Perm (Fin 4)), ∀ j, E j=edge r (q j) := by
  classical
  have hinj := quartic_layer_injective U V E hm hs
  let q : Equiv.Perm (Fin 4) := Equiv.ofBijective (fun j => layerIndex (E j))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj,rfl⟩)
  let b : Fin 4 → Row := fun j => rowOf (E (q.symm j))
  have he (j : Fin 4) : E (q.symm j)=edge (b j) j := by
    rw [edge_reconstruction _ (quartic_parallel U V E hm hs _)]
    have hi : layerIndex (E (q.symm j))=j := q.apply_symm_apply j
    rw [hi]
  have hm' : moment U V (fun j => edge (b j) j) ≠ 0 := by
    have ht := moment_reindex U V E q.symm
    simp_rw [he] at ht
    rw [ht]
    exact hm
  have hb := ordered_row_nonzero U V b hm'
  refine ⟨b 0,q,fun j => ?_⟩
  have hh := he (q j)
  rw [q.symm_apply_apply] at hh
  rw [hb] at hh
  exact hh

abbrev WindingParameter := Row × Equiv.Perm (Fin 4)

def encode (p : WindingParameter) : Fin 4 → SpatialEdge := fun j => edge p.1 (p.2 j)

theorem encode_injective : Function.Injective encode := by
  intro p q hh
  have he (j : Fin 4) : vertex p.1 (p.2 j)=vertex q.1 (q.2 j) :=
    congrArg Prod.fst (congrFun hh j)
  have hp : p.2=q.2 := by
    apply Equiv.ext
    intro j
    exact ((vertex_eq_iff _ _ _ _).mp (he j)).2
  exact Prod.ext ((vertex_eq_iff _ _ _ _).mp (he 0)).1 hp

def contrast {n : ℕ} (U V : State) (E : Fin n → SpatialEdge) : ℝ :=
  moment U V E-moment U (PeriodicCenterSeam.flip 1 V) E

theorem contrast_support (U V : State) (E : Fin 4 → SpatialEdge)
    (hc : contrast U V E ≠ 0) : ∃ p : WindingParameter, encode p=E := by
  have hm : moment U V E ≠ 0 := by
    intro hz
    apply hc
    rw [contrast,moment_twist,hz,mul_zero,sub_self]
  have hs : (layerCount E 3 : ZMod 2)=1 := by
    rcases binary (layerCount E 3) with hh|hh
    · apply (hc ?_).elim
      rw [contrast,moment_twist,hh,character_zero,one_mul,sub_self]
    · exact hh
  obtain ⟨r,q,hq⟩ := quartic_winding_support U V E hm hs
  exact ⟨(r,q),funext (fun j => (hq j).symm)⟩

private theorem sum_over_support {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (f : κ → ℝ)
    (hs : ∀ k, f k ≠ 0 → ∃ i, e i = k) : (∑ k, f k)=∑ i, f (e i) := by
  classical
  symm
  apply Finset.sum_bij_ne_zero (fun i _ _ => e i)
  · intro i _ _
    exact Finset.mem_univ _
  · intro i _ _ j _ _ hij
    exact he hij
  · intro k _ hk
    obtain ⟨i,hi⟩ := hs k hk
    refine ⟨i,Finset.mem_univ i,?_,hi⟩
    rwa [hi]
  · intro i _ _
    rfl

/-- Complete quartic seam contrast reduced to the actual winding rows; all
other tuples vanish, including every repeated-edge and plaquette contribution. -/
theorem full_quartic_reduction (U V : State) :
    powerMoment 4 U V-powerMoment 4 U (PeriodicCenterSeam.flip 1 V) =
      ∑ p : WindingParameter, contrast U V (encode p) := by
  classical
  rw [power_moment_expansion,power_moment_expansion,← Finset.sum_sub_distrib]
  change (∑ E : Fin 4 → SpatialEdge, contrast U V E) = _
  exact sum_over_support encode encode_injective (contrast U V) (contrast_support U V)

theorem moment_row (U V : State) (r : Row) :
    moment U V (fun j => edge r j) =
      ∫ a, PeriodicTemporalCycleMoment.temporalProduct U V r a ∂gaugeHaar := by
  unfold moment product PeriodicTemporalCycleMoment.temporalProduct
  simp only [Fin.prod_univ_four]

theorem contrast_encode (h : ℝ) (p : WindingParameter) :
    contrast (PeriodicTemporalCycleMoment.orbit h) 1 (encode p)=Real.cos (4*h)/32 := by
  unfold contrast encode
  rw [moment_reindex _ _ (fun j => edge p.1 j) p.2,
    moment_reindex _ _ (fun j => edge p.1 j) p.2,moment_row,moment_row]
  exact PeriodicTemporalCycleMoment.row_difference h p.1

/-- The FULL fourth temporal-Haar moment contrast for the original quarter-turn
boundary. This is not yet the beta-derivative/log-normalized physical score. -/
theorem full_quartic_orbit (h : ℝ) :
    powerMoment 4 (PeriodicTemporalCycleMoment.orbit h) 1 -
      powerMoment 4 (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1) =
        12*Real.cos (4*h) := by
  rw [full_quartic_reduction]
  simp_rw [contrast_encode]
  have hc : Fintype.card WindingParameter=384 := by
    norm_num [WindingParameter,Row,Fintype.card_perm,Nat.factorial]
  rw [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul]
  norm_num
  ring

def fourthContrast (h : ℝ) : ℝ :=
  powerMoment 4 (PeriodicTemporalCycleMoment.orbit h) 1 -
    powerMoment 4 (PeriodicTemporalCycleMoment.orbit h) (PeriodicCenterSeam.flip 1 1)

theorem full_quartic_second : HasDerivAt (deriv fourthContrast) (-192) 0 := by
  have he : fourthContrast=(fun h : ℝ => 12*Real.cos (4*h)) := funext full_quartic_orbit
  rw [he]
  have hd : deriv (fun h : ℝ => 12*Real.cos (4*h)) =
      (fun h : ℝ => -48*Real.sin (4*h)) := by
    funext h
    have hh := (((hasDerivAt_id h).const_mul 4).cos).const_mul 12
    simp only [id_eq] at hh
    convert hh.deriv using 1 <;> ring
  rw [hd]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul 4).sin).const_mul (-48) using 1 <;> norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalParity
