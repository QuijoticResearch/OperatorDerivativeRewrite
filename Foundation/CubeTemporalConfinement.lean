import Foundation.CubeRootGround

/-! Global actual temporal confinement from the common axial tree. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeTemporalConfinement
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge
open CubeTemporalRootHaar FourCubePinnedCoercivity
attribute [local irreducible] defect

private theorem rooted_bound (U : State) (a : ℝ) (ha : 0 ≤ a)
    (hU : ∀ e,chordLabel e=none → defect (U e) ≤ a) (v : SpatialVertex) :
    defect (rootedGauge U v) ≤ 9*a := by
  have hb (e : SpatialEdge) (he : chordLabel e=none) (p : Prop) [Decidable p] :
      defect (if p then U e else 1) ≤ a := by
    split_ifs
    · exact hU e he
    · simpa only [defect_one] using ha
  unfold rootedGauge
  apply (defect_triple _ _ _).trans
  calc
    _ ≤ 3*(a+a+a) := by
      gcongr <;> apply hb <;> rfl
    _ = 9*a := by ring

theorem temporal_tree_word (q r : Chords) (g : Gauge) (e : SpatialEdge) (he : chordLabel e=none) :
    temporalWord (axialState q) (axialState r) g e=(gaugeAction g (1:State) e)⁻¹ := by
  simp only [temporalWord,axialState,he,Option.elim_none,one_mul,inv_one,mul_one,gaugeAction,Pi.one_apply]
  group

private theorem tree_defect (q r : Chords) (g : Gauge) (e : SpatialEdge) (he : chordLabel e=none) :
    defect (gaugeAction g (1:State) e) ≤ temporalAction (axialState q) (axialState r) g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun i _ => defect_nonneg (temporalWord (axialState q) (axialState r) g i)) (Finset.mem_univ e)
  have h' : defect (temporalWord (axialState q) (axialState r) g e) ≤
      temporalAction (axialState q) (axialState r) g := by
    simpa only [defect,temporalAction] using h
  rw [temporal_tree_word q r g e he,defect_inv] at h'
  exact h'

/-- Every actual relative temporal link is globally confined, independently of
both boundary chord fields and of the free temporal root. -/
theorem relative_defect (q r : Chords) (g : Gauge) (v : RelativeIndex) :
    defect (relative g v) ≤ 9*temporalAction (axialState q) (axialState r) g := by
  have h := rooted_bound (gaugeAction g (1:State)) _
    (temporal_action_bounds (axialState q) (axialState r) g).1 (tree_defect q r g) v.val
  have hz : rootedGauge (1:State) v.val=1 := by simp [rootedGauge]
  have hr := rooted_covariant g (1:State) v.val
  rw [hz,mul_one] at hr
  have he : root=(![0,0,0] : SpatialVertex) := by ext i; fin_cases i <;> rfl
  rw [← he] at hr
  have hc : rootedGauge (gaugeAction g (1:State)) v.val=(relative g v)⁻¹ := by
    rw [hr]
    unfold relative
    group
  rw [hc,defect_inv] at h
  exact h

def relativeEnergy (h : Relative) : ℝ := ∑ v,defect (h v)

theorem relativeEnergy_nonnegative (h : Relative) : 0 ≤ relativeEnergy h :=
  Finset.sum_nonneg (fun _ _ => defect_nonneg _)

/-- A global nonlinear temporal bound, not only a small-coordinate Hessian. -/
theorem energy_bound (q r : Chords) (g : Gauge) :
    relativeEnergy (relative g) ≤ 63*temporalAction (axialState q) (axialState r) g := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => relative_defect q r g v)
  simp only [Finset.sum_const,Finset.card_univ,relative_count,nsmul_eq_mul] at h
  change (∑ v : RelativeIndex,defect (relative g v)) ≤ _
  convert h using 1 <;> ring

/-- Actual temporal action dominates the seven-relative-link defect energy. -/
theorem halfAction_lower (q r : Chords) (g : Gauge) :
    (spatialAction (axialState q)+spatialAction (axialState r))/2+
      relativeEnergy (relative g)/63 ≤ halfAction (axialState q) (axialState r) g := by
  have h := energy_bound q r g
  unfold halfAction
  linarith

/-- Global domination with the genuine two boundary half-weights retained. -/
theorem weight_bound (beta : ℝ) (hb : 0 ≤ beta) (q r : Chords) (g : Gauge) :
    weight beta (axialState q) (axialState r) g ≤
      Real.exp (-beta*spatialAction (axialState q)/2)*
      Real.exp (-beta*spatialAction (axialState r)/2)*
      Real.exp (-(beta/63)*relativeEnergy (relative g)) := by
  unfold weight
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (halfAction_lower q r g) hb
  nlinarith


/-- Pure-gauge cancellation in the ACTUAL temporal words. -/
theorem flat_temporal_zero (a : Gauge) : temporalAction (gaugeAction a (1:State)) (1:State) a=0 := by
  have hw (e : SpatialEdge) : temporalWord (gaugeAction a (1:State)) (1:State) a e=1 := by
    unfold temporalWord gaugeAction
    simp only [Pi.one_apply]
    group
  unfold temporalAction
  simp only [hw,SU2OpenLinkGaugeObstruction.halfTrace_one,sub_self,Finset.sum_const_zero]

def flipGauge : Gauge := by
  classical
  exact fun v => if v=root then 1 else SU2StapleExtremes.minusOne

theorem flip_energy : relativeEnergy (relative flipGauge)=14 := by
  have hr : flipGauge root=1 := by simp [flipGauge]
  have hv (v : RelativeIndex) : relative flipGauge v=SU2StapleExtremes.minusOne := by
    simp only [relative,hr,inv_one,mul_one]
    simp [flipGauge,v.property]
  have hd : defect SU2StapleExtremes.minusOne=2 := by
    unfold defect
    rw [SU2OpenLinkGaugeObstruction.halfTrace_minusOne]
    norm_num
  unfold relativeEnergy
  simp only [hv,hd,Finset.sum_const,Finset.card_univ,relative_count,nsmul_eq_mul]
  norm_num

/-- No constant controls RAW relative temporal links for arbitrary original
boundary representatives. The common axial tree is a mathematical hypothesis. -/
theorem no_raw_temporal_coercivity (C : ℝ) :
    ¬ ∀ U V g,relativeEnergy (relative g) ≤ C*temporalAction U V g := by
  intro h
  have hf := h (gaugeAction flipGauge (1:State)) (1:State) flipGauge
  rw [flip_energy,flat_temporal_zero,mul_zero] at hf
  norm_num at hf


/-- Zero actual temporal action on the common axial section forces a CONSTANT
temporal field. The surviving global root is not fixed to the identity. -/
theorem zero_temporal_constant (q r : Chords) (g : Gauge)
    (hg : temporalAction (axialState q) (axialState r) g=0) :
    ∃ c : SU2,g=(fun _ => c) := by
  have hr : relative g=(1:Relative) := by
    funext v
    apply (defect_zero_iff _).mp
    have h := relative_defect q r g v
    rw [hg,mul_zero] at h
    exact le_antisymm h (defect_nonneg _)
  refine ⟨g root,?_⟩
  calc
    g = assemble (g root) (relative g) := (assemble_relative g).symm
    _ = fun _ => g root := by
      rw [hr]
      funext v
      simp [assemble,anchored]

end OperatorDerivativeRewrite.Foundation.CubeTemporalConfinement
