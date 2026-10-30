import Foundation.PeriodicInteriorHolonomy
import Foundation.SU2BoundedObservableGradient
import Foundation.SU2OpenLinkGaugeObstruction
import Mathlib.Tactic.Group

/-! Exact nonlinear periodic SU2 flat links with nontrivial winding holonomy. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.PeriodicSU2FlatHolonomy
open PeriodicInteriorGaugeKernel QuaternionSU2Representation
open SU2TraceHessianModel SU2BoundedObservableGradient

abbrev Links := Edge → SU2
abbrev Gauge := Vertex → SU2

def plaquette (U : Links) (v : Vertex) (i j : Direction) : SU2 :=
  U (v,i)*U (shift v i,j)*(U (shift v j,i))⁻¹*(U (v,j))⁻¹

def action (U : Links) : ℝ := ∑ p : Face,(1-halfTrace (plaquette U p.val.1 p.val.2.1 p.val.2.2))

def seam (a : SU2) (e : Edge) : SU2 := if e.2=0 ∧ e.1 0=3 then a else 1

theorem seam_flat (a : SU2) (v : Vertex) (i j : Direction) (hij : i<j) :
    plaquette (seam a) v i j=1 := by
  have hj : j≠0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
  by_cases hi : i=0
  · subst i
    simp [plaquette,seam,shift,hj,Ne.symm hj]
  · simp [plaquette,seam,hi,hj]

theorem seam_action (a : SU2) : action (seam a)=0 := by
  unfold action
  apply Finset.sum_eq_zero
  intro p _
  rw [seam_flat a _ _ _ p.property,SU2OpenLinkGaugeObstruction.halfTrace_one,sub_self]

def gaugeAction (g : Gauge) (U : Links) (e : Edge) : SU2 :=
  g e.1*U e*(g (shift e.1 e.2))⁻¹

theorem plaquette_gauge (g : Gauge) (U : Links) (v : Vertex) (i j : Direction) :
    plaquette (gaugeAction g U) v i j=g v*plaquette U v i j*(g v)⁻¹ := by
  unfold plaquette gaugeAction
  rw [shift_commute v i j]
  group

theorem action_gauge (g : Gauge) (U : Links) : action (gaugeAction g U)=action U := by
  unfold action
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquette_gauge,halfTrace_conjugate]

def winding (U : Links) : SU2 :=
  U (origin,0)*U (PeriodicInteriorHolonomy.once,0)*
    U (PeriodicInteriorHolonomy.twice,0)*U (PeriodicInteriorHolonomy.thrice,0)

theorem winding_seam (a : SU2) : winding (seam a)=a := by
  have h0 : (0 : ZMod 4) ≠ 3 := by decide
  have h1 : (1 : ZMod 4) ≠ 3 := by decide
  have h2 : (2 : ZMod 4) ≠ 3 := by decide
  norm_num [winding,seam,h0,h1,h2,PeriodicInteriorHolonomy.once,PeriodicInteriorHolonomy.twice,
    PeriodicInteriorHolonomy.thrice,origin,shift]

theorem winding_gauge (g : Gauge) (U : Links) :
    winding (gaugeAction g U)=g origin*winding U*(g origin)⁻¹ := by
  unfold winding gaugeAction
  rw [PeriodicInteriorHolonomy.cycle_closes]
  change (g origin*U (origin,0)*(g PeriodicInteriorHolonomy.once)⁻¹)*
    (g PeriodicInteriorHolonomy.once*U (PeriodicInteriorHolonomy.once,0)*(g PeriodicInteriorHolonomy.twice)⁻¹)*
    (g PeriodicInteriorHolonomy.twice*U (PeriodicInteriorHolonomy.twice,0)*(g PeriodicInteriorHolonomy.thrice)⁻¹)*
    (g PeriodicInteriorHolonomy.thrice*U (PeriodicInteriorHolonomy.thrice,0)*(g origin)⁻¹)=_
  group

def pureGauge (U : Links) : Prop := ∃ g : Gauge,gaugeAction g (fun _ => 1)=U

theorem winding_one : winding (fun _ => 1)=1 := by simp [winding]

theorem pureGauge_winding (U : Links) (h : pureGauge U) : winding U=1 := by
  obtain ⟨g,hg⟩ := h
  rw [← hg,winding_gauge,winding_one]
  simp

theorem seam_not_pureGauge (a : SU2) (ha : a≠1) : ¬ pureGauge (seam a) := by
  intro h
  exact ha ((winding_seam a).symm.trans (pureGauge_winding _ h))

def windingTrace (U : Links) : ℝ := halfTrace (winding U)

theorem windingTrace_gauge (g : Gauge) (U : Links) :
    windingTrace (gaugeAction g U)=windingTrace U := by
  rw [windingTrace,winding_gauge,halfTrace_conjugate]
  rfl

def family (θ : ℝ) : Links := seam (rotationPoint θ)

theorem family_action (θ : ℝ) : action (family θ)=0 := seam_action _

theorem family_windingTrace (θ : ℝ) : windingTrace (family θ)=Real.cos θ := by
  rw [windingTrace,family,winding_seam]
  change traceReal (rotation θ)/2=Real.cos θ
  rw [rotation_trace]
  ring

theorem family_not_pureGauge (θ : ℝ) (hθ : 0<θ) (hπ : θ≤Real.pi) :
    ¬ pureGauge (family θ) := by
  apply seam_not_pureGauge
  intro he
  have hc : Real.cos θ < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (show θ∈Set.Icc 0 Real.pi from ⟨hθ.le,hπ⟩) hθ
  have ht := family_windingTrace θ
  rw [windingTrace,family,winding_seam,he,SU2OpenLinkGaugeObstruction.halfTrace_one] at ht
  linarith

theorem arbitrarily_small_flat (ε : ℝ) (hε : 0<ε) :
    ∃ θ : ℝ,0<θ ∧ θ<ε ∧ action (family θ)=0 ∧ ¬ pureGauge (family θ) := by
  let θ := min (ε/2) (Real.pi/2)
  have hp : 0<θ := lt_min (by positivity) (by positivity)
  have he : θ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hπ : θ≤Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  exact ⟨θ,hp,he,family_action θ,family_not_pureGauge θ hp hπ⟩

theorem rotationPoint_zero : rotationPoint 0=(1 : SU2) := by
  apply Subtype.ext
  simp [rotationPoint,rotation]

theorem family_zero : family 0=(fun _ => 1) := by
  funext e
  simp [family,seam,rotationPoint_zero]

theorem family_continuous : Continuous family := by
  have hr : Continuous rotationPoint := by
    have hc : Continuous rotation := by unfold rotation; fun_prop
    exact hc.subtype_mk _
  apply continuous_pi
  intro e
  by_cases he : e.2=0 ∧ e.1 0=3
  · simpa only [family,seam,if_pos he] using hr
  · simp only [family,seam,if_neg he]
    exact continuous_const

theorem family_tendsto : Filter.Tendsto family (nhds (0:ℝ)) (nhds (fun _ => (1 : SU2))) := by
  simpa only [family_zero] using family_continuous.continuousAt.tendsto (x := (0:ℝ))

theorem family_gauge_equivalence (θ φ : ℝ) (hθ : θ∈Set.Icc 0 Real.pi)
    (hφ : φ∈Set.Icc 0 Real.pi) :
    (∃ g : Gauge,gaugeAction g (family θ)=family φ) ↔ θ=φ := by
  constructor
  · rintro ⟨g,hg⟩
    have ht := congrArg windingTrace hg
    rw [windingTrace_gauge,family_windingTrace,family_windingTrace] at ht
    exact Real.strictAntiOn_cos.injOn hθ hφ ht
  · intro he
    subst φ
    refine ⟨fun _ => 1,?_⟩
    funext e
    simp [gaugeAction]

theorem action_nonnegative (U : Links) : 0 ≤ action U := by
  unfold action
  apply Finset.sum_nonneg
  intro p _
  have h := (abs_le.mp (halfTrace_bound (plaquette U p.val.1 p.val.2.1 p.val.2.2))).2
  linarith

theorem nonisolated_flat (S : Set Links) (hS : S∈nhds (fun _ : Edge => (1 : SU2))) :
    ∃ U : Links,U∈S ∧ action U=0 ∧ ¬ pureGauge U := by
  have ht := family_tendsto.eventually hS
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨θ,hθ,hθε,ha,hg⟩ := arbitrarily_small_flat ε hε
  have hin : θ∈Metric.ball (0:ℝ) ε := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hθ] using hθε
  exact ⟨family θ,hsub hin,ha,hg⟩

theorem small_trace_defect (ε : ℝ) (hε : 0<ε) :
    ∃ θ : ℝ,0<θ ∧ θ<ε ∧ 0<1-windingTrace (family θ) ∧ action (family θ)=0 := by
  let θ := min (ε/2) (Real.pi/2)
  have hp : 0<θ := lt_min (by positivity) (by positivity)
  have he : θ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hπ : θ≤Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hc : Real.cos θ<1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (show θ∈Set.Icc 0 Real.pi from ⟨hp.le,hπ⟩) hp
  refine ⟨θ,hp,he,?_,family_action θ⟩
  rw [family_windingTrace]
  linarith

theorem no_local_holonomy_coercivity (c ε : ℝ) (hc : 0<c) (hε : 0<ε) :
    ¬ ∀ θ : ℝ,0<θ -> θ<ε -> c*(1-windingTrace (family θ)) ≤ action (family θ) := by
  intro hb
  obtain ⟨θ,hθ,he,hd,ha⟩ := small_trace_defect ε hε
  have h := hb θ hθ he
  rw [ha] at h
  exact (not_le_of_gt (mul_pos hc hd)) h

theorem no_holonomy_coercivity (c : ℝ) (hc : 0<c) :
    ¬ ∀ U : Links,c*(1-windingTrace U) ≤ action U := by
  intro hb
  exact no_local_holonomy_coercivity c 1 hc (by norm_num) (fun θ _ _ => hb (family θ))

end OperatorDerivativeRewrite.Foundation.PeriodicSU2FlatHolonomy
