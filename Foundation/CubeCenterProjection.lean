import Foundation.CubeSlabL2

/-! The old all-center cross-ratio witness is pure gauge on the actual cube.
This refutes its direct transfer to the projected slab; it proves no physical gap. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubeCenterProjection
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge

def centerState : State := fun _ => SU2StapleExtremes.minusOne

def checkerGauge (v : SpatialVertex) : SU2 :=
  if ((v 0).val+(v 1).val+(v 2).val)%2=0 then 1 else SU2StapleExtremes.minusOne

private theorem center_square :
    SU2StapleExtremes.minusOne*SU2StapleExtremes.minusOne=(1 : SU2) := by
  apply Subtype.ext
  change QuaternionSU2Representation.repr (-1)*QuaternionSU2Representation.repr (-1)=1
  have hr : QuaternionSU2Representation.repr (-1)= -(1 : SU2TraceHessianModel.M2) := by
    simpa using repr_real (-1)
  rw [hr]
  simp

private theorem center_inverse : SU2StapleExtremes.minusOne⁻¹=SU2StapleExtremes.minusOne := by
  calc
    _ = SU2StapleExtremes.minusOne⁻¹*1 := (mul_one _).symm
    _ = SU2StapleExtremes.minusOne⁻¹*
        (SU2StapleExtremes.minusOne*SU2StapleExtremes.minusOne) := by rw [center_square]
    _ = _ := by group

/-- The all-center link field is in the vacuum's actual full-vertex gauge orbit. -/
theorem checker_center : gaugeAction checkerGauge (1 : State)=centerState := by
  funext e
  rcases e with ⟨⟨v,a⟩,he⟩
  change v a=0 at he
  have hex (w : SpatialVertex) : ∃ x y z : Fin 2, w=![x,y,z] := by
    refine ⟨w 0,w 1,w 2,?_⟩
    ext i
    fin_cases i <;> rfl
  obtain ⟨x,y,z,hv⟩ := hex v
  clear hex
  subst v
  fin_cases a <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [gaugeAction,checkerGauge,centerState,shift,Function.update,
      center_inverse,center_square] at *
  all_goals
    exfalso
    revert he
    decide +kernel

theorem kernel_center_left (beta : ℝ) (V : State) :
    kernel beta centerState V=kernel beta 1 V := by
  rw [← checker_center]
  exact kernel_left_invariant beta checkerGauge 1 V

theorem kernel_center_right (beta : ℝ) (U : State) :
    kernel beta U centerState=kernel beta U 1 := by
  rw [← checker_center]
  exact kernel_right_invariant beta checkerGauge U 1

/-- Gauge projection collapses this specific old extremizing four-point witness. -/
theorem actual_center_crossRatio (beta : ℝ) :
    YMPositiveKernel.crossRatio (kernel beta) (1 : State) centerState 1 centerState=1 := by
  unfold YMPositiveKernel.crossRatio
  simp_rw [kernel_center_left,kernel_center_right]
  exact div_self (mul_pos (kernel_positive beta 1 1) (kernel_positive beta 1 1)).ne'

/-- The earlier kinetic witness remains correct BEFORE gauge projection. -/
theorem unprojected_center_crossRatio (beta : ℝ) :
    YMPositiveKernel.crossRatio (YMPositiveKernel.kinetic (n := 12) beta)
      (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne)
      (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne)=Real.exp (48*beta) := by
  have h := YMPositiveKernel.center_crossRatio (n := 12) (fun _ => 1)
    (fun _ => zero_lt_one) beta
  have hw : YMPositiveKernel.weightedKernel (fun _ : (Fin 12 → SU2) => 1) beta=
      YMPositiveKernel.kinetic beta := by funext C D; simp [YMPositiveKernel.weightedKernel]
  rw [hw] at h
  norm_num at h
  exact h

/-- A precise failure of preserving the raw center witness under actual projection. -/
theorem projection_changes_center_witness (beta : ℝ) (hb : 0 < beta) :
    YMPositiveKernel.crossRatio (kernel beta) (1 : State) centerState 1 centerState <
      YMPositiveKernel.crossRatio (YMPositiveKernel.kinetic (n := 12) beta)
        (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne)
        (fun _ => 1) (fun _ => SU2StapleExtremes.minusOne) := by
  rw [actual_center_crossRatio,unprojected_center_crossRatio]
  exact Real.one_lt_exp_iff.mpr (by positivity)


/-- The same growth occurs for the ACTUAL homogeneous slab weight before temporal averaging. -/
theorem unintegrated_center_crossRatio (beta : ℝ) :
    YMPositiveKernel.crossRatio (fun U V => weight beta U V 1)
      (1 : State) centerState 1 centerState=Real.exp (48*beta) := by
  have hI : spatialAction (1 : State)=0 := by
    simp [spatialAction,spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have hC : spatialAction centerState=0 := by
    rw [← checker_center,spatial_action_invariant,hI]
  have htII : temporalAction (1 : State) 1 1=0 := by
    simp [temporalAction,temporalWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have htCC : temporalAction centerState centerState 1=0 := by
    simp [temporalAction,temporalWord,centerState,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have htIC : temporalAction (1 : State) centerState 1=24 := by
    norm_num [temporalAction,temporalWord,centerState,center_inverse,
      SU2OpenLinkGaugeObstruction.halfTrace_minusOne,edge_count]
  have htCI : temporalAction centerState (1 : State) 1=24 := by
    norm_num [temporalAction,temporalWord,centerState,
      SU2OpenLinkGaugeObstruction.halfTrace_minusOne,edge_count]
  dsimp only [YMPositiveKernel.crossRatio,weight,halfAction]
  rw [hI,hC,htII,htCC,htIC,htCI]
  norm_num
  simp only [← Real.exp_neg]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The actual temporal Haar average does not preserve this unintegrated witness. -/
theorem actual_average_changes_center_witness (beta : ℝ) (hb : 0 < beta) :
    YMPositiveKernel.crossRatio (kernel beta) (1 : State) centerState 1 centerState <
      YMPositiveKernel.crossRatio (fun U V => weight beta U V 1)
        (1 : State) centerState 1 centerState := by
  rw [actual_center_crossRatio,unintegrated_center_crossRatio]
  exact Real.one_lt_exp_iff.mpr (by positivity)

end OperatorDerivativeRewrite.Foundation.CubeCenterProjection
