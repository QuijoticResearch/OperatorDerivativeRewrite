import Foundation.HigherHeatFirstChannelRange
import Foundation.PeriodicGroundBridge
import Foundation.PeriodicGaussianTransferGram

/-! The classical pure-order negative-square obstruction, realized on the completed
signed analytic domain and tested against actual Wilson probability Hilbert spaces.
No arbitrary operator transfer, shrinking horizon, or physical gap is excluded. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.WilsonSignedPairingObstruction
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatCompletedSignedMean

def leading (m : ℕ) (T : ℝ≥0) : ℝ :=
  ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(T:ℝ))

def witness (m : ℕ) (T : ℝ≥0) : Domain :=
  core terminalCylinder-leading m T • core (terminalCylinder^(2*m-1))

theorem leading_ne_zero (m : ℕ) (T : ℝ≥0) (hT : 0<T) : leading m T≠0 := by
  unfold leading
  exact mul_ne_zero (by positivity)
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast hT)))

private theorem power_pairing (m : ℕ) (hm : 0<m) (T : ℝ≥0) (hT : 0<T) (r s : ℕ) :
    pairing m hm T hT (core (terminalCylinder^r)) (core (terminalCylinder^s)) =
      PseudoPolynomialStein.moment (2*m) ((-1:ℝ)^(m+1)*(T:ℝ)) (r+s) := by
  rw [pairing_core_real,← pow_add,terminal_moments]
  rfl

theorem terminal_null (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T) :
    pairing m (by omega) T hT (core terminalCylinder) (core terminalCylinder)=0 := by
  have h := power_pairing m (by omega) T hT 1 1
  simp only [pow_one] at h
  rw [h,PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ 2
    (PseudoMomentPositivity.pure_order_nondiagonal_degrees (2*m) (by omega)).1]

theorem upper_terminal_null (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T) :
    pairing m (by omega) T hT (core (terminalCylinder^(2*m-1)))
      (core (terminalCylinder^(2*m-1)))=0 := by
  rw [power_pairing]
  apply PseudoPolynomialStein.moment_off_order (2*m) (by omega)
  rw [show 2*m-1+(2*m-1)=2*(2*m-1) by omega]
  exact (PseudoMomentPositivity.pure_order_nondiagonal_degrees (2*m) (by omega)).2

theorem terminal_cross (m : ℕ) (hm : 0<m) (T : ℝ≥0) (hT : 0<T) :
    pairing m hm T hT (core (terminalCylinder^(2*m-1))) (core terminalCylinder)=leading m T :=
  HigherHeatFirstChannelRange.witness_pairing m hm T hT

theorem terminal_centered (m : ℕ) (hm : 0<m) (T : ℝ≥0) (hT : 0<T) :
    mean m hm T hT (core terminalCylinder)=0 := by
  have h : core terminalCylinder=core (terminalCylinder^1) := by rw [pow_one]
  rw [h,mean_core_real,terminal_moments,
    PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ 1 (by
      exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))]
  rfl

theorem witness_centered (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T) :
    mean m (by omega) T hT (witness m T)=0 := by
  rw [witness,map_sub,map_smul,terminal_centered,
    HigherHeatFirstChannelRange.witness_centered,smul_zero,sub_zero]

theorem witness_pairing (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T) :
    pairing m (by omega) T hT (witness m T) (witness m T)= -2*(leading m T)^2 := by
  have hc := terminal_cross m (by omega) T hT
  have hcs := (pairing_comm m (by omega) T hT (core terminalCylinder)
    (core (terminalCylinder^(2*m-1)))).trans hc
  simp only [witness,map_sub,map_smul,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,terminal_null m hm T hT,
    upper_terminal_null m hm T hT,hc,hcs]
  ring

theorem witness_negative (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T) :
    pairing m (by omega) T hT (witness m T) (witness m T)<0 := by
  rw [witness_pairing m hm T hT]
  nlinarith [sq_pos_of_ne_zero (leading_ne_zero m T hT)]

/-- Even a nonlinear map into a real Hilbert space cannot preserve centered
signed self-pairings. This contradiction already lies on polynomial cylinders. -/
theorem no_centered_hilbert_realization (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ¬ ∃ J : Domain → H, ∀ u : Domain, mean m (by omega) T hT u=0 →
      inner ℝ (J u) (J u)=pairing m (by omega) T hT u u := by
  rintro ⟨J,hJ⟩
  have hh := hJ (witness m T) (witness_centered m hm T hT)
  have hn := witness_negative m hm T hT
  rw [← hh,real_inner_self_eq_norm_sq] at hn
  exact (not_lt_of_ge (sq_nonneg _)) hn

/-- Absolute error on this fixed witness has a positive floor. This is not an
operator norm bound or a normalization-independent obstruction. -/
theorem positive_form_defect (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    (q : ℝ) (hq : 0≤q) :
    2*(leading m T)^2 ≤ |q-pairing m (by omega) T hT (witness m T) (witness m T)| := by
  rw [witness_pairing m hm T hT]
  have hh := le_abs_self (q- -2*(leading m T)^2)
  linarith

/-- Original boundary-conditioned Wilson L2, arbitrary coupling and endpoints. -/
theorem conditional_native_defect (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    (β : ℝ) (U W : PeriodicTemporalSlab.State)
    (f : Lp ℝ 2 (PeriodicGroundBridge.law β U W)) :
    2*(leading m T)^2 ≤ |inner ℝ f f-
      pairing m (by omega) T hT (witness m T) (witness m T)| := by
  apply positive_form_defect m hm T hT
  rw [real_inner_self_eq_norm_sq]
  exact sq_nonneg _

/-- The single-witness error floor is sharp: the zero native image attains it.
This does not assert a simultaneous optimal approximation of all pairings. -/
theorem conditional_zero_defect (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    (β : ℝ) (U W : PeriodicTemporalSlab.State) :
    |inner ℝ (0 : Lp ℝ 2 (PeriodicGroundBridge.law β U W)) 0-
      pairing m (by omega) T hT (witness m T) (witness m T)|=2*(leading m T)^2 := by
  rw [inner_zero_left,witness_pairing m hm T hT]
  have he : (0:ℝ)- -2*(leading m T)^2=2*(leading m T)^2 := by ring
  rw [he,abs_of_nonneg (by positivity)]

theorem no_conditional_centered_realization (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    (β : ℝ) (U W : PeriodicTemporalSlab.State) :
    ¬ ∃ J : Domain → Lp ℝ 2 (PeriodicGroundBridge.law β U W),
      ∀ u : Domain, mean m (by omega) T hT u=0 →
        inner ℝ (J u) (J u)=pairing m (by omega) T hT u u :=
  no_centered_hilbert_realization m hm T hT

/-- At a FIXED positive horizon, arbitrary coupling-dependent endpoints and
native observables cannot make this signed covariance defect disappear. -/
theorem conditional_defect_not_tendsto (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    (U W : ℝ → PeriodicTemporalSlab.State)
    (f : ∀ β : ℝ, Lp ℝ 2 (PeriodicGroundBridge.law β (U β) (W β))) :
    ¬ Tendsto (fun β : ℝ => |inner ℝ (f β) (f β)-
      pairing m (by omega) T hT (witness m T) (witness m T)|) atTop (𝓝 0) := by
  intro hh
  have hb := ge_of_tendsto hh (Filter.Eventually.of_forall
    (fun β => conditional_native_defect m hm T hT β (U β) (W β) (f β)))
  nlinarith [sq_pos_of_ne_zero (leading_ne_zero m T hT)]

/-- Actual stationary Wilson transfer Gram, ONLY on its proved bounded measurable
full-gauge-invariant native core, at nonnegative coupling. -/
theorem stationary_transfer_defect (m : ℕ) (hm : 1<m) (T : ℝ≥0) (hT : 0<T)
    {β : ℝ} (hβ : 0≤β) (g : PeriodicSlabGround.GroundData β)
    (f : PeriodicTemporalSlab.State → ℝ) (hf : Measurable f)
    (hmem : MemLp f 2 g.stationary) (B : ℝ) (hb : ∀ U, |f U|≤B)
    (hInv : ∀ a U, f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    2*(leading m T)^2 ≤ |inner ℝ (PeriodicSlabL2.operator g (hmem.toLp f)) (hmem.toLp f)-
      pairing m (by omega) T hT (witness m T) (witness m T)| :=
  positive_form_defect m hm T hT _
    (PeriodicGaussianTransferGram.native_nonnegative hβ g f hf hmem B hb hInv)

end OperatorDerivativeRewrite.Foundation.WilsonSignedPairingObstruction
