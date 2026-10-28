import Foundation.YMPositivePower
import Foundation.SU2SevenLinkGroundTransform
import Foundation.SU2HomogeneousPlaquetteObstruction
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Direct positive-kernel realization of the normalized seven-link transfer.
No indexed/tuple identification or supplied positive eigenfunction is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkVacuum
open QuaternionSU2Representation SU2WilsonConvolution SU2SevenLinkTransfer
open SU2SevenLinkVariational BoundedExponentialTiltResponse

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact homeomorph.symm.secondCountableTopology

private instance state_secondCountable : SecondCountableTopology State := by infer_instance
private instance state_borel : BorelSpace State := by infer_instance

private def edgeDensity (β : ℝ) (v : SU2) : ℝ := density law halfTrace β v

@[fun_prop] private theorem edgeDensity_measurable (β : ℝ) : Measurable (edgeDensity β) :=
  (halfTrace_measurable.const_mul β).exp.div_const _

private theorem edgeDensity_nonneg (β : ℝ) (v : SU2) : 0 ≤ edgeDensity β v :=
  density_nonneg law halfTrace halfTrace_measurable halfTrace_bound β v

def noiseDensity (β : ℝ) (v : State) : ℝ :=
  edgeDensity β v.1*(edgeDensity β v.2.1*(edgeDensity β v.2.2.1*
    (edgeDensity β v.2.2.2.1*(edgeDensity β v.2.2.2.2.1*
      (edgeDensity β v.2.2.2.2.2.1*edgeDensity β v.2.2.2.2.2.2)))))

theorem noiseDensity_measurable (β : ℝ) : Measurable (noiseDensity β) := by
  unfold noiseDensity
  have hd := edgeDensity_measurable β
  fun_prop

theorem noiseDensity_nonneg (β : ℝ) (v : State) : 0 ≤ noiseDensity β v := by
  unfold noiseDensity
  have hd := edgeDensity_nonneg β
  exact mul_nonneg (hd _) (mul_nonneg (hd _) (mul_nonneg (hd _)
    (mul_nonneg (hd _) (mul_nonneg (hd _) (mul_nonneg (hd _) (hd _))))))

/-- Exact density of the actual product of seven normalized Wilson increments. -/
theorem noise_withDensity (β : ℝ) :
    noise β=haar.withDensity (fun v => ENNReal.ofReal (noiseDensity β v)) := by
  have hd : Measurable (fun v => ENNReal.ofReal (edgeDensity β v)) :=
    (edgeDensity_measurable β).ennreal_ofReal
  change edgeLaw (law.withDensity (fun v => ENNReal.ofReal (edgeDensity β v)))=_
  unfold haar edgeLaw
  rw [prod_withDensity hd hd]
  repeat' rw [prod_withDensity hd (by fun_prop)]
  congr 1
  funext v
  simp only [noiseDensity,ENNReal.ofReal_mul (edgeDensity_nonneg β _)]

private theorem haar_inverse : haar.map Inv.inv=haar := by
  have he := SU2SevenLinkVariational.noise_inverse 0
  simpa only [SU2HomogeneousPlaquetteObstruction.noise_zero] using he

private instance haar_leftInvariant : haar.IsMulLeftInvariant := by
  letI : MeasurableMul State := {
    measurable_const_mul := fun g => (continuous_const_mul g).measurable
    measurable_mul_const := fun g => (continuous_mul_const g).measurable }
  letI : MeasurableInv State := ⟨continuous_inv.measurable⟩
  have hi : haar.inv=haar := haar_inverse
  rw [← hi]
  infer_instance

/-- Exact normalized transfer integral against the EXISTING tuple Haar law. -/
theorem step_density (β : ℝ) (f : State → ℝ) (s : State) :
    SU2SevenLinkTransfer.step β f s=∫ r,noiseDensity β (s⁻¹*r)*f r ∂haar := by
  unfold SU2SevenLinkTransfer.step
  rw [noise_withDensity]
  rw [integral_withDensity_eq_integral_toReal_smul
    (noiseDensity_measurable β).ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (noiseDensity_nonneg β _),smul_eq_mul]
  have he := integral_mul_left_eq_self (μ := haar)
    (fun r => noiseDensity β (s⁻¹*r)*f r) s
  simpa only [inv_mul_cancel_left] using he


private theorem edgeDensity_bounds (β : ℝ) (v : SU2) :
    Real.exp (-|β|)/partition law halfTrace β ≤ edgeDensity β v ∧
      edgeDensity β v ≤ Real.exp |β|/partition law halfTrace β := by
  have hz := partition_pos law halfTrace halfTrace_measurable halfTrace_bound β
  have he : |β*halfTrace v| ≤ |β| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (halfTrace_bound v) (abs_nonneg β)
  unfold edgeDensity density
  exact ⟨div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp he).1) hz.le,
    div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp he).2) hz.le⟩

private theorem noiseDensity_bounds (β : ℝ) (v : State) :
    (Real.exp (-|β|)/partition law halfTrace β)^7 ≤ noiseDensity β v ∧
      noiseDensity β v ≤ (Real.exp |β|/partition law halfTrace β)^7 := by
  have hz := partition_pos law halfTrace halfTrace_measurable halfTrace_bound β
  have hlo := mul_le_mul ((edgeDensity_bounds β v.1).1)
    (mul_le_mul ((edgeDensity_bounds β v.2.1).1)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.1).1)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.1).1)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.2.1).1)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.2.2.1).1) ((edgeDensity_bounds β v.2.2.2.2.2.2).1) (by positivity) (edgeDensity_nonneg β v.2.2.2.2.2.1)) (by positivity) (edgeDensity_nonneg β v.2.2.2.2.1)) (by positivity) (edgeDensity_nonneg β v.2.2.2.1)) (by positivity) (edgeDensity_nonneg β v.2.2.1)) (by positivity) (edgeDensity_nonneg β v.2.1)) (by positivity) (edgeDensity_nonneg β v.1)
  have hup := mul_le_mul ((edgeDensity_bounds β v.1).2)
    (mul_le_mul ((edgeDensity_bounds β v.2.1).2)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.1).2)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.1).2)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.2.1).2)
    (mul_le_mul ((edgeDensity_bounds β v.2.2.2.2.2.1).2) ((edgeDensity_bounds β v.2.2.2.2.2.2).2) (edgeDensity_nonneg β v.2.2.2.2.2.2) (by positivity))
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.2.1) (edgeDensity_nonneg β v.2.2.2.2.2.2)) (by positivity))
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.2.1) (edgeDensity_nonneg β v.2.2.2.2.2.2))) (by positivity))
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.2.1) (edgeDensity_nonneg β v.2.2.2.2.2.2)))) (by positivity))
    (mul_nonneg (edgeDensity_nonneg β v.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.2.1) (edgeDensity_nonneg β v.2.2.2.2.2.2))))) (by positivity))
    (mul_nonneg (edgeDensity_nonneg β v.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.1)
    (mul_nonneg (edgeDensity_nonneg β v.2.2.2.2.2.1) (edgeDensity_nonneg β v.2.2.2.2.2.2)))))) (by positivity)
  constructor
  · convert hlo using 1 <;> (try dsimp [noiseDensity]) <;> ring
  · convert hup using 1 <;> (try dsimp [noiseDensity]) <;> ring

private theorem halfWeight_bounds (t : ℝ) (s : State) :
    Real.exp (-|t|/2) ≤ halfWeight t s ∧ halfWeight t s ≤ Real.exp (|t|/2) := by
  have he : |t*first s/2| ≤ |t|/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_mul]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t))
      (by norm_num : (0:ℝ) ≤ 2)
  exact ⟨Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).1]),
    Real.exp_le_exp.mpr (abs_le.mp he).2⟩

def kernelDensity (β t : ℝ) (s r : State) : ℝ :=
  halfWeight t s*noiseDensity β (s⁻¹*r)*halfWeight t r

theorem kernelDensity_measurable (β t : ℝ) : Measurable (Function.uncurry (kernelDensity β t)) := by
  exact (((halfWeight_measurable t).comp measurable_fst).mul
    ((noiseDensity_measurable β).comp (by fun_prop))).mul
    ((halfWeight_measurable t).comp measurable_snd)

private def lower (β t : ℝ) : ℝ :=
  (Real.exp (-|t|/2))^2*(Real.exp (-|β|)/partition law halfTrace β)^7

private def upper (β t : ℝ) : ℝ :=
  (Real.exp (|t|/2))^2*(Real.exp |β|/partition law halfTrace β)^7

private theorem lower_pos (β t : ℝ) : 0 < lower β t := by
  have hz := partition_pos law halfTrace halfTrace_measurable halfTrace_bound β
  unfold lower
  positivity

private theorem upper_pos (β t : ℝ) : 0 < upper β t := by
  have hz := partition_pos law halfTrace halfTrace_measurable halfTrace_bound β
  unfold upper
  positivity

private theorem kernelDensity_bounds (β t : ℝ) (s r : State) :
    lower β t ≤ kernelDensity β t s r ∧ kernelDensity β t s r ≤ upper β t := by
  have hz := partition_pos law halfTrace halfTrace_measurable halfTrace_bound β
  have hd := noiseDensity_bounds β (s⁻¹*r)
  have hs := halfWeight_bounds t s
  have hr := halfWeight_bounds t r
  have hp (x : State) : 0 < halfWeight t x := Real.exp_pos _
  unfold lower upper kernelDensity
  constructor
  · calc
      _ = Real.exp (-|t|/2)*(Real.exp (-|β|)/partition law halfTrace β)^7*Real.exp (-|t|/2) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hs.1 hd.1 (by positivity) (hp s).le) hr.1
        (Real.exp_pos _).le (mul_nonneg (hp s).le (noiseDensity_nonneg β _))
  · calc
      _ ≤ Real.exp (|t|/2)*(Real.exp |β|/partition law halfTrace β)^7*Real.exp (|t|/2) :=
        mul_le_mul (mul_le_mul hs.2 hd.2 (noiseDensity_nonneg β _) (Real.exp_pos _).le) hr.2
          (hp r).le (by positivity)
      _ = _ := by ring

/-- The kernel is ALREADY normalized by all seven Wilson partitions. -/
theorem kernelDensity_apply (β t : ℝ) (f : State → ℝ) (s : State) :
    YMPositivePower.applyKernel haar (kernelDensity β t) f s=spatialStep β t f s := by
  unfold YMPositivePower.applyKernel spatialStep
  rw [step_density]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  unfold kernelDensity halfWeight
  ring

/-- The exact existing normalized GroundData contract is inhabited for every
real temporal parameter and spatial tilt; no ground-state axiom is added. -/
theorem groundData_nonempty (β t : ℝ) : Nonempty (SU2SevenLinkGroundTransform.GroundData β t) := by
  obtain ⟨lam,ψ,hl,hu,hm,hb,he⟩ := YMPositivePower.positive_eigenfunction_exists
    haar (kernelDensity β t) (lower β t) (upper β t) (kernelDensity_measurable β t)
    (lower_pos β t) (kernelDensity_bounds β t) 1
  refine ⟨⟨lam,ψ,(lower β t)/(upper β t),(upper β t)/(lower β t),
    (lower_pos β t).trans_le hl,div_pos (lower_pos β t) (upper_pos β t),hm,?_,?_⟩⟩
  · intro s
    refine ⟨(hb s).1,?_⟩
    rw [abs_of_pos ((div_pos (lower_pos β t) (upper_pos β t)).trans_le (hb s).1)]
    exact (hb s).2
  · intro s
    rw [← kernelDensity_apply]
    exact he s


/-- Chosen from the PROVED normalized existence theorem, never postulated. -/
def data (β t : ℝ) : SU2SevenLinkGroundTransform.GroundData β t :=
  Classical.choice (groundData_nonempty β t)

/-- The formerly missing-vacuum conditional local comparison is now realized
in the actual normalized stationary law. Small independent spatial tilt is
required; this is not an equal-coupling or physical4D assertion. -/
theorem realized_stationary_obstruction_interval (β : ℝ) (hc : coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      let v := (data β t).evenized
      let f := v.observable (SU2SevenLinkSpatialSeparation.oddA β) (SU2SevenLinkSpatialSeparation.oddB β)
      (∫ s,f s ∂v.stationary)=0 ∧
      0 < (∫ s,(f s)^2 ∂v.stationary) ∧
      coefficient β^4 <
        (∫ s,f s*(∫ r,f r ∂v.kernel s) ∂v.stationary)/(∫ s,(f s)^2 ∂v.stationary) := by
  obtain ⟨δ,hδ,hδ1,hall⟩ := SU2SevenLinkGroundTransform.exists_stationary_obstruction_interval β hc
  exact ⟨δ,hδ,hδ1,fun t ht htδ => hall t ht htδ (data β t)⟩

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkVacuum
