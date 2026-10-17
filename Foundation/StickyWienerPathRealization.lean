import Foundation.BrownianMassPathFunctional
import Foundation.BrownianMassRandomTimeChange

/-! A Borel map from Wiener path space to the actual sticky continuous path.
The totalization outside good mass paths is explicit; agreement uses one
full-measure event simultaneously at every time and stickiness parameter. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyWienerPathRealization
open InfiniteGaussian IBMConstructedSources BrownianMassPathFunctional
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem monotone_set_measurable : MeasurableSet {p : C(ℝ≥0, ℝ) | Monotone p} := by
  have hc : Continuous (fun p : C(ℝ≥0, ℝ) => (p : ℝ≥0 → ℝ)) :=
    continuous_pi (fun _ => continuous_eval_const _)
  exact (isClosed_monotone.preimage hc).measurableSet

def cumulativePath (p : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  by
    classical
    exact if Monotone (functional p) then functional p else 0

theorem cumulative_measurable : Measurable cumulativePath := by
  classical
  exact Measurable.ite (monotone_set_measurable.preimage functional_measurable)
    functional_measurable measurable_const

theorem cumulative_monotone (p : C(ℝ≥0, ℝ)) : Monotone (cumulativePath p) := by
  classical
  by_cases hp : Monotone (functional p)
  · simpa only [cumulativePath,if_pos hp] using hp
  · simp only [cumulativePath,if_neg hp,ContinuousMap.coe_zero]
    exact monotone_const

def mass (p : C(ℝ≥0, ℝ)) (t : ℝ≥0) : ℝ≥0 :=
  (cumulativePath p t-cumulativePath p 0).toNNReal

theorem mass_continuous (p : C(ℝ≥0, ℝ)) : Continuous (mass p) :=
  continuous_real_toNNReal.comp ((cumulativePath p).continuous.sub continuous_const)

theorem mass_monotone (p : C(ℝ≥0, ℝ)) : Monotone (mass p) :=
  fun _ _ h => Real.toNNReal_mono (sub_le_sub_right (cumulative_monotone p h) _)

theorem mass_zero (p : C(ℝ≥0, ℝ)) : mass p 0 = 0 := by simp [mass]

theorem mass_coordinate_measurable (t : ℝ≥0) : Measurable (fun p => mass p t) :=
  (((ContinuousMap.measurable_eval t).comp cumulative_measurable).sub
    ((ContinuousMap.measurable_eval 0).comp cumulative_measurable)).real_toNNReal

def inverse (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ≥0 :=
  StickyTimeChangeClock.inverseClock κ (mass p) (mass_continuous p)
    (mass_monotone p) (mass_zero p)

theorem inverse_continuous (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) : Continuous (inverse κ p) :=
  StickyTimeChangeClock.inverse_continuous κ _ _ _ _

theorem inverse_coordinate_measurable (κ t : ℝ≥0) :
    Measurable (fun p => inverse κ p t) := by
  apply measurable_of_Iio
  intro b
  have he : {p | inverse κ p t < b} = {p | t < b+κ*mass p b} := by
    ext p
    exact (StickyTimeChangeClock.clockIso κ (mass p) (mass_continuous p)
      (mass_monotone p) (mass_zero p)).symm_apply_lt
  change MeasurableSet {p | inverse κ p t < b}
  rw [he]
  exact measurableSet_lt measurable_const
    (measurable_const.add (measurable_const.mul (mass_coordinate_measurable b)))

def inversePath (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ≥0) :=
  ⟨inverse κ p,inverse_continuous κ p⟩

def stickyPath (κ : ℝ≥0) (p : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  p.comp (inversePath κ p)

theorem stickyPath_measurable (κ : ℝ≥0) : Measurable (stickyPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact continuous_eval.measurable.comp
    (measurable_id.prodMk (inverse_coordinate_measurable κ t))

theorem mass_agrees : ∀ᵐ ω ∂gaussianProduct,
    mass (clockPath ω) = BrownianRandomMassClock.mass ω := by
  filter_upwards [functional_agrees,BrownianMassContinuousLimit.limitPath_properties,
    BrownianMassPathFunctional.mass_agrees] with ω hf hp hm
  funext t
  have hmono : Monotone (functional (clockPath ω)) := by rw [hf]; exact hp.2.1
  simp only [mass,cumulativePath,if_pos hmono,hf,hp.1,sub_zero]
  rw [hm t,hf]

theorem inverse_agrees : ∀ᵐ ω ∂gaussianProduct, ∀ κ : ℝ≥0,
    inverse κ (clockPath ω) = BrownianMassRandomTimeChange.inverse κ ω := by
  filter_upwards [mass_agrees] with ω hm κ
  unfold inverse BrownianMassRandomTimeChange.inverse
  congr 1

theorem stickyPath_agrees : ∀ᵐ ω ∂gaussianProduct, ∀ κ : ℝ≥0,
    stickyPath κ (clockPath ω) = BrownianMassRandomTimeChange.changedPath κ ω := by
  filter_upwards [inverse_agrees] with ω hi κ
  ext t
  change clockPath ω (inverse κ (clockPath ω) t) =
    clockPath ω (BrownianMassRandomTimeChange.inverse κ ω t)
  rw [hi κ]

theorem stickyPath_law (κ : ℝ≥0) :
    (gaussianProduct.map clockPath).map (stickyPath κ) =
      gaussianProduct.map (BrownianMassRandomTimeChange.changedPath κ) := by
  rw [Measure.map_map (stickyPath_measurable κ) clockPath_measurable]
  exact Measure.map_congr (stickyPath_agrees.mono (fun _ h => h κ))

end OperatorDerivativeRewrite.Foundation.StickyWienerPathRealization
