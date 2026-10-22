import Foundation.IBMClockInitialEnlargement

/-! A genuine nonzero L2 martingale in the ACTUAL raw natural IBM filtration.
It is the optional projection of the quadratic clock martingale, not of Y_t. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicQuadraticMartingale
open InfiniteGaussian IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMEvenClockProjection IBMClockInitialEnlargement
set_option backward.isDefEq.respectTransparency false

def value (t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ :=
  IBMSourceLaws.jointMeasure[actualQuadratic t | naturalFiltration t]

def valueClass (t : ℝ≥0) : past t :=
  condExpL2 ℝ ℝ (naturalFiltration.le t) (clockQuadratic t)

theorem valueClass_ae (t : ℝ≥0) :
    (valueClass t : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] value t := by
  have hc : (valueClass t : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      IBMSourceLaws.jointMeasure[clockQuadratic t | naturalFiltration t] := by
    simpa only [valueClass, Lp.toLp_coeFn] using (Lp.memLp (clockQuadratic t)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le t)
  have ha : clockQuadratic t =ᵐ[IBMSourceLaws.jointMeasure] actualQuadratic t := clockQuadratic_ae t
  exact hc.trans (condExp_congr_ae ha)

theorem value_memLp (t : ℝ≥0) : MemLp (value t) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (valueClass t : JointL2)).ae_eq (valueClass_ae t)

theorem actual_martingale : Martingale value naturalFiltration IBMSourceLaws.jointMeasure := by
  refine ⟨fun t => stronglyMeasurable_condExp, ?_⟩
  intro s t hst
  calc
    IBMSourceLaws.jointMeasure[value t | naturalFiltration s] =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[actualQuadratic t | naturalFiltration s] :=
      condExp_condExp_of_le (naturalFiltration.mono hst) (naturalFiltration.le t)
    _ =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[IBMSourceLaws.jointMeasure[actualQuadratic t | enlargement s] |
          naturalFiltration s] :=
      (condExp_condExp_of_le (natural_le_enlargement s) (enlargement.le s)).symm
    _ =ᵐ[IBMSourceLaws.jointMeasure] value s :=
      condExp_congr_ae (actualQuadratic_martingale.condExp_ae_eq hst)

theorem value_nonzero (t : ℝ≥0) (ht : 0 < t) :
    ¬ value t =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  intro hz
  apply conditional_quadratic_ne_zero t t ht le_rfl
  apply Lp.ext
  exact (valueClass_ae t).trans (hz.trans (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure).symm)

theorem value_zero : value 0 =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (0 : ℝ) := by
  have hn : ‖clockQuadratic 0‖ ^ 2 = 0 := by
    change ‖IBMClockConditionalCorrection.clockLift (GaussianTimeSpaceHermite.brownianCore 0 2 : GaussianL2)‖ ^ 2 = 0
    rw [IBMClockConditionalCorrection.clockLift.norm_map, GaussianTimeSpaceHermite.brownianCore_norm_sq]
    norm_num
  have hz : clockQuadratic 0 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have he := valueClass_ae 0
  change (condExpL2 ℝ ℝ (naturalFiltration.le 0) (clockQuadratic 0) : JointL2) =ᵐ[_] value 0 at he
  rw [hz, map_zero] at he
  exact he.symm.trans (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure)

theorem valueClass_bound_sq (t : ℝ≥0) : ‖valueClass t‖ ^ 2 ≤ 2 * (t : ℝ) ^ 2 := by
  have hb := norm_condExpL2_le (𝕜 := ℝ) (naturalFiltration.le t) (clockQuadratic t)
  have hn : ‖clockQuadratic t‖ ^ 2 = 2 * (t : ℝ) ^ 2 := by
    change ‖IBMClockConditionalCorrection.clockLift (GaussianTimeSpaceHermite.brownianCore t 2 : GaussianL2)‖ ^ 2 = _
    rw [IBMClockConditionalCorrection.clockLift.norm_map, GaussianTimeSpaceHermite.brownianCore_norm_sq]
    norm_num
  change ‖valueClass t‖ ≤ ‖clockQuadratic t‖ at hb
  nlinarith [norm_nonneg (valueClass t), norm_nonneg (clockQuadratic t)]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicQuadraticMartingale
