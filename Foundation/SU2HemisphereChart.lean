import Foundation.SU2GaussianConeCoordinates
import Foundation.SU2StaplePolar
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Explicit inverse and matrix coordinates for the actual Gaussian/Haar hemisphere chart. -/
noncomputable section
open scoped Quaternion Matrix Matrix.Norms.Operator ENNReal
namespace OperatorDerivativeRewrite.Foundation.SU2HemisphereChart
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2TraceHessianModel

def rawPoint (y : Triple) : ℍ := ⟨1,y 0,y 1,y 2⟩
def radius (y : Triple) : ℝ := Real.sqrt (chartRate y)

theorem radius_positive (y : Triple) : 0 < radius y :=
  Real.sqrt_pos.mpr (chartRate_positive y)

theorem rawPoint_tuple (y : Triple) :
    QuaternionAngularHaar.tuple (rawPoint y)=WithLp.toLp 2 (Fin.cons 1 y : Raw) := by
  ext i
  fin_cases i <;> rfl

theorem chartPoint_norm (y : Triple) :
    ‖WithLp.toLp 2 (Fin.cons 1 y : Raw)‖=radius y := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_succ,chartRate,radius,Real.norm_eq_abs,sq_abs]
  ring

theorem recover_chart (y : Triple) :
    recover (hemisphereChart y : M2)=(radius y)⁻¹ • rawPoint y := by
  have hx : WithLp.toLp 2 (Fin.cons 1 y : Raw) ≠ 0 := by
    intro he
    have hh := congrArg (fun v : GaussianAngularSphere.Space => v 0) he
    norm_num at hh
  change recover (QuaternionSU2Representation.repr (QuaternionAngularHaar.rawDirection (WithLp.toLp 2 (Fin.cons 1 y : Raw))))=_
  rw [recover_repr]
  simp only [QuaternionAngularHaar.rawDirection,if_neg hx,NormedSpace.normalize]
  rw [map_smul,chartPoint_norm]
  rw [← rawPoint_tuple,QuaternionAngularHaar.tuple.symm_apply_apply]


def coordinates (U : SU2) : Triple :=
  ![(recover (U : M2)).imI/(recover (U : M2)).re,
    (recover (U : M2)).imJ/(recover (U : M2)).re,
    (recover (U : M2)).imK/(recover (U : M2)).re]

theorem coordinates_chart (y : Triple) : coordinates (hemisphereChart y)=y := by
  have hn : radius y ≠ 0 := ne_of_gt (radius_positive y)
  unfold coordinates
  rw [recover_chart]
  ext i
  fin_cases i <;> simp [rawPoint,hn,mul_comm,mul_left_comm,mul_assoc]

theorem chart_injective : Function.Injective hemisphereChart :=
  Function.LeftInverse.injective coordinates_chart

theorem chart_halfTrace (y : Triple) : halfTrace (hemisphereChart y)=(radius y)⁻¹ := by
  change traceReal (hemisphereChart y : M2)/2=_
  rw [← repr_recover (hemisphereChart y : M2) (hemisphereChart y).property,repr_halfTrace]
  rw [recover_chart]
  simp [rawPoint]

theorem chart_mem_hemisphere (y : Triple) : hemisphereChart y ∈ hemisphere :=
  by simpa only [hemisphere,Set.mem_setOf_eq,chart_halfTrace] using inv_pos.mpr (radius_positive y)

theorem chart_matrix (y : Triple) :
    (hemisphereChart y : M2)=(radius y)⁻¹ • QuaternionSU2Representation.repr (rawPoint y) := by
  rw [← repr_recover (hemisphereChart y : M2) (hemisphereChart y).property,recover_chart]
  change SU2StaplePolar.reprLinear ((radius y)⁻¹ • rawPoint y)=_
  exact SU2StaplePolar.reprLinear.map_smul _ _

theorem halfTrace_recover (U : SU2) : halfTrace U=(recover (U : M2)).re := by
  change traceReal (U : M2)/2=_
  rw [← repr_recover (U : M2) U.property,repr_halfTrace,recover_repr]

theorem rawPoint_coordinates (U : SU2) (hU : U ∈ hemisphere) :
    rawPoint (coordinates U)=((recover (U : M2)).re)⁻¹ • recover (U : M2) := by
  have hp : 0 < (recover (U : M2)).re := by
    simpa only [hemisphere,Set.mem_setOf_eq,halfTrace_recover] using hU
  have hn := ne_of_gt hp
  apply Quaternion.ext <;> simp [rawPoint,coordinates,hn,div_eq_mul_inv,mul_comm]

theorem chart_coordinates (U : SU2) (hU : U ∈ hemisphere) :
    hemisphereChart (coordinates U)=U := by
  have hp : 0 < (recover (U : M2)).re := by
    simpa only [hemisphere,Set.mem_setOf_eq,halfTrace_recover] using hU
  have hn : ‖recover (U : M2)‖=1 := CStarRing.norm_of_mem_unitary (recover_mem U)
  have hr : radius (coordinates U)=((recover (U : M2)).re)⁻¹ := by
    rw [← chartPoint_norm,← rawPoint_tuple,QuaternionAngularHaar.tuple.norm_map,
      rawPoint_coordinates U hU,norm_smul,hn,mul_one,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp)]
  have he : recover (hemisphereChart (coordinates U) : M2)=recover (U : M2) := by
    rw [recover_chart,hr,rawPoint_coordinates U hU,inv_inv,smul_smul,
      mul_inv_cancel₀ hp.ne',one_smul]
  apply Subtype.ext
  rw [← repr_recover (hemisphereChart (coordinates U) : M2)
    (hemisphereChart (coordinates U)).property,he,repr_recover (U : M2) U.property]

theorem coordinates_measurable : Measurable coordinates := by
  have hm (i j : Fin 2) : Measurable (fun U : SU2 => (U : M2) i j) := by
    have hc : Continuous (fun U : SU2 => (U : M2) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact hc.measurable
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact (Complex.measurable_im.comp (hm 0 0)).div (Complex.measurable_re.comp (hm 0 0))
  · exact (Complex.measurable_re.comp (hm 0 1)).div (Complex.measurable_re.comp (hm 0 0))
  · exact (Complex.measurable_im.comp (hm 0 1)).div (Complex.measurable_re.comp (hm 0 0))

theorem chart_measurable : Measurable hemisphereChart := by
  unfold hemisphereChart
  exact gaussianDirection_measurable.comp (by fun_prop)

theorem lintegral_coordinate_observable (g : Triple → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ U in hemisphere,g (coordinates U) ∂QuaternionSU2Representation.law)=
      ∫⁻ y : Triple,ENNReal.ofReal (chartDensity y)*g y := by
  have hh := lintegral_haar_hemisphere_chart (fun U => g (coordinates U))
    (hg.comp coordinates_measurable)
  simpa only [coordinates_chart] using hh

end OperatorDerivativeRewrite.Foundation.SU2HemisphereChart
