import Foundation.FourCubeHaarHalfDensity
/-! Gauge-invariant boundary scalars are invisible to every normalized interior law,
yet change its actual thermal three-source interaction. Comparison weights only:
the original Wilson action and its nonzero interaction are preserved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeGaugeCalibration
open FourCubeConditionalScore FourCubeHaarContinuousIntegral FourCubeHaarParity
open FourCubeIntegratedCubic QuaternionSU2Representation
open FourCubeThermalMixedDifference (cornerSum)
attribute [local irreducible] FourCubeBoundarySmoothAction.action haarIntegral

def boundaryLoop (b : OneSidedCapComplex.Boundary → SU2) : ℝ :=
  halfTrace (word b chosen*(word b partner)⁻¹)

theorem boundaryLoop_gauge (g : OneSidedCapComplex.FullVertex → SU2)
    (b : OneSidedCapComplex.Boundary → SU2) :
    boundaryLoop (boundaryGauge g b)=boundaryLoop b := pair_trace_gauge g b

def loop (a : Parameters) : ℝ := boundaryLoop (boundaryData (a 0) (a 1) (a 2))

theorem loop_formula (x y z : ℝ) :
    loop ![x,y,z]=Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z := by
  change halfTrace (word (boundaryData x y z) chosen*(word (boundaryData x y z) partner)⁻¹)=_
  rw [word_chosen,word_partner,inv_one,mul_one]
  have h := FourCubeWilsonCubic.triple_action x y z
  rw [SU2JointPlaquetteCubic.action_formula] at h
  linarith

def comparisonWeight (β q : ℝ) (a : Parameters) : Observables :=
  Real.exp (q*β*loop a) • FourCubeConditionalScore.weight β a

def comparisonPartition (β q : ℝ) (a : Parameters) : ℝ := haarIntegral (comparisonWeight β q a)

theorem comparisonPartition_eq (β q : ℝ) (a : Parameters) :
    comparisonPartition β q a=Real.exp (q*β*loop a)*FourCubeBoundarySmoothPartition.partition β a := by
  rw [comparisonPartition,comparisonWeight,map_smul]
  rfl

theorem comparisonPartition_pos (β q : ℝ) (a : Parameters) : 0<comparisonPartition β q a := by
  rw [comparisonPartition_eq]
  exact mul_pos (Real.exp_pos _) (partition_pos β a)

theorem normalized_density_eq (β q : ℝ) (a : Parameters) (s : InteriorState) :
    comparisonWeight β q a s/comparisonPartition β q a=
      (FourCubeHaarHalfDensity.root β a s)^2 := by
  rw [comparisonPartition_eq,comparisonWeight,ContinuousMap.smul_apply,smul_eq_mul,
    FourCubeHaarHalfDensity.root_sq,weight_apply,← FourCubeBoundarySmoothAction.action_apply]
  field_simp [Real.exp_ne_zero,(partition_pos β a).ne']

def comparisonLaw (β q : ℝ) (a : Parameters) : Measure InteriorState :=
  interiorHaar.withDensity (fun s => ENNReal.ofReal (comparisonWeight β q a s/comparisonPartition β q a))

theorem comparisonLaw_eq (β q : ℝ) (a : Parameters) : comparisonLaw β q a=law β a := by
  rw [comparisonLaw,FourCubeHaarHalfDensity.law_root_density]
  congr 1
  funext s
  rw [normalized_density_eq]

def comparisonPotential (β q : ℝ) (a : Parameters) : ℝ := -Real.log (comparisonPartition β q a)

theorem comparisonPotential_eq (β q : ℝ) (a : Parameters) :
    comparisonPotential β q a=potential β a-q*β*loop a := by
  rw [comparisonPotential,comparisonPartition_eq,
    Real.log_mul (Real.exp_ne_zero _) (partition_pos β a).ne',Real.log_exp,potential]
  ring

/-- Reference normalization is retained, so this agrees with the EXISTING
actual normalized free energy when q=0. -/
def coarsePotential (β q x y z : ℝ) : ℝ :=
  comparisonPotential β q ![x,y,z]+Real.log (FourCubePinnedConcentration.normalizer β)

theorem coarsePotential_eq (β q x y z : ℝ) :
    coarsePotential β q x y z=FourCubeThermalMixedDifference.freeEnergy β x y z-
      q*β*loop ![x,y,z] := by
  rw [coarsePotential,comparisonPotential_eq,potential_eq_actual]
  change (FourCubeThermalMixedDifference.freeEnergy β x y z-_
    -q*β*loop ![x,y,z])+_=_
  ring

theorem corner_loop (t : ℝ) :
    cornerSum (fun x y z => loop ![x,y,z]) t= -8*(Real.sin t)^3 := by
  unfold cornerSum
  simp only [loop_formula,Real.cos_neg,Real.sin_neg]
  ring

def thermalResponse (q t : ℝ) : ℝ := cornerSum (coarsePotential (1/t^2) q) t/(8*t)

theorem thermalResponse_eq (q t : ℝ) :
    thermalResponse q t=FourCubeThermalMixedDifference.thermalResponse t+q*(Real.sin t/t)^3 := by
  have he : cornerSum (coarsePotential (1/t^2) q) t=
      cornerSum (FourCubeThermalMixedDifference.freeEnergy (1/t^2)) t-
        q*(1/t^2)*cornerSum (fun x y z => loop ![x,y,z]) t := by
    unfold cornerSum
    simp_rw [coarsePotential_eq]
    ring
  rw [thermalResponse,he,corner_loop,FourCubeThermalMixedDifference.thermalResponse]
  by_cases ht : t=0
  · subst t; simp [cornerSum]
  · field_simp [ht]
    <;> ring

/-- The same conditional family supports ANY prescribed cubic coefficient under
these gauge-invariant boundary comparison factors. This does not change Wilson. -/
theorem thermalResponse_limit (q : ℝ) :
    Tendsto (thermalResponse q) (𝓝[≠] 0) (𝓝 (FourCubeThermalMixedDifference.c+q)) := by
  have hs : Tendsto (fun t : ℝ => Real.sin t/t) (𝓝[≠] 0) (𝓝 1) := by
    simpa [div_eq_mul_inv,mul_comm] using (Real.hasDerivAt_sin (0:ℝ)).tendsto_slope_zero
  have h := FourCubeThermalMixedDifference.actual_thermal_mixed_limit.add ((hs.pow 3).const_mul q)
  simp only [one_pow,mul_one] at h
  apply h.congr'
  filter_upwards with t
  exact (thermalResponse_eq q t).symm

theorem prescribed_limit (L : ℝ) :
    (∀ β a,comparisonLaw β (L-FourCubeThermalMixedDifference.c) a=law β a) ∧
    Tendsto (thermalResponse (L-FourCubeThermalMixedDifference.c)) (𝓝[≠] 0) (𝓝 L) := by
  refine ⟨fun β a => comparisonLaw_eq β _ a,?_⟩
  have h := thermalResponse_limit (L-FourCubeThermalMixedDifference.c)
  have he : FourCubeThermalMixedDifference.c+(L-FourCubeThermalMixedDifference.c)=L := by ring
  rwa [he] at h
end OperatorDerivativeRewrite.Foundation.FourCubeGaugeCalibration
