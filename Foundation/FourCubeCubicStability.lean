import Foundation.FourCubeReplicatedInteraction
/-! Stability test for the actual quadratic Schur term plus the verified harmonic cubic.
This truncation is a comparison, not the exact compact Wilson action. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix
namespace OperatorDerivativeRewrite.Foundation.FourCubeCubicStability
open FourCubeMovingSchurLimit FourCubeHarmonicAmplitude
open OneSidedSchurForm
attribute [local irreducible] schur boundaryComponent

def quadratic : ℝ := effectiveEnergy 1 1 1/2

theorem quadratic_nonneg : 0≤quadratic := div_nonneg (effectiveEnergy_nonneg 1 1 1) (by norm_num)

theorem effective_diagonal (r : ℝ) : effectiveEnergy r r r=r^2*effectiveEnergy 1 1 1 := by
  have hb (a : Fin 3) : boundaryComponent r r r a=r • boundaryComponent 1 1 1 a := by
    rw [boundary_component_scale]
    fin_cases a <;> rfl
  rw [effectiveEnergy_schur,effectiveEnergy_schur]
  simp_rw [hb,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  simp only [← Finset.mul_sum]
  ring

def truncation (t x y z : ℝ) : ℝ := effectiveEnergy x y z/2+t*FourCubeCubicIntegral.harmonicCubic x y z

theorem truncation_diagonal (t r : ℝ) :
    truncation t r r r=quadratic*r^2+t*FourCubeThermalMixedDifference.c*r^3 := by
  rw [truncation,effective_diagonal,harmonic_amplitudes]
  unfold quadratic FourCubeThermalMixedDifference.c
  ring

/-- The positive thermal direction has a negative far-field ray at EVERY fixed t>0. -/
theorem ray_unbounded_below (t : ℝ) (ht : 0<t) (B : ℝ) :
    ∃ r : ℝ,truncation t r r r<B := by
  let b := t*FourCubeThermalMixedDifference.c
  have hb : 0<b := mul_pos ht FourCubeThermalMixedDifference.c_positive
  let s := 1+(quadratic+|B|+1)/b
  have hsp : 1≤s := by
    have ha := quadratic_nonneg
    have hn : 0≤(quadratic+|B|+1)/b := div_nonneg (by linarith [abs_nonneg B]) hb.le
    dsimp [s]
    linarith
  have hbs : quadratic+|B|+1≤b*s := by
    dsimp [s]
    have he : b*(1+(quadratic+|B|+1)/b)=b+quadratic+|B|+1 := by field_simp; ring
    rw [he]
    linarith
  have hq : quadratic-b*s≤-(|B|+1) := by linarith
  have hss : 1≤s^2 := by nlinarith
  have hv : s^2*(quadratic-b*s)≤-(|B|+1) := by
    calc
      _ ≤ s^2*(-(|B|+1)) := mul_le_mul_of_nonneg_left hq (sq_nonneg s)
      _ ≤ 1*(-(|B|+1)) := mul_le_mul_of_nonpos_right hss (by linarith [abs_nonneg B])
      _ = _ := one_mul _
  refine ⟨-s,?_⟩
  rw [truncation_diagonal]
  change quadratic*(-s)^2+b*(-s)^3<B
  have he : quadratic*(-s)^2+b*(-s)^3=s^2*(quadratic-b*s) := by ring
  rw [he]
  have hB := neg_abs_le B
  linarith

theorem no_global_lower_bound (t : ℝ) (ht : 0<t) :
    ¬ ∃ K : ℝ,∀ x y z : ℝ,K≤truncation t x y z := by
  rintro ⟨K,hK⟩
  obtain ⟨r,hr⟩ := ray_unbounded_below t ht K
  exact (not_lt_of_ge (hK r r r)) hr

/-- This is a pointwise envelope obstruction, not a claim about a measure-zero ray integral. -/
theorem no_gaussian_ray_envelope (t : ℝ) (ht : 0<t) (C α : ℝ) (hC : 0≤C) (hα : 0≤α) :
    ¬ ∀ r : ℝ,Real.exp (-truncation t r r r)≤C*Real.exp (-α*r^2) := by
  intro h
  obtain ⟨r,hr⟩ := ray_unbounded_below t ht (-Real.log (C+1))
  have hp : 0<C+1 := by linarith
  have hg : Real.exp (-α*r^2)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα (sq_nonneg r)])
  have he : C+1<Real.exp (-truncation t r r r) := by
    rw [← Real.exp_log hp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hu := (h r).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg hC)
  linarith

def stabilizedRay (d t r : ℝ) : ℝ := truncation t r r r+d*t^2*r^4

/-- Sharp stability threshold on the actual diagonal for a positive quartic comparison term. -/
theorem quartic_ray_stability (d t : ℝ) (hd : 0<d) (ht : 0<t) :
    (∀ r : ℝ,0≤stabilizedRay d t r) ↔ FourCubeThermalMixedDifference.c^2≤4*quadratic*d := by
  let c := FourCubeThermalMixedDifference.c
  have hc : 0<c := FourCubeThermalMixedDifference.c_positive
  constructor
  · intro h
    let r := -c/(2*d*t)
    have hr : r≠0 := div_ne_zero (neg_ne_zero.mpr hc.ne') (ne_of_gt (by positivity : 0<2*d*t))
    have hh := h r
    rw [stabilizedRay,truncation_diagonal] at hh
    change 0≤quadratic*r^2+t*c*r^3+d*t^2*r^4 at hh
    have he : quadratic*r^2+t*c*r^3+d*t^2*r^4=r^2*(quadratic+t*c*r+d*t^2*r^2) := by ring
    rw [he] at hh
    have hq : 0≤quadratic+t*c*r+d*t^2*r^2 := (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hr)).mp hh
    have heq : 4*d*(quadratic+t*c*r+d*t^2*r^2)=4*quadratic*d-c^2 := by
      dsimp [r]
      field_simp [hd.ne',ht.ne']
      <;> ring
    have hn := mul_nonneg (show 0≤4*d by positivity) hq
    rw [heq] at hn
    change c^2≤4*quadratic*d
    linarith
  · intro h r
    change c^2≤4*quadratic*d at h
    have he : 4*d*(quadratic+t*c*r+d*t^2*r^2)=(2*d*t*r+c)^2+4*quadratic*d-c^2 := by ring
    have hq : 0≤quadratic+t*c*r+d*t^2*r^2 := by
      have hn : 0≤4*d*(quadratic+t*c*r+d*t^2*r^2) := by rw [he]; nlinarith [sq_nonneg (2*d*t*r+c)]
      exact (mul_nonneg_iff_of_pos_left (by positivity : 0<4*d)).mp hn
    rw [stabilizedRay,truncation_diagonal]
    change 0≤quadratic*r^2+t*c*r^3+d*t^2*r^4
    convert mul_nonneg (sq_nonneg r) hq using 1 <;> ring
end OperatorDerivativeRewrite.Foundation.FourCubeCubicStability
