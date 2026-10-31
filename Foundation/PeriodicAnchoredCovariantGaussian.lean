import Foundation.PeriodicTemporalQuadratic
import Foundation.PeriodicRelativeGaugeGaussian
/-! Uniform anchored covariant coercivity on the ACTUAL192-link spatial
lattice, for arbitrary SU(2) link backgrounds. The existing63-relative-vertex
field carries a genuine positive finite affine Lebesgue Gaussian, an integrable
majorant and exact anchored gauge-translation invariance. For constant flat
backgrounds its integrand matches the verified pointwise Wilson scaling limit.
No exchange with nonlinear Haar integration, determinant formula, stationary
spectral limit or physical mass gap is asserted. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicAnchoredCovariantGaussian
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets SU2RootAdjoint
open PeriodicTemporalSlab PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian

def connectionGradient (U : State) (Z : SpatialVertex → Triple) (e : SpatialEdge) : Triple :=
  Z e.1-rotate (U e) (Z (shift e.1 e.2))
def connectionEnergy (U : State) (Z : SpatialVertex → Triple) : ℝ :=
  ∑ e : SpatialEdge,sizeSq (connectionGradient U Z e)
def relativeEnergy (U : State) (Z : Field) : ℝ := connectionEnergy U (velocity Z)

private theorem sizeSq_difference_bound (a b : Triple) :
    sizeSq b≤2*sizeSq (a-b)+2*sizeSq a := by
  unfold sizeSq
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (2*a 0-b 0),sq_nonneg (2*a 1-b 1),sq_nonneg (2*a 2-b 2)]

theorem connectionEnergy_nonneg (U : State) (Z : SpatialVertex → Triple) : 0≤connectionEnergy U Z :=
  Finset.sum_nonneg (fun e _ => sizeSq_nonneg (connectionGradient U Z e))

theorem point_bound (U : State) (Z : SpatialVertex → Triple) (hZ : Z root=0) (v : SpatialVertex) :
    sizeSq (Z v)≤((2 : ℝ)^(depth v+1)-2)*connectionEnergy U Z := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      rw [← hn]
      simp [hZ,depth,root,sizeSq]
    · have hd := parent_depth v hv
      have hprev := ih (depth (parent v)) (by omega) (parent v) rfl
      have hstep := sizeSq_difference_bound (Z (parent v))
        (rotate (U (parent v,axis v)) (Z v))
      rw [rotate_sizeSq] at hstep
      have he : sizeSq (Z (parent v)-rotate (U (parent v,axis v)) (Z v))≤connectionEnergy U Z := by
        have hh := Finset.single_le_sum (fun e (_ : e∈Finset.univ) =>
          sizeSq_nonneg (connectionGradient U Z e)) (Finset.mem_univ (parent v,axis v))
        simpa only [connectionEnergy,connectionGradient,parent_shift v hv] using hh
      have hp : (2 : ℝ)^(depth v+1)-2=
          2+2*((2 : ℝ)^(depth (parent v)+1)-2) := by
        rw [← hd,pow_succ]
        ring
      rw [← hn,hp]
      nlinarith

theorem uniform_point_bound (U : State) (Z : SpatialVertex → Triple) (hZ : Z root=0)
    (v : SpatialVertex) : sizeSq (Z v)≤1022*connectionEnergy U Z := by
  have h := point_bound U Z hZ v
  have hp : (2 : ℝ)^(depth v+1)≤2^10 :=
    pow_le_pow_right₀ (by norm_num) (by have hd := depth_le v; omega)
  have he := connectionEnergy_nonneg U Z
  nlinarith

theorem relative_coercive (U : State) (Z : Field) :
    fieldSizeSq Z≤64386*relativeEnergy U Z := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (v : RelFieldIndex) _ => uniform_point_bound U (velocity Z) (velocity_root Z) v.val)
  simp only [velocity_rel,Finset.sum_const,Finset.card_univ,rel_count,nsmul_eq_mul] at h
  unfold fieldSizeSq relativeEnergy
  norm_num at h
  linarith

def rate : ℝ := 1/64386

theorem rate_pos : 0<rate := by norm_num [rate]
theorem relative_lower (U : State) (Z : Field) : rate*fieldSizeSq Z≤relativeEnergy U Z := by
  have h := relative_coercive U Z
  unfold rate
  linarith

theorem relative_zero_iff (U : State) (Z : Field) : relativeEnergy U Z=0 ↔ Z=0 := by
  constructor
  · intro he
    have hb := relative_coercive U Z
    have hz (v : RelFieldIndex) : sizeSq (Z v)=0 := by
      have hh := Finset.single_le_sum (fun w (_ : w∈Finset.univ) => sizeSq_nonneg (Z w)) (Finset.mem_univ v)
      change sizeSq (Z v)≤fieldSizeSq Z at hh
      exact le_antisymm (by linarith) (sizeSq_nonneg _)
    funext v i
    have hs := hz v
    unfold sizeSq at hs
    have h0 : (Z v 0)^2=0 := by nlinarith [sq_nonneg (Z v 1),sq_nonneg (Z v 2)]
    have h1 : (Z v 1)^2=0 := by nlinarith [sq_nonneg (Z v 0),sq_nonneg (Z v 2)]
    have h2 : (Z v 2)^2=0 := by nlinarith [sq_nonneg (Z v 0),sq_nonneg (Z v 1)]
    fin_cases i
    · exact sq_eq_zero_iff.mp h0
    · exact sq_eq_zero_iff.mp h1
    · exact sq_eq_zero_iff.mp h2
  · rintro rfl
    have hv : velocity (0 : Field)=0 := by funext v; simp [velocity]
    simp [relativeEnergy,connectionEnergy,connectionGradient,hv,PeriodicRelativeGaugeGaussian.rotate_zero,sizeSq]

def boundarySize (B : SpatialEdge → Triple) : ℝ := ∑ e,sizeSq (B e)
def affineEnergy (U : State) (B : SpatialEdge → Triple) (Z : Field) : ℝ :=
  (∑ e : SpatialEdge,sizeSq (B e-connectionGradient U (velocity Z) e))/2

theorem affine_lower (U : State) (B : SpatialEdge → Triple) (Z : Field) :
    relativeEnergy U Z/4-boundarySize B/2≤affineEnergy U B Z := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => sizeSq_difference_bound (B e) (connectionGradient U (velocity Z) e))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  unfold relativeEnergy connectionEnergy boundarySize affineEnergy
  linarith only [h]

theorem gaussian_bound (U : State) (B : SpatialEdge → Triple) (Z : Field) :
    Real.exp (-affineEnergy U B Z)≤
      Real.exp (boundarySize B/2)*Real.exp (-(rate/4)*fieldSizeSq Z) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := affine_lower U B Z
  have hc := relative_lower U Z
  linarith

private theorem rotate_continuous (c : SU2) : Continuous (rotate c) := by
  let L : Triple →ₗ[ℝ] Triple :=
    { toFun := rotate c
      map_add' := rotate_add c
      map_smul' := by intro a u; exact rotate_smul c a u }
  exact L.continuous_of_finiteDimensional

theorem affineEnergy_continuous (U : State) (B : SpatialEdge → Triple) :
    Continuous (affineEnergy U B) := by
  have hg (e : SpatialEdge) : Continuous (fun Z : Field => B e-connectionGradient U (velocity Z) e) := by
    exact continuous_const.sub ((velocity_continuous e.1).sub
      ((rotate_continuous (U e)).comp (velocity_continuous (shift e.1 e.2))))
  have hs (e : SpatialEdge) : Continuous (fun Z : Field => sizeSq (B e-connectionGradient U (velocity Z) e)) := by
    unfold sizeSq
    exact (((continuous_apply 0).comp (hg e)).pow 2 |>.add
      (((continuous_apply 1).comp (hg e)).pow 2)).add (((continuous_apply 2).comp (hg e)).pow 2)
  exact (continuous_finsetSum Finset.univ (fun e _ => hs e)).div_const 2

theorem affineGaussian_integrable (U : State) (B : SpatialEdge → Triple) :
    Integrable (fun Z : Field => Real.exp (-affineEnergy U B Z)) := by
  have hi := (fieldGaussian_integrable (rate/4) (by have hr := rate_pos; positivity : 0<rate/4)).const_mul (Real.exp (boundarySize B/2))
  apply hi.mono' (Real.continuous_exp.comp (affineEnergy_continuous U B).neg).aestronglyMeasurable
  filter_upwards [] with Z
  change ‖Real.exp (-affineEnergy U B Z)‖≤_
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact gaussian_bound U B Z

def gaussianMass (U : State) (B : SpatialEdge → Triple) : ℝ :=
  ∫ Z : Field,Real.exp (-affineEnergy U B Z)

theorem gaussianMass_pos (U : State) (B : SpatialEdge → Triple) : 0<gaussianMass U B :=
  integral_exp_pos (affineGaussian_integrable U B)

theorem gaussianMass_upper (U : State) (B : SpatialEdge → Triple) :
    gaussianMass U B≤Real.exp (boundarySize B/2)*
      ∫ Z : Field,Real.exp (-(rate/4)*fieldSizeSq Z) := by
  have hi := (fieldGaussian_integrable (rate/4) (by have hr := rate_pos; positivity : 0<rate/4)).const_mul (Real.exp (boundarySize B/2))
  have h := integral_mono (affineGaussian_integrable U B) hi (gaussian_bound U B)
  simpa only [integral_const_mul,gaussianMass] using h

open PeriodicFlatBackgroundHessian PeriodicTemporalQuadratic

theorem affine_temporal (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) :
    affineEnergy (fun e => h e.2) (fun e => X e-Y e) Z=
      temporalEnergy h X Y (velocity Z)/2 := rfl

def normalWeight (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) : ℝ :=
  Real.exp (-((quadratic h X/2+temporalEnergy h X Y (velocity Z)+quadratic h Y/2)/2))

theorem normalWeight_factor (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) :
    normalWeight h X Y Z=Real.exp (-quadratic h X/4-quadratic h Y/4)*
      Real.exp (-affineEnergy (fun e => h e.2) (fun e => X e-Y e) Z) := by
  rw [← Real.exp_add,affine_temporal]
  unfold normalWeight
  apply congrArg Real.exp
  ring

theorem normalWeight_integrable (h : Fin 3 → SU2) (X Y : Velocity) :
    Integrable (normalWeight h X Y) := by
  have hf : normalWeight h X Y=(fun Z : Field => Real.exp (-quadratic h X/4-quadratic h Y/4)*
      Real.exp (-affineEnergy (fun e => h e.2) (fun e => X e-Y e) Z)) := funext (normalWeight_factor h X Y)
  rw [hf]
  exact (affineGaussian_integrable _ _).const_mul _

theorem normal_integral_factor (h : Fin 3 → SU2) (X Y : Velocity) :
    (∫ Z : Field,normalWeight h X Y Z)=Real.exp (-quadratic h X/4-quadratic h Y/4)*
      gaussianMass (fun e => h e.2) (fun e => X e-Y e) := by
  simp_rw [normalWeight_factor]
  rw [integral_const_mul]
  rfl

theorem normal_integral_pos (h : Fin 3 → SU2) (X Y : Velocity) :
    0<∫ Z : Field,normalWeight h X Y Z := by
  rw [normal_integral_factor]
  exact mul_pos (Real.exp_pos _) (gaussianMass_pos _ _)

theorem normalWeight_bound (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) :
    normalWeight h X Y Z≤Real.exp (boundarySize (fun e => X e-Y e)/2)*
      Real.exp (-(rate/4)*fieldSizeSq Z) := by
  rw [normalWeight_factor]
  have hx : 0≤quadratic h X := Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _)
  have hy : 0≤quadratic h Y := Finset.sum_nonneg (fun _ _ => sizeSq_nonneg _)
  have he : Real.exp (-quadratic h X/4-quadratic h Y/4)≤1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  exact (mul_le_of_le_one_left (le_of_lt (Real.exp_pos _)) he).trans (gaussian_bound _ _ _)

private theorem velocity_sub (Z W : Field) : velocity (Z-W)=velocity Z-velocity W := by
  funext v
  by_cases hv : v=root <;> simp [velocity,hv]
private theorem relativeGradient_sub (U : State) (Z W : Field) (e : SpatialEdge) :
    connectionGradient U (velocity (Z-W)) e=
      connectionGradient U (velocity Z) e-connectionGradient U (velocity W) e := by
  rw [velocity_sub]
  simp only [connectionGradient,Pi.sub_apply,rotate_sub]
  abel

theorem affine_boundary_gauge (U : State) (B : SpatialEdge → Triple) (W Z : Field) :
    affineEnergy U (fun e => B e+connectionGradient U (velocity W) e) Z=
      affineEnergy U B (Z-W) := by
  unfold affineEnergy
  apply congrArg (fun x : ℝ => x/2)
  apply Finset.sum_congr rfl
  intro e _
  rw [relativeGradient_sub]
  apply congrArg sizeSq
  ext i
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem gaussianMass_gauge (U : State) (B : SpatialEdge → Triple) (W : Field) :
    gaussianMass U (fun e => B e+connectionGradient U (velocity W) e)=gaussianMass U B := by
  unfold gaussianMass
  simp_rw [affine_boundary_gauge]
  exact integral_sub_right_eq_self (fun Z : Field => Real.exp (-affineEnergy U B Z)) W

open Filter
open scoped Topology

theorem normalWeight_pointwise (h : Fin 3 → SU2) (X Y : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) (Z : Field) :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.weight (1/t^2) (state h X t) (state h Y t)
      (temporalGauge (velocity Z) t)) (𝓝[≠] 0) (𝓝 (normalWeight h X Y Z)) :=
  weight_scaled_limit h X Y (velocity Z) hc

end OperatorDerivativeRewrite.Foundation.PeriodicAnchoredCovariantGaussian
