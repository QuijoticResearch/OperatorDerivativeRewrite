import Foundation.CubeChordTransfer
import Foundation.SU2ExponentialMembership
import Foundation.SU2FourWordVariation

/-! Actual second variation of the homogeneous Wilson slab, with both spatial
half weights and the temporal vertex-gauge directions retained. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeSlabSecondVariation
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ExponentialMembership SU2FourWordVariation

abbrev EdgeVelocity := SpatialEdge → Fin 3 → ℝ
abbrev GaugeVelocity := SpatialVertex → Fin 3 → ℝ

def logState (X : EdgeVelocity) (t : ℝ) : State :=
  fun e => ⟨NormedSpace.exp (t • algebraElement (X e)),scaled_algebraElement_exp_mem t (X e)⟩
def logGauge (Z : GaugeVelocity) (t : ℝ) : Gauge :=
  fun v => ⟨NormedSpace.exp (t • algebraElement (Z v)),scaled_algebraElement_exp_mem t (Z v)⟩

def curl (X : EdgeVelocity) (p : SpatialFace) : Fin 3 → ℝ :=
  X (faceEdge p 0)+X (faceEdge p 1)-X (faceEdge p 2)-X (faceEdge p 3)
def gradient (Z : GaugeVelocity) (e : SpatialEdge) : Fin 3 → ℝ :=
  Z (shift e.val.1 e.val.2)-Z e.val.1

def spatialQuadratic (X : EdgeVelocity) : ℝ := ∑ p,lengthSq (curl X p)
def temporalQuadratic (X Y : EdgeVelocity) (Z : GaugeVelocity) : ℝ :=
  ∑ e,lengthSq (X e-Y e+gradient Z e)
def ray (X Y : EdgeVelocity) (Z : GaugeVelocity) (t : ℝ) : ℝ :=
  halfAction (logState X t) (logState Y t) (logGauge Z t)

private abbrev Rows := SpatialFace ⊕ (SpatialFace ⊕ SpatialEdge)
private def vectors (X Y : EdgeVelocity) (Z : GaugeVelocity) : Rows → Fin 4 → Fin 3 → ℝ
  | .inl p => fun i => X (faceEdge p i)
  | .inr (.inl p) => fun i => Y (faceEdge p i)
  | .inr (.inr e) => ![X e,Z (shift e.val.1 e.val.2),Y e,Z e.val.1]
private def rowWeight : Rows → ℝ
  | .inl _ => 1/2
  | .inr (.inl _) => 1/2
  | .inr (.inr _) => 1
private def word (v : Fin 4 → Fin 3 → ℝ) : ℝ → ℝ :=
  action (algebraElement (v 0)) (algebraElement (v 1))
    (-algebraElement (v 2)) (-algebraElement (v 3))
private def slope (v : Fin 4 → Fin 3 → ℝ) : ℝ → ℝ :=
  actionSlope (algebraElement (v 0)) (algebraElement (v 1))
    (-algebraElement (v 2)) (-algebraElement (v 3))

private theorem log_inv (v : Fin 3 → ℝ) (t : ℝ) :
    (⟨NormedSpace.exp (t • algebraElement v),scaled_algebraElement_exp_mem t v⟩ : SU2)⁻¹=
      (⟨NormedSpace.exp (t • (-algebraElement v)),by
        simpa only [neg_smul,smul_neg] using scaled_algebraElement_exp_mem (-t) v⟩ : SU2) := by
  apply Subtype.ext
  change (NormedSpace.exp (t • algebraElement v))ᴴ=_
  rw [← Matrix.exp_conjTranspose]
  simp [Matrix.conjTranspose_smul,algebraElement_skewHermitian]

private theorem word_spatial (X : EdgeVelocity) (p : SpatialFace) (t : ℝ) :
    1-halfTrace (spatialWord (logState X t) p)=word (fun i => X (faceEdge p i)) t := by
  unfold spatialWord logState
  rw [log_inv,log_inv]
  rfl

private theorem word_temporal (X Y : EdgeVelocity) (Z : GaugeVelocity) (e : SpatialEdge) (t : ℝ) :
    1-halfTrace (temporalWord (logState X t) (logState Y t) (logGauge Z t) e)=
      word ![X e,Z (shift e.val.1 e.val.2),Y e,Z e.val.1] t := by
  unfold temporalWord logState logGauge
  rw [log_inv,log_inv]
  rfl

private theorem ray_model (X Y : EdgeVelocity) (Z : GaugeVelocity) :
    ray X Y Z=(fun t => ∑ r : Rows,rowWeight r*word (vectors X Y Z r) t) := by
  funext t
  unfold ray halfAction spatialAction temporalAction
  simp_rw [word_spatial,word_temporal]
  simp only [Fintype.sum_sum_type,vectors,rowWeight,one_mul,← Finset.mul_sum]
  ring

private theorem sum_hasDeriv (X Y : EdgeVelocity) (Z : GaugeVelocity) (t : ℝ) :
    HasDerivAt (fun u => ∑ r : Rows,rowWeight r*word (vectors X Y Z r) u)
      (∑ r : Rows,rowWeight r*slope (vectors X Y Z r) t) t := by
  convert! HasDerivAt.sum (u := Finset.univ)
    (fun r _ => (action_hasDerivAt (algebraElement (vectors X Y Z r 0))
      (algebraElement (vectors X Y Z r 1)) (-algebraElement (vectors X Y Z r 2))
      (-algebraElement (vectors X Y Z r 3)) t).const_mul (rowWeight r)) using 1

/-- Both shared spatial half weights and the actual temporal gauge gradient appear. -/
theorem second_variation (X Y : EdgeVelocity) (Z : GaugeVelocity) :
    deriv (deriv (ray X Y Z)) 0=
      spatialQuadratic X/8+spatialQuadratic Y/8+temporalQuadratic X Y Z/4 := by
  rw [ray_model,show deriv (fun t => ∑ r : Rows,rowWeight r*word (vectors X Y Z r) t)=
    (fun t => ∑ r : Rows,rowWeight r*slope (vectors X Y Z r) t) from
      funext (fun t => (sum_hasDeriv X Y Z t).deriv)]
  have hh := HasDerivAt.sum (u := Finset.univ) (fun r (_ : r ∈ (Finset.univ : Finset Rows)) =>
    (actionSlope_hasDerivAt (algebraElement (vectors X Y Z r 0))
      (algebraElement (vectors X Y Z r 1)) (-algebraElement (vectors X Y Z r 2))
      (-algebraElement (vectors X Y Z r 3)) 0).const_mul (rowWeight r))
  have he : deriv (fun t => ∑ r : Rows,rowWeight r*slope (vectors X Y Z r) t) 0=
      ∑ r : Rows,rowWeight r*(lengthSq (vectors X Y Z r 0+vectors X Y Z r 1-
        vectors X Y Z r 2-vectors X Y Z r 3)/4) := by
    have hd : deriv (fun t => ∑ r : Rows,rowWeight r*slope (vectors X Y Z r) t) 0=
        ∑ r : Rows,rowWeight r*(-traceReal (pathSecond (algebraElement (vectors X Y Z r 0))
          (algebraElement (vectors X Y Z r 1)) (-algebraElement (vectors X Y Z r 2))
          (-algebraElement (vectors X Y Z r 3)) 0)/2) := by
      convert! hh.deriv using 1
    rw [hd]
    simp_rw [signed_slope_second_zero]
  rw [he,Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [vectors,rowWeight,one_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  change (∑ p : SpatialFace,(1/2 : ℝ)*(lengthSq (curl X p)/4))+
    ((∑ p : SpatialFace,(1/2 : ℝ)*(lengthSq (curl Y p)/4))+
      (∑ e : SpatialEdge,lengthSq (X e+Z (shift e.val.1 e.val.2)-Y e-Z e.val.1)/4))=
        spatialQuadratic X/8+spatialQuadratic Y/8+temporalQuadratic X Y Z/4
  have hv (e : SpatialEdge) :
      X e+Z (shift e.val.1 e.val.2)-Y e-Z e.val.1=X e-Y e+(Z (shift e.val.1 e.val.2)-Z e.val.1) := by
    funext a
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  simp_rw [hv]
  simp only [← Finset.mul_sum,← Finset.sum_div]
  change (1/2 : ℝ)*(spatialQuadratic X/4)+(1/2*(spatialQuadratic Y/4)+
    temporalQuadratic X Y Z/4)=_
  ring

/-- Constant vertex velocities are exact gauge zero modes of the temporal Hessian. -/
theorem constant_gradient (c : Fin 3 → ℝ) : gradient (fun _ => c)=0 := by
  funext e a
  simp [gradient]

theorem temporal_constant_shift (X Y : EdgeVelocity) (Z : GaugeVelocity) (c : Fin 3 → ℝ) :
    temporalQuadratic X Y (fun v => Z v+c)=temporalQuadratic X Y Z := by
  unfold temporalQuadratic gradient
  congr 1
  funext e
  congr 1
  funext a
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end OperatorDerivativeRewrite.Foundation.CubeSlabSecondVariation
