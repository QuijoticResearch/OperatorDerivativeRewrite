import Foundation.PeriodicCubeFiberObstruction
import Foundation.SU2QuaternionOddWord

/-! Actual SU2 conditional covariance for overlapping cube faces. Weighted
quaternion sums retain all cross terms; plaquette defects measure alignment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion Matrix
namespace OperatorDerivativeRewrite.Foundation.PeriodicCubeConditionalGram
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicLinkStaples PeriodicCurvatureVariance PeriodicCubeFiberObstruction
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar incidentFaces

def coordinate (A : SU2) : ℍ := recover (A : SU2TraceHessianModel.M2)

theorem coordinate_norm (A : SU2) : ‖coordinate A‖=1 :=
  CStarRing.norm_of_mem_unitary (recover_mem A)

private theorem coordinate_mul (A B : SU2) : coordinate (A*B)=coordinate A*coordinate B := by
  apply repr_injective
  unfold coordinate
  rw [repr_mul,repr_recover _ A.property,repr_recover _ B.property]
  exact repr_recover _ (A*B).property

private theorem coordinate_inv (A : SU2) : coordinate A⁻¹=star (coordinate A) :=
  SU2QuaternionOddWord.recover_inverse A

def probe (q : ℍ) (A : SU2) : ℝ := (q*coordinate A).re

private theorem coordinate_trace (C : SU2) : halfTrace C=(coordinate C).re :=
  SU2HemisphereChart.halfTrace_recover C

theorem probe_coordinate (C A : SU2) : probe (coordinate C) A=halfTrace (C*A) := by
  rw [SU2HemisphereChart.halfTrace_recover]
  exact congrArg (fun q : ℍ => q.re) (coordinate_mul C A).symm

theorem probe_polar (q : ℍ) (A : SU2) :
    probe q A=‖q‖*halfTrace (SU2StaplePolar.orientation q*A) := by
  have h : probe q A=SU2TraceHessianModel.traceReal
      (QuaternionSU2Representation.repr q*(A : SU2TraceHessianModel.M2))/2 := by
    rw [← repr_recover _ A.property,← repr_mul,repr_halfTrace]
    rfl
  rw [h,SU2StaplePolar.repr_polar,Matrix.smul_mul]
  have ht (c : ℝ) (M : SU2TraceHessianModel.M2) :
      SU2TraceHessianModel.traceReal (c • M)=c*SU2TraceHessianModel.traceReal M := by
    simp [SU2TraceHessianModel.traceReal,Matrix.trace_smul]
  rw [ht]
  change (‖q‖*SU2TraceHessianModel.traceReal ((SU2StaplePolar.orientation q*A : SU2) :
    SU2TraceHessianModel.M2))/2=_
  unfold halfTrace
  ring

theorem probe_add (q r : ℍ) (A : SU2) : probe (q+r) A=probe q A+probe r A := by
  simp only [probe,add_mul,Quaternion.re_add]

theorem probe_smul (c : ℝ) (q : ℍ) (A : SU2) : probe (c • q) A=c*probe q A := by
  simp [probe]

theorem conditional_probe_lower (e : SpatialEdge) (β : ℝ) (hβ : 0≤β)
    (U W : State) (r : PeriodicLinkDisintegration.Rest e) (q : ℍ) :
    ‖q‖^2*(6/(49*(1+6*β)^2)) ≤
      variance (probe q) (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  rw [show probe q=(fun A => ‖q‖*halfTrace (SU2StaplePolar.orientation q*A)) from
    funext (probe_polar q),variance_const_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖q‖)
  have hm : Measurable (fun A : SU2 => halfTrace (SU2StaplePolar.orientation q*A)) :=
    halfTrace_measurable.comp (measurable_const_mul (SU2StaplePolar.orientation q))
  rw [variance_eq_integral hm.aemeasurable]
  exact PeriodicPlaquetteVarianceLower.centered_fiber e β hβ U W r _ _

theorem coordinate_distance (V C : SU2) :
    ‖coordinate C-coordinate V⁻¹‖^2=2*(1-halfTrace (V*C)) := by
  rw [norm_sub_sq_real,coordinate_norm,coordinate_norm,Quaternion.inner_def,
    coordinate_inv,star_star,← coordinate_mul,← coordinate_trace,
    SU2WilsonConvolution.halfTrace_mul_comm]
  ring

private theorem add_square (x y : ℍ) : ‖x+y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := norm_add_le x y
  nlinarith [norm_nonneg x,norm_nonneg y,norm_nonneg (x+y),sq_nonneg (‖x‖-‖y‖)]

private theorem weighted_alignment (x y z : ℍ) (hz : ‖z‖=1) (a b : ℝ) :
    (a+b)^2≤2*‖a • x+b • y‖^2+
      4*a^2*‖x-z‖^2+4*b^2*‖y-z‖^2 := by
  have h := add_square (a • x+b • y) (-(a • (x-z)+b • (y-z)))
  have he : (a • x+b • y)+ -(a • (x-z)+b • (y-z))=(a+b) • z := by module
  rw [he,norm_smul,Real.norm_eq_abs,hz,mul_one,sq_abs,norm_neg] at h
  have h2 := add_square (a • (x-z)) (b • (y-z))
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h2
  nlinarith

/-- The two actual trace coefficients align with the SAME inverse link near
flatness. Orientation signs must not replace this quaternion calculation. -/
theorem two_coefficient_lower (V C D : SU2) (a b : ℝ) :
    (a+b)^2/2-4*a^2*(1-halfTrace (V*C))-4*b^2*(1-halfTrace (V*D)) ≤
      ‖a • coordinate C+b • coordinate D‖^2 := by
  have h := weighted_alignment (coordinate C) (coordinate D) (coordinate V⁻¹)
    (coordinate_norm _) a b
  rw [coordinate_distance,coordinate_distance] at h
  nlinarith

def leftFace : Fin 12 → Fin 6 := ![2,2,3,3,0,0,1,1,0,0,1,1]
def rightFace : Fin 12 → Fin 6 := ![4,5,4,5,4,5,4,5,2,3,2,3]
def leftSlot : Fin 12 → Fin 4 := ![0,2,0,2,0,2,0,2,3,1,3,1]
def rightSlot : Fin 12 → Fin 4 := ![0,0,2,2,3,3,1,1,3,3,1,1]

theorem slots (i : Fin 12) :
    faceEdge (face (leftFace i)) (leftSlot i)=edge i ∧
    faceEdge (face (rightFace i)) (rightSlot i)=edge i ∧ leftFace i≠rightFace i := by
  revert i
  decide +kernel

theorem only_slots (i : Fin 12) (j : Fin 6) (k : Fin 4) :
    faceEdge (face j) k=edge i ↔
      (j=leftFace i ∧ k=leftSlot i) ∨ (j=rightFace i ∧ k=rightSlot i) := by
  revert i j k
  decide +kernel

/-- The exact signless incidence Gram on the actual cube, with its kernel
excluded by an explicit sum-of-squares identity. -/
theorem incidence_identity (a : Fin 6 → ℝ) :
    (∑ i : Fin 12, (a (leftFace i)+a (rightFace i))^2)=
      2*(∑ j : Fin 6, a j^2)+(a 0-a 1)^2+(a 2-a 3)^2+(a 4-a 5)^2+
        (∑ j : Fin 6, a j)^2 := by
  norm_num [leftFace,rightFace,Fin.sum_univ_succ]
  ring

private theorem remainder_trace (V : State) (p : SpatialFace) (k : Fin 4) :
    halfTrace (V (faceEdge p k)*faceRemainder V p k)=plaquette p V := by
  have h := spatial_trace_at_slot V p k (V (faceEdge p k))
  simpa only [Function.update_eq_self,plaquette] using h.symm

def coefficient (a : Fin 6 → ℝ) (V : State) (i : Fin 12) : ℍ :=
  a (leftFace i) • coordinate (faceRemainder V (face (leftFace i)) (leftSlot i))+
    a (rightFace i) • coordinate (faceRemainder V (face (rightFace i)) (rightSlot i))

theorem coefficient_lower (a : Fin 6 → ℝ) (V : State) (i : Fin 12) :
    (a (leftFace i)+a (rightFace i))^2/2-
      4*a (leftFace i)^2*(1-plaquette (face (leftFace i)) V)-
      4*a (rightFace i)^2*(1-plaquette (face (rightFace i)) V) ≤
        ‖coefficient a V i‖^2 := by
  have hl := remainder_trace V (face (leftFace i)) (leftSlot i)
  have hr := remainder_trace V (face (rightFace i)) (rightSlot i)
  rw [(slots i).1] at hl
  rw [(slots i).2.1] at hr
  have h := two_coefficient_lower (V (edge i))
    (faceRemainder V (face (leftFace i)) (leftSlot i))
    (faceRemainder V (face (rightFace i)) (rightSlot i))
    (a (leftFace i)) (a (rightFace i))
  rw [hl,hr] at h
  exact h

private theorem weighted_count (w : Fin 6 → ℝ) :
    (∑ i : Fin 12, (4*w (leftFace i)+4*w (rightFace i)))=16*(∑ j : Fin 6, w j) := by
  norm_num [leftFace,rightFace,Fin.sum_univ_succ]
  ring

/-- Overlap causes a controlled defect error, not independent channels. -/
theorem cube_coefficient_lower (a : Fin 6 → ℝ) (V : State) :
    (∑ j : Fin 6, a j^2)-16*(∑ j : Fin 6, a j^2*(1-plaquette (face j) V)) ≤
      ∑ i : Fin 12, ‖coefficient a V i‖^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => coefficient_lower a V i)
  have he : (∑ i : Fin 12,
      ((a (leftFace i)+a (rightFace i))^2/2-
        4*a (leftFace i)^2*(1-plaquette (face (leftFace i)) V)-
        4*a (rightFace i)^2*(1-plaquette (face (rightFace i)) V)))=
      (∑ i : Fin 12, (a (leftFace i)+a (rightFace i))^2)/2-
        16*(∑ j : Fin 6, a j^2*(1-plaquette (face j) V)) := by
    calc
      _ = ∑ i : Fin 12, ((a (leftFace i)+a (rightFace i))^2/2-
          (4*(a (leftFace i)^2*(1-plaquette (face (leftFace i)) V))+
            4*(a (rightFace i)^2*(1-plaquette (face (rightFace i)) V)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.sum_div,
          weighted_count (fun j => a j^2*(1-plaquette (face j) V))]
  rw [he] at h
  have hg : 2*(∑ j : Fin 6, a j^2)≤
      ∑ i : Fin 12, (a (leftFace i)+a (rightFace i))^2 := by
    rw [incidence_identity]
    nlinarith [sq_nonneg (a 0-a 1),sq_nonneg (a 2-a 3),sq_nonneg (a 4-a 5),
      sq_nonneg (∑ j : Fin 6, a j)]
  linarith

theorem near_flat_coefficient_lower (a : Fin 6 → ℝ) (V : State)
    (hV : ∀ j : Fin 6, 1-plaquette (face j) V≤1/32) :
    (∑ j : Fin 6, a j^2)/2 ≤ ∑ i : Fin 12, ‖coefficient a V i‖^2 := by
  have h := cube_coefficient_lower a V
  have hd : (∑ j : Fin 6, a j^2*(1-plaquette (face j) V)) ≤
      (∑ j : Fin 6, a j^2)/32 := by
    calc
      _ ≤ ∑ j : Fin 6, a j^2*(1/32) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hV j) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring
  linarith

def family (a : Fin 6 → ℝ) (V : State) : ℝ := ∑ j : Fin 6, a j*plaquette (face j) V

theorem family_measurable (a : Fin 6 → ℝ) : Measurable (family a) :=
  Finset.measurable_sum _ (fun j _ => (plaquette_measurable (face j)).const_mul (a j))

theorem family_bound (a : Fin 6 → ℝ) (V : State) : |family a V|≤∑ j : Fin 6, |a j| := by
  calc
    _ ≤ ∑ j : Fin 6, |a j*plaquette (face j) V| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (halfTrace_bound _) (abs_nonneg _)).trans_eq (mul_one _)

theorem family_memLp (a : Fin 6 → ℝ) (μ : Measure State) [IsFiniteMeasure μ] :
    MemLp (family a) 2 μ :=
  MemLp.of_bound (family_measurable a).aestronglyMeasurable _
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using family_bound a V))

theorem family_gauge (a : Fin 6 → ℝ) (g : Gauge) (V : State) :
    family a (PeriodicSlabGauge.gaugeAction g V)=family a V := by
  unfold family plaquette
  simp only [PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]

theorem family_center_even (a : Fin 6 → ℝ) (i : Fin 3) (V : State) :
    family a (PeriodicCenterSeam.flip i V)=family a V := by
  unfold family plaquette
  simp only [PeriodicCenterSeam.spatial_word]

def intercept (a : Fin 6 → ℝ) (V : State) (i : Fin 12) : ℝ :=
  family a V-a (leftFace i)*plaquette (face (leftFace i)) V-
    a (rightFace i)*plaquette (face (rightFace i)) V

private theorem off_incident (i : Fin 12) (j : Fin 6)
    (hL : j≠leftFace i) (hR : j≠rightFace i) : face j∉incidentFaces (edge i) := by
  intro h
  obtain ⟨k,hk⟩ := (mem_incidentFaces (edge i) (face j)).mp h
  rcases (only_slots i j k).mp hk with h | h
  · exact hL h.1
  · exact hR h.1

theorem family_fiber (a : Fin 6 → ℝ) (V : State) (i : Fin 12) (A : SU2) :
    family a (Function.update V (edge i) A)=probe (coefficient a V i) A+intercept a V i := by
  have hLR := (slots i).2.2
  have hl : plaquette (face (leftFace i)) (Function.update V (edge i) A)=
      halfTrace (A*faceRemainder V (face (leftFace i)) (leftSlot i)) := by
    simpa only [plaquette,(slots i).1] using spatial_trace_at_slot V (face (leftFace i)) (leftSlot i) A
  have hr : plaquette (face (rightFace i)) (Function.update V (edge i) A)=
      halfTrace (A*faceRemainder V (face (rightFace i)) (rightSlot i)) := by
    simpa only [plaquette,(slots i).2.1] using spatial_trace_at_slot V (face (rightFace i)) (rightSlot i) A
  have he (j : Fin 6) :
      a j*plaquette (face j) (Function.update V (edge i) A)=a j*plaquette (face j) V+
        (if j=leftFace i then a (leftFace i)*
          (halfTrace (A*faceRemainder V (face (leftFace i)) (leftSlot i))-
            plaquette (face (leftFace i)) V) else 0)+
        (if j=rightFace i then a (rightFace i)*
          (halfTrace (A*faceRemainder V (face (rightFace i)) (rightSlot i))-
            plaquette (face (rightFace i)) V) else 0) := by
    by_cases hL : j=leftFace i
    · subst j
      simp only [hl,ite_true,if_neg hLR]
      ring
    · by_cases hR : j=rightFace i
      · subst j
        simp only [hr,if_neg hL,ite_true,add_zero]
        ring
      · have ho := spatial_word_nonincident V (edge i) (face j) (off_incident i j hL hR) A
        simp only [plaquette,ho,if_neg hL,if_neg hR,add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => he j)
  calc
    _ = family a V+a (leftFace i)*
        (halfTrace (A*faceRemainder V (face (leftFace i)) (leftSlot i))-
          plaquette (face (leftFace i)) V)+a (rightFace i)*
        (halfTrace (A*faceRemainder V (face (rightFace i)) (rightSlot i))-
          plaquette (face (rightFace i)) V) := by
      unfold family
      rw [hs,Finset.sum_add_distrib,Finset.sum_add_distrib]
      simp
    _ = _ := by
      unfold coefficient intercept
      rw [probe_add,probe_smul,probe_smul,probe_coordinate,probe_coordinate,
        SU2WilsonConvolution.halfTrace_mul_comm A,
        SU2WilsonConvolution.halfTrace_mul_comm A]
      ring

theorem probe_measurable (q : ℍ) : Measurable (probe q) := by
  rw [show probe q=(fun A => ‖q‖*halfTrace (SU2StaplePolar.orientation q*A)) from
    funext (probe_polar q)]
  exact (halfTrace_measurable.comp (measurable_const_mul _)).const_mul _

def rowVariance (a : Fin 6 → ℝ) (β : ℝ) (U W V : State) (g h : Gauge)
    (i : Fin 12) : ℝ :=
  variance (fun A => family a (Function.update V (edge i) A))
    (PeriodicLinkDisintegration.conditionalKernel (edge i) β U W
      (((PeriodicLinkDisintegration.split (edge i)) (V,(g,h))).1))

theorem assemble_state (e : SpatialEdge) (V : State) (g h : Gauge) (A : SU2) :
    (PeriodicLinkDisintegration.split e).symm
      ((((PeriodicLinkDisintegration.split e) (V,(g,h))).1),A)=
      (Function.update V e A,(g,h)) := by
  apply (PeriodicLinkDisintegration.split e).injective
  rw [(PeriodicLinkDisintegration.split e).apply_symm_apply,
    PeriodicLinkDisintegration.split_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change V j=Function.update V e A j
      exact (Function.update_of_ne j.property _ _).symm
    · rfl
  · change A=Function.update V e A e
    simp only [Function.update_self]

/-- Literal original normalized centered conditional integral, preserving the
actual rest field and both temporal fields. -/
theorem rowVariance_kernel (a : Fin 6 → ℝ) (β : ℝ) (U W V : State) (g h : Gauge)
    (i : Fin 12) :
    rowVariance a β U W V g h i=
      ∫ A, (family a ((PeriodicLinkDisintegration.split (edge i)).symm
        ((((PeriodicLinkDisintegration.split (edge i)) (V,(g,h))).1),A)).1-
        PeriodicNativeCompression.conditionalMean (edge i) β U W (fun q => family a q.1)
          (((PeriodicLinkDisintegration.split (edge i)) (V,(g,h))).1))^2
      ∂PeriodicLinkDisintegration.conditionalKernel (edge i) β U W
        (((PeriodicLinkDisintegration.split (edge i)) (V,(g,h))).1) := by
  unfold rowVariance PeriodicNativeCompression.conditionalMean
  simp only [assemble_state]
  have hm : Measurable (fun A => family a (Function.update V (edge i) A)) := by
    rw [show (fun A => family a (Function.update V (edge i) A))=
      (fun A => probe (coefficient a V i) A+intercept a V i) from funext (family_fiber a V i)]
    exact (probe_measurable _).add measurable_const
  exact variance_eq_integral hm.aemeasurable

theorem rowVariance_lower (a : Fin 6 → ℝ) (β : ℝ) (hβ : 0≤β)
    (U W V : State) (g h : Gauge) (i : Fin 12) :
    ‖coefficient a V i‖^2*(6/(49*(1+6*β)^2))≤rowVariance a β U W V g h i := by
  letI := PeriodicLinkDisintegration.kernel_markov (edge i) β U W
  unfold rowVariance
  rw [show (fun A => family a (Function.update V (edge i) A))=
      (fun A => probe (coefficient a V i) A+intercept a V i) from funext (family_fiber a V i),
    variance_add_const (probe_measurable _).aestronglyMeasurable]
  exact conditional_probe_lower (edge i) β hβ U W _ _

/-- The full nonlinear Wilson conditional law satisfies a signed-coefficient
cube frame with an explicit LOCAL defect error. No product law is used. -/
theorem cube_row_lower (a : Fin 6 → ℝ) (β : ℝ) (hβ : 0≤β)
    (U W V : State) (g h : Gauge) :
    (6/(49*(1+6*β)^2))*((∑ j : Fin 6, a j^2)-
      16*(∑ j : Fin 6, a j^2*(1-plaquette (face j) V))) ≤
        ∑ i : Fin 12, rowVariance a β U W V g h i := by
  have hc : 0≤6/(49*(1+6*β)^2) := by positivity
  calc
    _ ≤ (6/(49*(1+6*β)^2))*(∑ i : Fin 12, ‖coefficient a V i‖^2) :=
      mul_le_mul_of_nonneg_left (cube_coefficient_lower a V) hc
    _ = ∑ i : Fin 12, ‖coefficient a V i‖^2*(6/(49*(1+6*β)^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => rowVariance_lower a β hβ U W V g h i)

theorem near_flat_row_lower (a : Fin 6 → ℝ) (β : ℝ) (hβ : 0≤β)
    (U W V : State) (g h : Gauge)
    (hV : ∀ j : Fin 6, 1-plaquette (face j) V≤1/32) :
    (6/(49*(1+6*β)^2))*(∑ j : Fin 6, a j^2)/2 ≤
      ∑ i : Fin 12, rowVariance a β U W V g h i := by
  have hc : 0≤6/(49*(1+6*β)^2) := by positivity
  calc
    _ ≤ (6/(49*(1+6*β)^2))*(∑ i : Fin 12, ‖coefficient a V i‖^2) := by
      have h := mul_le_mul_of_nonneg_left (near_flat_coefficient_lower a V hV) hc
      nlinarith
    _ = ∑ i : Fin 12, ‖coefficient a V i‖^2*(6/(49*(1+6*β)^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => rowVariance_lower a β hβ U W V g h i)


end OperatorDerivativeRewrite.Foundation.PeriodicCubeConditionalGram
