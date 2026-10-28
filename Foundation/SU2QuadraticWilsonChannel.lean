import Foundation.SU2SharedPlaquetteProjection
/-!
Exact quadratic Wilson convolution and the shared-edge two-plaquette channel.
The twelve conjugations give an exact degree-two identity by centrality;
they do not approximate the increment law. All word layers are integrable.
Spatial weighting, full L2 spectral realization and perturbation closure are
separate obligations; no physical mass-gap conclusion is established here.
-/
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

def rotorRaw (k : Fin 3) : ℍ :=
  ![⟨1,0,0,0⟩,⟨1/2,1/2,1/2,1/2⟩,⟨1/2,-1/2,-1/2,-1/2⟩] k
def axisRaw (j : Fin 4) : ℍ :=
  ![⟨1,0,0,0⟩,⟨0,1,0,0⟩,⟨0,0,1,0⟩,⟨0,0,0,1⟩] j

theorem rotor_unitary (k : Fin 3) : rotorRaw k ∈ unitary ℍ := by
  fin_cases k <;> norm_num [rotorRaw,Unitary.mem_iff,Quaternion.star_mul_self,
    Quaternion.self_mul_star,Quaternion.normSq_def'] <;> rfl
theorem axis_unitary (j : Fin 4) : axisRaw j ∈ unitary ℍ := by
  fin_cases j <;> norm_num [axisRaw,Unitary.mem_iff,Quaternion.star_mul_self,
    Quaternion.self_mul_star,Quaternion.normSq_def'] <;> rfl

def conjugator (k : Fin 3) (j : Fin 4) : QuaternionAngularHaar.Group :=
  ⟨rotorRaw k,rotor_unitary k⟩*⟨axisRaw j,axis_unitary j⟩
def cycleRaw (k : Fin 3) (v : ℍ) : ℍ :=
  ![v,⟨v.re,v.imK,v.imI,v.imJ⟩,⟨v.re,v.imJ,v.imK,v.imI⟩] k
def flipRaw (j : Fin 4) (v : ℍ) : ℍ :=
  ![v,⟨v.re,v.imI,-v.imJ,-v.imK⟩,⟨v.re,-v.imI,v.imJ,-v.imK⟩,⟨v.re,-v.imI,-v.imJ,v.imK⟩] j

theorem rotor_conjugate (k : Fin 3) (v : ℍ) : rotorRaw k*v*star (rotorRaw k)=cycleRaw k v := by
  fin_cases k <;> ext <;> norm_num [rotorRaw,cycleRaw,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

theorem axis_conjugate (j : Fin 4) (v : ℍ) : axisRaw j*v*star (axisRaw j)=flipRaw j v := by
  fin_cases j <;> ext <;> norm_num [axisRaw,flipRaw,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul] <;> ring

theorem conjugator_coordinates (k : Fin 3) (j : Fin 4) (v : ℍ) :
    (conjugator k j : ℍ)*v*star (conjugator k j : ℍ)=cycleRaw k (flipRaw j v) := by
  change (rotorRaw k*axisRaw j)*v*star (rotorRaw k*axisRaw j)=_
  rw [star_mul]
  have he : (rotorRaw k*axisRaw j)*v*(star (axisRaw j)*star (rotorRaw k))=
      rotorRaw k*(axisRaw j*v*star (axisRaw j))*star (rotorRaw k) := by noncomm_ring
  rw [he,axis_conjugate,rotor_conjugate]

theorem cycle_flip_average (k : Fin 3) (c d v : ℍ) :
    (∑ j : Fin 4, (c*cycleRaw k (flipRaw j v)).re*(d*cycleRaw k (flipRaw j v)).re)/4 =
      c.re*d.re*v.re^2+c.imI*d.imI*(cycleRaw k v).imI^2+
        c.imJ*d.imJ*(cycleRaw k v).imJ^2+c.imK*d.imK*(cycleRaw k v).imK^2 := by
  fin_cases k <;> norm_num [cycleRaw,flipRaw,Fin.sum_univ_succ,Quaternion.re_mul] <;> ring

theorem twirl_raw (c d v : ℍ) :
    (∑ k : Fin 3, ∑ j : Fin 4,
      (c*((conjugator k j : ℍ)*v*star (conjugator k j : ℍ))).re*
      (d*((conjugator k j : ℍ)*v*star (conjugator k j : ℍ))).re)/12 =
    c.re*d.re*v.re^2+(c.imI*d.imI+c.imJ*d.imJ+c.imK*d.imK)*(v.imI^2+v.imJ^2+v.imK^2)/3 := by
  simp_rw [conjugator_coordinates]
  have he : (∑ k : Fin 3, ∑ j : Fin 4,
      (c*cycleRaw k (flipRaw j v)).re*(d*cycleRaw k (flipRaw j v)).re)/12 =
      (∑ k : Fin 3, (∑ j : Fin 4,
        (c*cycleRaw k (flipRaw j v)).re*(d*cycleRaw k (flipRaw j v)).re)/4)/3 := by
    rw [← Finset.sum_div]; ring
  rw [he]
  simp_rw [cycle_flip_average]
  norm_num [Fin.sum_univ_succ,cycleRaw]
  ring
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

def pointCoefficient (V : SU2) : ℝ := (4*halfTrace V^2-1)/3

theorem twirl_trace (C D V : SU2) :
    (∑ k : Fin 3, ∑ j : Fin 4,
      halfTrace (C*(hom (conjugator k j)*V*(hom (conjugator k j))⁻¹))*
      halfTrace (D*(hom (conjugator k j)*V*(hom (conjugator k j))⁻¹)))/12 =
    pointCoefficient V*(halfTrace C*halfTrace D)+
      (1-pointCoefficient V)*(halfTrace (C*D⁻¹)/4) := by
  obtain ⟨c,rfl⟩ := hom_surjective C
  obtain ⟨d,rfl⟩ := hom_surjective D
  obtain ⟨v,rfl⟩ := hom_surjective V
  have htrace (a g b : QuaternionAngularHaar.Group) :
      halfTrace (hom a*(hom g*hom b*(hom g)⁻¹)) =
        ((a : ℍ)*((g : ℍ)*(b : ℍ)*star (g : ℍ))).re := by
    rw [← map_inv,← map_mul,← map_mul,← map_mul,halfTrace_map,← Unitary.star_eq_inv]
    rfl
  simp_rw [htrace]
  rw [twirl_raw]
  have hn : (v : ℍ).re^2+(v : ℍ).imI^2+(v : ℍ).imJ^2+(v : ℍ).imK^2=1 := by
    have hh : Quaternion.normSq (v : ℍ)=1 := by
      rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
    simpa [Quaternion.normSq_def',pow_two] using hh
  have ht : halfTrace (hom c*(hom d)⁻¹) = ((c : ℍ)*star (d : ℍ)).re := by
    rw [← map_inv,← map_mul,halfTrace_map,← Unitary.star_eq_inv]
    rfl
  have him : (v : ℍ).imI^2+(v : ℍ).imJ^2+(v : ℍ).imK^2=1-(v : ℍ).re^2 := by linarith [hn]
  rw [him,pointCoefficient,halfTrace_map,halfTrace_map,halfTrace_map,ht]
  simp only [QuaternionAngularHaar.realCoordinate,Quaternion.re_mul,Quaternion.re_star,Quaternion.imI_star,
    Quaternion.imJ_star,Quaternion.imK_star]
  ring
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

def tracePair (C D V : SU2) : ℝ := halfTrace (C*V)*halfTrace (D*V)
def secondMoment (β : ℝ) : ℝ := ∫ V, halfTrace V^2 ∂increment β
def quadraticCoefficient (β : ℝ) : ℝ := (4*secondMoment β-1)/3

theorem tracePair_measurable (C D : SU2) : Measurable (tracePair C D) :=
  (halfTrace_measurable.comp (measurable_const_mul C)).mul
    (halfTrace_measurable.comp (measurable_const_mul D))
theorem tracePair_bound (C D V : SU2) : |tracePair C D V| ≤ 1 := by
  rw [tracePair,abs_mul]
  simpa using mul_le_mul (halfTrace_bound (C*V)) (halfTrace_bound (D*V))
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem increment_conjugation (β : ℝ) (g : SU2) :
    (increment β).map (fun V => g*V*g⁻¹)=increment β :=
  SU2GaugeCovariantTransfer.tilt_conjugation_map g β

private theorem conjugate_pair_integrable (β : ℝ) (C D g : SU2) :
    Integrable (fun V => tracePair C D (g*V*g⁻¹)) (increment β) := by
  letI := increment_probability β
  apply Integrable.of_bound ((tracePair_measurable C D).comp
    ((measurable_mul_const g⁻¹).comp (measurable_const_mul g))).aestronglyMeasurable 1
  filter_upwards with V
  simpa only [Real.norm_eq_abs,Function.comp_apply] using tracePair_bound C D (g*V*g⁻¹)

theorem conjugate_pair_integral (β : ℝ) (C D g : SU2) :
    (∫ V, tracePair C D (g*V*g⁻¹) ∂increment β) = ∫ V, tracePair C D V ∂increment β := by
  have he := integral_map (μ := increment β)
    ((measurable_mul_const g⁻¹).comp (measurable_const_mul g)).aemeasurable
    (tracePair_measurable C D).aestronglyMeasurable
  change (∫ V, tracePair C D V ∂(increment β).map (fun V => g*V*g⁻¹)) =
    (∫ V, tracePair C D (g*V*g⁻¹) ∂increment β) at he
  rw [increment_conjugation] at he
  exact he.symm

private theorem square_integrable (β : ℝ) : Integrable (fun V => halfTrace V^2) (increment β) := by
  letI := increment_probability β
  apply Integrable.of_bound (halfTrace_measurable.pow_const 2).aestronglyMeasurable 1
  filter_upwards with V
  simpa only [Real.norm_eq_abs,abs_pow,sq_abs,one_pow] using
    pow_le_pow_left₀ (abs_nonneg (halfTrace V)) (halfTrace_bound V) 2

theorem pointCoefficient_integral (β : ℝ) :
    (∫ V, pointCoefficient V ∂increment β)=quadraticCoefficient β := by
  letI := increment_probability β
  unfold pointCoefficient
  rw [integral_div]
  have he := integral_sub ((square_integrable β).const_mul 4) (integrable_const (1:ℝ))
  rw [he,integral_const_mul]
  simp [quadraticCoefficient,secondMoment]

theorem bilinear_convolution (β : ℝ) (C D : SU2) :
    (∫ V, tracePair C D V ∂increment β)=
      quadraticCoefficient β*(halfTrace C*halfTrace D)+
      (1-quadraticCoefficient β)*(halfTrace (C*D⁻¹)/4) := by
  letI := increment_probability β
  have hir (k : Fin 3) : Integrable (fun V => ∑ j : Fin 4,
      tracePair C D (hom (conjugator k j)*V*(hom (conjugator k j))⁻¹)) (increment β) :=
    integrable_finsetSum _ (fun j _ => conjugate_pair_integrable β C D (hom (conjugator k j)))
  have hleft : (∫ V, (∑ k : Fin 3, ∑ j : Fin 4,
      tracePair C D (hom (conjugator k j)*V*(hom (conjugator k j))⁻¹))/12 ∂increment β)=
      ∫ V, tracePair C D V ∂increment β := by
    rw [integral_div,integral_finsetSum _ (fun k _ => hir k)]
    simp_rw [integral_finsetSum _ (fun j _ => conjugate_pair_integrable β C D (hom (conjugator _ j))),
      conjugate_pair_integral]
    norm_num
    ring
  have hd : Integrable pointCoefficient (increment β) :=
    (((square_integrable β).const_mul 4).sub (integrable_const 1)).div_const 3
  have hd' : Integrable (fun V => 1-pointCoefficient V) (increment β) := (integrable_const 1).sub hd
  have hmean' : (∫ V, 1-pointCoefficient V ∂increment β)=1-quadraticCoefficient β := by
    have he := integral_sub (integrable_const (1:ℝ)) hd
    simpa only [Pi.sub_apply,integral_const,probReal_univ,one_smul,pointCoefficient_integral] using he
  calc
    _ = ∫ V, (∑ k : Fin 3, ∑ j : Fin 4,
        tracePair C D (hom (conjugator k j)*V*(hom (conjugator k j))⁻¹))/12 ∂increment β := hleft.symm
    _ = ∫ V, pointCoefficient V*(halfTrace C*halfTrace D)+
        (1-pointCoefficient V)*(halfTrace (C*D⁻¹)/4) ∂increment β := by
      apply integral_congr_ae
      filter_upwards with V
      exact twirl_trace C D V
    _ = _ := by
      rw [integral_add (hd.mul_const _) (hd'.mul_const _),integral_mul_const,
        integral_mul_const,pointCoefficient_integral,hmean']
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

theorem sharedProduct_step (β : ℝ) (L R C : SU2) :
    step β (sharedProduct L R) C=quadraticCoefficient β*sharedProduct L R C+
      (1-quadraticCoefficient β)*sharedMean L R := by
  have he : (fun V => sharedProduct L R (C*V))=tracePair (L*C) (R⁻¹*C) := by
    funext V
    have ht : halfTrace ((C*V)⁻¹*R)=halfTrace ((R⁻¹*C)*V) := by
      have hh := halfTrace_inv ((C*V)⁻¹*R)
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh.symm
    simp only [sharedProduct,tracePair,ht,mul_assoc]
  unfold step
  rw [he,bilinear_convolution]
  have hg : (L*C)*(R⁻¹*C)⁻¹=L*R := by group
  have ht : halfTrace (R⁻¹*C)=halfTrace (C⁻¹*R) := by
    simpa only [mul_inv_rev,inv_inv] using halfTrace_inv (C⁻¹*R)
  rw [hg,ht]
  rfl

private theorem sharedIncrement_integrable (β : ℝ) (L R C : SU2) :
    Integrable (fun V => sharedProduct L R (C*V)) (increment β) := by
  letI := increment_probability β
  apply Integrable.of_bound ((sharedProduct_measurable L R).comp
    (measurable_const_mul C)).aestronglyMeasurable 1
  filter_upwards with V
  simpa only [Real.norm_eq_abs,Function.comp_apply] using sharedProduct_bound L R (C*V)

theorem sharedResidual_step (β : ℝ) (L R C : SU2) :
    step β (sharedResidual L R) C=quadraticCoefficient β*sharedResidual L R C := by
  letI := increment_probability β
  change (∫ V, sharedProduct L R (C*V)-sharedMean L R ∂increment β)=_
  rw [integral_sub (sharedIncrement_integrable β L R C) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  change step β (sharedProduct L R) C-sharedMean L R=_
  rw [sharedProduct_step]
  unfold sharedResidual
  ring

def centeredSquare (C : SU2) : ℝ := halfTrace C^2-1/4

theorem centeredSquare_step (β : ℝ) (C : SU2) :
    step β centeredSquare C=quadraticCoefficient β*centeredSquare C := by
  have he : sharedResidual 1 1=centeredSquare := by
    funext V
    simp [sharedResidual,sharedProduct,sharedMean,centeredSquare,halfTrace_inv,
      SU2OpenLinkGaugeObstruction.halfTrace_one,pow_two]
  rw [← he]
  exact sharedResidual_step β 1 1 C

theorem quadraticCoefficient_zero : quadraticCoefficient 0=0 := by
  unfold quadraticCoefficient secondMoment increment
  rw [SU2StapleExtremes.zero_tilt,(SU2TiltEnergyResponse.moment_values law).2.1]
  norm_num

theorem centeredSquare_mean_zero : (∫ C, centeredSquare C ∂law)=0 := by
  unfold centeredSquare
  rw [integral_sub (BoundedExponentialTiltResponse.bounded_power_integrable law halfTrace
    halfTrace_measurable halfTrace_bound 2) (integrable_const _),
    (SU2TiltEnergyResponse.moment_values law).2.1]
  norm_num

theorem centeredSquare_second_moment : (∫ C, centeredSquare C^2 ∂law)=(1/16:ℝ) := by
  have h2 := BoundedExponentialTiltResponse.bounded_power_integrable law halfTrace halfTrace_measurable halfTrace_bound 2
  have h4 := BoundedExponentialTiltResponse.bounded_power_integrable law halfTrace halfTrace_measurable halfTrace_bound 4
  have he : (fun C => centeredSquare C^2) = fun C => (halfTrace C^4-(1/2:ℝ)*halfTrace C^2)+1/16 := by
    funext C; unfold centeredSquare; ring
  have hadd := integral_add (h4.sub (h2.const_mul (1/2))) (integrable_const (1/16:ℝ))
  have hsub := integral_sub h4 (h2.const_mul (1/2))
  simp only [Pi.sub_apply] at hadd hsub
  rw [he,hadd,hsub,integral_const_mul,(SU2TiltEnergyResponse.moment_values law).2.1,
    (SU2TiltEnergyResponse.moment_values law).2.2.2.1]
  norm_num

theorem centeredSquare_conjugate (g C : SU2) : centeredSquare (g*C*g⁻¹)=centeredSquare C := by
  simp only [centeredSquare,halfTrace_conjugate]
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

private theorem traceSandwich_integrable (β : ℝ) (L R : SU2) :
    Integrable (fun V => halfTrace (L*V*R)) (increment β) := by
  letI := increment_probability β
  apply Integrable.of_bound (halfTrace_measurable.comp
    ((measurable_mul_const R).comp (measurable_const_mul L))).aestronglyMeasurable 1
  filter_upwards with V
  simpa only [Real.norm_eq_abs,Function.comp_apply] using halfTrace_bound (L*V*R)

private theorem residualLeft_integrable (β : ℝ) (L A R C : SU2) :
    Integrable (fun V => sharedResidual (L*V*A) R C) (increment β) := by
  have hi := ((traceSandwich_integrable β L (A*C)).mul_const (halfTrace (C⁻¹*R))).sub
    ((traceSandwich_integrable β L (A*R)).div_const 4)
  apply hi.congr
  filter_upwards with V
  simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc,Pi.sub_apply]

private theorem residualRight_integrable (β : ℝ) (L R A C : SU2) :
    Integrable (fun V => sharedResidual L (R*V*A) C) (increment β) := by
  have hi := ((traceSandwich_integrable β (C⁻¹*R) A).const_mul (halfTrace (L*C))).sub
    ((traceSandwich_integrable β (L*R) A).div_const 4)
  apply hi.congr
  filter_upwards with V
  simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc,Pi.sub_apply]

theorem residual_left_average (β : ℝ) (L A R C : SU2) :
    (∫ V, sharedResidual (L*V*A) R C ∂increment β)=coefficient β*sharedResidual (L*A) R C := by
  have he : (fun V => sharedResidual (L*V*A) R C) = fun V =>
      halfTrace (L*V*(A*C))*halfTrace (C⁻¹*R)-halfTrace (L*V*(A*R))/4 := by
    funext V; simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc]
  rw [he,integral_sub ((traceSandwich_integrable β L (A*C)).mul_const _) ((traceSandwich_integrable β L (A*R)).div_const _),
    integral_mul_const,integral_div,trace_sandwich,trace_sandwich]
  simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc]
  ring

theorem residual_right_average (β : ℝ) (L R A C : SU2) :
    (∫ V, sharedResidual L (R*V*A) C ∂increment β)=coefficient β*sharedResidual L (R*A) C := by
  have he : (fun V => sharedResidual L (R*V*A) C) = fun V =>
      halfTrace (L*C)*halfTrace ((C⁻¹*R)*V*A)-halfTrace ((L*R)*V*A)/4 := by
    funext V; simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc]
  rw [he,integral_sub ((traceSandwich_integrable β (C⁻¹*R) A).const_mul _) ((traceSandwich_integrable β (L*R) A).div_const _),
    integral_const_mul,integral_div,trace_sandwich,trace_sandwich]
  simp only [sharedResidual,sharedProduct,sharedMean,mul_assoc]
  ring

def rightWords (β : ℝ) : List SU2 → SU2 → SU2 → SU2 → ℝ
  | [], C, L, R => sharedResidual L R C
  | A::as, C, L, R => ∫ V, rightWords β as C L (R*A*V) ∂increment β

theorem rightWords_exact (β : ℝ) (as : List SU2) (C L R : SU2) :
    rightWords β as C L R=coefficient β^as.length*sharedResidual L (R*as.prod) C := by
  induction as generalizing R with
  | nil => simp [rightWords]
  | cons A as ih =>
    simp only [rightWords,ih,integral_const_mul,List.length_cons,List.prod_cons]
    rw [residual_right_average,pow_succ]
    simp only [mul_assoc]

def residualWords (β : ℝ) : List SU2 → List SU2 → SU2 → SU2 → SU2 → ℝ
  | [], bs, C, L, R => rightWords β bs C L R
  | A::as, bs, C, L, R => ∫ V, residualWords β as bs C (L*A*V) R ∂increment β

theorem residualWords_exact (β : ℝ) (as bs : List SU2) (C L R : SU2) :
    residualWords β as bs C L R=coefficient β^(as.length+bs.length)*
      sharedResidual (L*as.prod) (R*bs.prod) C := by
  induction as generalizing L with
  | nil => simp [residualWords,rightWords_exact]
  | cons A as ih =>
    simp only [residualWords,ih,integral_const_mul,List.length_cons,List.prod_cons]
    rw [residual_left_average,show as.length+1+bs.length=as.length+bs.length+1 by omega,pow_succ]
    simp only [mul_assoc]

theorem rightWords_layer_integrable (β : ℝ) (as : List SU2) (C L R A : SU2) :
    Integrable (fun V => rightWords β as C L (R*A*V)) (increment β) := by
  have hi := (residualRight_integrable β L (R*A) as.prod C).const_mul (coefficient β^as.length)
  simpa only [rightWords_exact] using hi

theorem residualWords_layer_integrable (β : ℝ) (as bs : List SU2) (C L R A : SU2) :
    Integrable (fun V => residualWords β as bs C (L*A*V) R) (increment β) := by
  have hi := (residualLeft_integrable β (L*A) as.prod (R*bs.prod) C).const_mul
    (coefficient β^(as.length+bs.length))
  simpa only [residualWords_exact] using hi

/-- One shared increment is used in BOTH plaquette words; private occurrences are independent. -/
def sharedWordAverage (β : ℝ) (as bs : List SU2) (C : SU2) : ℝ :=
  ∫ V, residualWords β as bs (C*V) 1 1 ∂increment β

theorem sharedWordAverage_exact (β : ℝ) (as bs : List SU2) (C : SU2) :
    sharedWordAverage β as bs C=coefficient β^(as.length+bs.length)*quadraticCoefficient β*
      sharedResidual as.prod bs.prod C := by
  unfold sharedWordAverage
  simp_rw [residualWords_exact,one_mul]
  rw [integral_const_mul]
  change coefficient β^(as.length+bs.length)*step β (sharedResidual as.prod bs.prod) C=_
  rw [sharedResidual_step]
  ring

theorem sharedWordAverage_layer_integrable (β : ℝ) (as bs : List SU2) (C : SU2) :
    Integrable (fun V => residualWords β as bs (C*V) 1 1) (increment β) := by
  letI := increment_probability β
  have hi : Integrable (fun V => sharedResidual as.prod bs.prod (C*V)) (increment β) :=
    (sharedIncrement_integrable β as.prod bs.prod C).sub (integrable_const _)
  simpa only [residualWords_exact,one_mul] using hi.const_mul (coefficient β^(as.length+bs.length))

theorem twoPlaquette_residual_average (β : ℝ) (A B C D E F U : SU2) :
    sharedWordAverage β [A,B,C] [D,E,F] U=
      coefficient β^6*quadraticCoefficient β*sharedResidual (A*B*C) (D*E*F) U := by
  simpa only [List.length_cons,List.length_nil,List.prod_cons,List.prod_nil,mul_one,
    Nat.reduceAdd,mul_assoc] using sharedWordAverage_exact β [A,B,C] [D,E,F] U

theorem outerRectangle_average (β : ℝ) (as bs : List SU2) :
    wordAverage β (as++bs) 1/4=coefficient β^(as.length+bs.length)*sharedMean as.prod bs.prod := by
  rw [wordAverage_exact]
  simp only [List.length_append,List.prod_append,one_mul,sharedMean]
  ring
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

theorem twoPlaquette_residual_gauge (g : Fin 6 → SU2) (A B C D E F U : SU2) :
    sharedResidual ((g 0*A*(g 1)⁻¹)*(g 1*B*(g 2)⁻¹)*(g 2*C*(g 3)⁻¹))
      ((g 3*D*(g 4)⁻¹)*(g 4*E*(g 5)⁻¹)*(g 5*F*(g 0)⁻¹))
      (g 3*U*(g 0)⁻¹)=sharedResidual (A*B*C) (D*E*F) U := by
  have hL : (g 0*A*(g 1)⁻¹)*(g 1*B*(g 2)⁻¹)*(g 2*C*(g 3)⁻¹)=g 0*(A*B*C)*(g 3)⁻¹ := by group
  have hR : (g 3*D*(g 4)⁻¹)*(g 4*E*(g 5)⁻¹)*(g 5*F*(g 0)⁻¹)=g 3*(D*E*F)*(g 0)⁻¹ := by group
  rw [hL,hR,sharedResidual,sharedProduct_gauge,sharedMean_gauge]
  rfl
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation

theorem centeredSquare_memLp : MemLp centeredSquare 2 law := by
  apply MemLp.of_bound ((halfTrace_measurable.pow_const 2).sub measurable_const).aestronglyMeasurable 2
  filter_upwards with C
  change ‖halfTrace C^2-(1/4:ℝ)‖ ≤ 2
  have hs : ‖halfTrace C^2‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs,abs_pow,one_pow] using
      pow_le_pow_left₀ (abs_nonneg (halfTrace C)) (halfTrace_bound C) 2
  calc
    _ ≤ ‖halfTrace C^2‖+‖(1/4:ℝ)‖ := norm_sub_le _ _
    _ ≤ 1+1/4 := add_le_add hs (by norm_num)
    _ ≤ 2 := by norm_num
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel

namespace OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
open QuaternionSU2Representation SU2WilsonConvolution SU2SharedPlaquetteProjection

theorem actual_kernel_centeredSquare (β : ℝ) (C : SU2) :
    (∫ D, centeredSquare D ∂SU2OneWordTransfer.transition law β C⁻¹)=
      quadraticCoefficient β*centeredSquare C := by
  rw [← step_actual_kernel β centeredSquare
    ((halfTrace_measurable.pow_const 2).sub measurable_const) C,centeredSquare_step]

theorem actual_kernel_residual (β : ℝ) (L R C : SU2) :
    (∫ D, sharedResidual L R D ∂SU2OneWordTransfer.transition law β C⁻¹)=
      quadraticCoefficient β*sharedResidual L R C := by
  rw [← step_actual_kernel β (sharedResidual L R)
    ((sharedProduct_measurable L R).sub measurable_const) C,sharedResidual_step]
end OperatorDerivativeRewrite.Foundation.SU2QuadraticWilsonChannel
