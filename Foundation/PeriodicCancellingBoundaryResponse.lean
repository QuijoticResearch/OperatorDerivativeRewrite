import Foundation.PeriodicLinkDisintegration
import Foundation.SU2AxisMatrixJets
import Foundation.SU2OneWordTransfer
/-! An actual rough spatial exterior with cancelling six staples. No statement
about typical exteriors, full block averages or a physical mass gap is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicCancellingBoundaryResponse
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
open SU2TraceHessianModel SU2StapleExtremes

def edge : SpatialEdge := (fun _ => 0,0)
def minusFace (back : Bool) : SpatialFace :=
  ⟨((fun j => if back ∧ j=1 then 3 else 0),(0,1)),by change (0:Fin 3)<1; decide⟩
def plusFace (back : Bool) : SpatialFace :=
  ⟨((fun j => if back ∧ j=2 then 3 else 0),(0,2)),by change (0:Fin 3)<2; decide⟩

def flux (e : SpatialEdge) : SU2 := if e.2=1 ∧ e.1 0=1 then minusOne else 1

theorem incident_exact : incidentFaces edge =
    {minusFace false,minusFace true,plusFace false,plusFace true} := by
  decide +kernel

private theorem slot_minus (b : Bool) : faceEdge (minusFace b) (if b then 2 else 0)=edge := by
  cases b <;> decide +kernel
private theorem slot_plus (b : Bool) : faceEdge (plusFace b) (if b then 2 else 0)=edge := by
  cases b <;> decide +kernel

private theorem staple_at (V : State) (e : SpatialEdge) (p : SpatialFace) (k : Fin 4)
    (h : faceEdge p k = e) : spatialStaple V e p=faceRemainder V p k := by
  have hx : ∃ j,faceEdge p j=e := ⟨k,h⟩
  have he : Classical.choose hx=k := faceEdge_injective p ((Classical.choose_spec hx).trans h.symm)
  simp only [spatialStaple,dite_eq_left hx,he]

private theorem minus_inv : minusOne⁻¹=minusOne := by
  apply Subtype.ext
  change (QuaternionSU2Representation.repr (-1 : ℍ))ᴴ=QuaternionSU2Representation.repr (-1 : ℍ)
  rw [← QuaternionSU2Representation.repr_star]
  simp

theorem spatial_minus (b : Bool) : spatialStaple flux edge (minusFace b)=minusOne := by
  rw [staple_at _ _ _ _ (slot_minus b)]
  have hz : (0:ZMod 4) ≠ 1 := by decide
  cases b <;> norm_num [faceRemainder,faceEdge,minusFace,flux,shift,minus_inv,hz]

theorem spatial_plus (b : Bool) : spatialStaple flux edge (plusFace b)=1 := by
  rw [staple_at _ _ _ _ (slot_plus b)]
  have hz : (0:ZMod 4) ≠ 1 := by decide
  cases b <;> norm_num [faceRemainder,faceEdge,plusFace,flux,shift,hz]

theorem spatial_change_zero (A : SU2) :
    spatialAction (Function.update flux edge A)=spatialAction (Function.update flux edge 1) := by
  have hs := spatial_action_change flux edge A
  rw [incident_exact] at hs
  have h01 : minusFace false ≠ minusFace true := by decide +kernel
  have h02 : minusFace false ≠ plusFace false := by decide +kernel
  have h03 : minusFace false ≠ plusFace true := by decide +kernel
  have h12 : minusFace true ≠ plusFace false := by decide +kernel
  have h13 : minusFace true ≠ plusFace true := by decide +kernel
  have h23 : plusFace false ≠ plusFace true := by decide +kernel
  simp [h01,h02,h03,h12,h13,h23,spatial_minus,spatial_plus,
    SU2WilsonConvolution.halfTrace_mul_comm A minusOne,
    SU2StrongCouplingCovariance.halfTrace_center_neg,
    SU2OpenLinkGaugeObstruction.halfTrace_minusOne,
    SU2OpenLinkGaugeObstruction.halfTrace_one] at hs
  linarith


attribute [local irreducible] edge flux minusFace plusFace spatialWord spatialStaple

def upper (h : ℝ) : State := fun _ => SU2JointPlaquetteCubic.axis 0 (Real.pi/2-h)
def lower (h : ℝ) : State := fun _ => SU2JointPlaquetteCubic.axis 0 (-(Real.pi/2-h))

private theorem inverse_axis_trace (A : SU2) (θ : ℝ) :
    halfTrace (A*SU2JointPlaquetteCubic.axis 0 θ)+
      halfTrace (A*SU2JointPlaquetteCubic.axis 0 (-θ))=2*Real.cos θ*halfTrace A := by
  simp only [halfTrace,Submonoid.coe_mul,SU2AxisMatrixJets.axis_matrix_formula,
    Real.cos_neg,Real.sin_neg,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one,
    traceReal,Matrix.trace_add,Matrix.trace_smul]
  simp only [Complex.add_re,Complex.smul_re,smul_eq_mul]
  ring

theorem temporal_pair_trace (h : ℝ) (A : SU2) :
    halfTrace (A*leftTemporal (upper h) 1 edge)+
      halfTrace (A*rightTemporal (lower h) 1 edge)=2*Real.sin h*halfTrace A := by
  simp only [leftTemporal,rightTemporal,upper,lower,Pi.one_apply,one_mul,mul_one,inv_one,
    SU2AxisMatrixJets.axis_inv,neg_neg]
  rw [add_comm,inverse_axis_trace,Real.cos_pi_div_two_sub]

theorem central_change (h : ℝ) (A : SU2) :
    PeriodicAugmentedBridge.centralAction (upper h) (lower h)
      (Function.update flux edge A,(1,1)) -
      PeriodicAugmentedBridge.centralAction (upper h) (lower h) (Function.update flux edge 1,(1,1)) =
        2*Real.sin h*(1-halfTrace A) := by
  have hl := temporal_action_change_left (upper h) flux 1 edge A
  have hr := temporal_action_change_right flux (lower h) 1 edge A
  have ht := temporal_pair_trace h A
  have h1 := temporal_pair_trace h 1
  simp only [one_mul,SU2OpenLinkGaugeObstruction.halfTrace_one] at h1
  unfold PeriodicAugmentedBridge.centralAction
  dsimp only
  rw [spatial_change_zero]
  linarith

def prefactor (β h : ℝ) : ℝ := localDensity β (upper h) flux (lower h) 1 1 edge 1 *
  Real.exp (-(2*β*Real.sin h))

theorem prefactor_positive (β h : ℝ) : 0<prefactor β h :=
  mul_pos (PeriodicAugmentedBridge.density_pos _ _ _ _) (Real.exp_pos _)

theorem density_factor (β h : ℝ) (A : SU2) :
    localDensity β (upper h) flux (lower h) 1 1 edge A =
      prefactor β h*Real.exp ((2*β*Real.sin h)*halfTrace A) := by
  have hc := central_change h A
  unfold prefactor localDensity
  rw [PeriodicAugmentedBridge.density_phase,PeriodicAugmentedBridge.density_phase]
  have he : -β*PeriodicAugmentedBridge.centralAction (upper h) (lower h)
      (Function.update flux edge A,(1,1)) =
      -β*PeriodicAugmentedBridge.centralAction (upper h) (lower h)
        (Function.update flux edge 1,(1,1)) -(2*β*Real.sin h)+
          (2*β*Real.sin h)*halfTrace A := by
    linear_combination -β*hc
  rw [he,Real.exp_add,Real.exp_sub]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]


def responseLaw (β h : ℝ) : Measure SU2 :=
  linkLaw β (upper h) flux (lower h) 1 1 edge

theorem law_eq_tilt (β h : ℝ) : responseLaw β h =
    BoundedExponentialTiltResponse.tiltedMeasure law halfTrace (2*β*Real.sin h) := by
  have hi : (∫ A,localDensity β (upper h) flux (lower h) 1 1 edge A ∂law)=
      prefactor β h*BoundedExponentialTiltResponse.partition law halfTrace (2*β*Real.sin h) := by
    simp_rw [density_factor]
    rw [integral_const_mul]
    simp only [BoundedExponentialTiltResponse.partition,
      BoundedExponentialTiltResponse.weighted,one_mul]
  unfold responseLaw linkLaw BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext A
  rw [density_factor,hi]
  unfold BoundedExponentialTiltResponse.density
  congr 1
  exact mul_div_mul_left _ _ (prefactor_positive β h).ne'

theorem cancellation_law (β : ℝ) : responseLaw β 0=law := by
  rw [law_eq_tilt]
  simp only [Real.sin_zero,mul_zero]
  exact SU2StapleExtremes.zero_tilt _ _

/-- This is the trace of a complete actual spatial plaquette. -/
def observable (V : State) : ℝ := halfTrace (spatialWord V (plusFace false))

theorem observable_section (A : SU2) : observable (Function.update flux edge A)=halfTrace A := by
  have hz : (1:ZMod 4) ≠ 0 := by decide
  norm_num [observable,spatialWord,plusFace,edge,flux,shift,Function.update_apply,
    Prod.mk.injEq,funext_iff,Fin.forall_fin_succ,hz]

theorem observable_gauge (g : Gauge) (V : State) :
    observable (PeriodicSlabGauge.gaugeAction g V)=observable V := by
  unfold observable
  rw [PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]


/-- Every bounded measurable observable has its actual boundary derivative. -/
theorem expectation_derivative (β : ℝ) (f : SU2 → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hfb : ∀ A, |f A| ≤ M) :
    HasDerivAt (fun h => ∫ A,f A ∂responseLaw β h)
      (2*β*(∫ A,f A*halfTrace A ∂law)) 0 := by
  have hd := BoundedExponentialTiltResponse.expectation_hasDerivAt_zero law
    halfTrace f halfTrace_measurable hf halfTrace_bound M hM hfb
  rw [(SU2TiltEnergyResponse.moment_values law).1,mul_zero,sub_zero] at hd
  have ht : HasDerivAt (fun h : ℝ => 2*β*Real.sin h) (2*β) 0 := by
    simpa using (Real.hasDerivAt_sin 0).const_mul (2*β)
  have hd0 : HasDerivAt (BoundedExponentialTiltResponse.expectation law halfTrace f)
      (∫ A,f A*halfTrace A ∂law) (2*β*Real.sin 0) := by
    simpa only [Real.sin_zero,mul_zero] using hd
  have hc := hd0.comp 0 ht
  simp_rw [law_eq_tilt,BoundedExponentialTiltResponse.tilted_integral law halfTrace f
    halfTrace_measurable halfTrace_bound]
  convert hc using 1
  · rfl
  · ring

/-- A fixed physical plaquette probe, scaled to unit conditional Haar L2 norm. -/
def physicalMean (β h : ℝ) : ℝ :=
  ∫ A,2*observable (Function.update flux edge A) ∂responseLaw β h

theorem physical_derivative (β : ℝ) : HasDerivAt (physicalMean β) β 0 := by
  have hb (A : SU2) : |2*halfTrace A|≤2 := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [halfTrace_bound A]
  have hd := expectation_derivative β (fun A => 2*halfTrace A)
    (measurable_const.mul halfTrace_measurable) 2 (by norm_num) hb
  have hm : (∫ A,(2*halfTrace A)*halfTrace A ∂law)=(1/2:ℝ) := by
    calc
      _ = 2*(∫ A,halfTrace A^2 ∂law) := by
        rw [← integral_const_mul]
        congr 1
        funext A
        ring
      _ = 1/2 := by rw [(SU2TiltEnergyResponse.moment_values law).2.1]; norm_num
  rw [hm] at hd
  unfold physicalMean
  simp_rw [observable_section]
  convert hd using 1 <;> ring

theorem physical_probe_unit (β : ℝ) :
    (∫ A,(2*observable (Function.update flux edge A))^2 ∂responseLaw β 0)=1 := by
  rw [cancellation_law]
  simp_rw [observable_section]
  calc
    _ = 4*(∫ A,halfTrace A^2 ∂law) := by
      rw [← integral_const_mul]
      congr 1
      funext A
      ring
    _ = 1 := by rw [(SU2TiltEnergyResponse.moment_values law).2.1]; norm_num

attribute [local irreducible] physicalMean

theorem thermal_derivative (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun a => physicalMean (1/t^2) (t*a)) (1/t) 0 := by
  have hi : HasDerivAt (fun a : ℝ => t*a) t 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id 0).const_mul t
  have hd := (physical_derivative (1/t^2)).comp_of_eq 0 hi (by simp only [mul_zero])
  have he : (1/t^2)*t=1/t := by field_simp [ht]
  rw [he] at hd
  exact hd


def thermalSlope (t : ℝ) : ℝ := deriv (fun a => physicalMean (1/t^2) (t*a)) 0

theorem thermal_slope (t : ℝ) (ht : t ≠ 0) : thermalSlope t=1/t :=
  (thermal_derivative t ht).deriv

/-- No beta-uniform thermal response bound on this valid rough-exterior family. -/
theorem unbounded_thermal_response (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ t : ℝ,0<t ∧ t<ε ∧ C<thermalSlope t := by
  have hc : 0 < |C|+1 := by positivity
  let d := min ε (1/(|C|+1))
  have hd : 0<d := lt_min hε (by positivity)
  let t := d/2
  have ht : 0<t := half_pos hd
  have he : t<ε := (half_lt_self hd).trans_le (min_le_left _ _)
  have hb : t<1/(|C|+1) := (half_lt_self hd).trans_le (min_le_right _ _)
  have hm : t*(|C|+1)<1 := (lt_div_iff₀ hc).mp hb
  refine ⟨t,ht,he,?_⟩
  rw [thermal_slope t ht.ne']
  apply (lt_div_iff₀ ht).mpr
  nlinarith [le_abs_self C]

def rest : PeriodicLinkDisintegration.Rest edge := ((fun j => flux j.val),(1,1))

private theorem base_rest : PeriodicLinkDisintegration.baseField edge rest =
    Function.update flux edge 1 := by
  apply (PeriodicLinkDisintegration.coordinateSplit edge).injective
  rw [PeriodicLinkDisintegration.baseField,MeasurableEquiv.apply_symm_apply,
    PeriodicLinkDisintegration.coordinateSplit_apply]
  apply Prod.ext
  · simp only [Function.update_self]
  · funext j
    exact (Function.update_of_ne j.property 1 flux).symm

/-- Pointwise section of the already proved ACTUAL augmented-law disintegration. -/
theorem actual_kernel_section (β h : ℝ) :
    PeriodicLinkDisintegration.conditionalKernel edge β (upper h) (lower h) rest =
      responseLaw β h := by
  rw [PeriodicLinkDisintegration.kernel_eq_linkLaw,base_rest,linkLaw_update_base]
  rfl

end OperatorDerivativeRewrite.Foundation.PeriodicCancellingBoundaryResponse
