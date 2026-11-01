import Foundation.PeriodicCubeConditionalGram
import Foundation.PeriodicSpatialRowDependence

/-! A nonlinear Wilson trace checkerboard whose single-link fibers vanish at
the flat field. This is not the older linear coarse/fine checkerboard mode. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicFlatCheckerboardObstruction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
open PeriodicCurvatureVariance
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar incidentFaces

def signZ (v : SpatialVertex) : ℤ := (-1)^((v 0).val+(v 1).val+(v 2).val)
def weightZ (p : SpatialFace) : ℤ := signZ p.val.1
def weight (p : SpatialFace) : ℝ := (weightZ p : ℝ)
def observable (V : State) : ℝ := ∑ p : SpatialFace, weight p*plaquette p V

private theorem sign_backshift (v : SpatialVertex) (j : Fin 3) :
    signZ (backshift v j)= -signZ v := by
  revert v j
  decide +kernel

private theorem shift_backshift (v : SpatialVertex) (j : Fin 3) :
    shift (backshift v j) j=v := by
  funext k
  simp [shift,backshift]

private theorem sign_shift (v : SpatialVertex) (j : Fin 3) : signZ (shift v j)= -signZ v := by
  have h := sign_backshift (shift v j) j
  rw [backshift_shift] at h
  omega

private def faceShift : SpatialFace ≃ SpatialFace where
  toFun p := ⟨(shift p.val.1 0,p.val.2),p.property⟩
  invFun p := ⟨(backshift p.val.1 0,p.val.2),p.property⟩
  left_inv p := by apply Subtype.ext; exact Prod.ext (backshift_shift _ _) rfl
  right_inv p := by apply Subtype.ext; exact Prod.ext (shift_backshift _ _) rfl

private theorem total_weightZ : (∑ p : SpatialFace, weightZ p)=0 := by
  have h := Equiv.sum_comp faceShift weightZ
  have hs (p : SpatialFace) : weightZ (faceShift p)= -weightZ p := sign_shift _ _
  simp only [hs,Finset.sum_neg_distrib] at h
  omega

theorem total_weight : (∑ p : SpatialFace, weight p)=0 := by
  unfold weight
  exact_mod_cast total_weightZ

private theorem backshift_ne (v : SpatialVertex) (j : Fin 3) : backshift v j≠v := by
  intro h
  have hs := shift_backshift v j
  rw [h] at hs
  exact shift_ne_self v j hs

private theorem sorted_base (v : SpatialVertex) (i j : Fin 3) (h : i≠j) :
    (sortedFace v i j h).val.1=v := by
  unfold sortedFace
  split_ifs <;> rfl

private theorem sorted_pair (v : SpatialVertex) (i j : Fin 3) (h : i≠j) :
    (sortedFace v i j h).val.2=if i<j then (i,j) else (j,i) := by
  unfold sortedFace
  split_ifs <;> rfl

private theorem candidate_injective (e : SpatialEdge) : Function.Injective (candidateFace e) := by
  rintro ⟨j,b⟩ ⟨k,c⟩ h
  have hd : j.val=k.val := by
    have hp := congrArg (fun p : SpatialFace => p.val.2) h
    simp only [candidateFace,sorted_pair] at hp
    have hh : ∀ i j k : Fin 3, i≠j → i≠k →
        (if i<j then (i,j) else (j,i))=(if i<k then (i,k) else (k,i)) → j=k := by
      decide
    exact hh e.2 j.val k.val j.property.symm k.property.symm hp
  have hjk : j=k := Subtype.ext hd
  subst k
  have hb := congrArg (fun p : SpatialFace => p.val.1) h
  simp only [candidateFace,sorted_base] at hb
  have hbc : b=c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (backshift_ne e.1 j hb)
    · exact False.elim (backshift_ne e.1 j hb.symm)
    · rfl
  cases hbc
  rfl

private theorem candidate_mem (e : SpatialEdge) (q : {j : Fin 3 // j≠e.2} × Bool) :
    candidateFace e q∈incidentFaces e := by
  apply (mem_incidentFaces e _).mpr
  rcases q with ⟨j,b⟩
  by_cases h : e.2<j.val
  · cases b
    · refine ⟨2,?_⟩
      simp [candidateFace,sortedFace,h,faceEdge,shift_backshift]
    · exact ⟨0,by simp [candidateFace,sortedFace,h,faceEdge]⟩
  · cases b
    · refine ⟨1,?_⟩
      simp [candidateFace,sortedFace,h,faceEdge,shift_backshift]
    · exact ⟨3,by simp [candidateFace,sortedFace,h,faceEdge]⟩

private theorem incident_candidates (e : SpatialEdge) : incidentFaces e=candidates e := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨k,hk⟩ := (mem_incidentFaces e p).mp hp
    rw [← hk]
    exact face_in_candidates p k
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact candidate_mem e q

private theorem candidate_weight (e : SpatialEdge) (j : {j : Fin 3 // j≠e.2}) (b : Bool) :
    weightZ (candidateFace e (j,b))=if b then signZ e.1 else -signZ e.1 := by
  unfold weightZ candidateFace
  rw [sorted_base]
  cases b <;> simp [sign_backshift]

private theorem incident_weightZ (e : SpatialEdge) :
    (∑ p ∈ incidentFaces e, weightZ p)=0 := by
  rw [incident_candidates]
  unfold candidates
  rw [Finset.sum_image (fun a ha b hb h => candidate_injective e h)]
  rw [Fintype.sum_prod_type]
  simp [candidate_weight,Fintype.sum_bool]

theorem incident_weight (e : SpatialEdge) : (∑ p ∈ incidentFaces e, weight p)=0 := by
  unfold weight
  exact_mod_cast incident_weightZ e

private theorem flat_remainder (p : SpatialFace) (k : Fin 4) : faceRemainder 1 p k=1 := by
  fin_cases k <;> simp [faceRemainder]

private theorem flat_trace (e : SpatialEdge) (p : SpatialFace) (A : SU2) :
    plaquette p (Function.update 1 e A)=if p∈incidentFaces e then halfTrace A else 1 := by
  by_cases hp : p∈incidentFaces e
  · obtain ⟨k,hk⟩ := (mem_incidentFaces e p).mp hp
    have h := spatial_trace_at_slot 1 p k A
    simpa only [plaquette,hk,flat_remainder,mul_one,if_pos hp] using h
  · simp only [plaquette,spatial_word_nonincident 1 e p hp A,if_neg hp]
    exact plaquette_one p

theorem flat_fiber_zero (e : SpatialEdge) (A : SU2) :
    observable (Function.update 1 e A)=0 := by
  classical
  unfold observable
  simp_rw [flat_trace]
  have he (p : SpatialFace) :
      weight p*(if p∈incidentFaces e then halfTrace A else 1)=
        weight p+(if p∈incidentFaces e then weight p*(halfTrace A-1) else 0) := by
    by_cases hp : p∈incidentFaces e <;> simp [hp] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,total_weight,zero_add,← Finset.sum_filter]
  have hf : (Finset.univ.filter (fun p : SpatialFace => p∈incidentFaces e))=incidentFaces e := by
    ext p
    simp
  rw [hf,← Finset.sum_mul,incident_weight,zero_mul]

theorem observable_one : observable 1=0 := by
  unfold observable
  simp only [plaquette_one,mul_one,total_weight]

private theorem weighted_change (V : State) (e : SpatialEdge) (A : SU2) :
    observable (Function.update V e A)-observable (Function.update V e 1)=
      ∑ p∈incidentFaces e, (weight p*plaquette p (Function.update V e A)-
        weight p*plaquette p (Function.update V e 1)) := by
  classical
  unfold observable
  rw [← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hn
  simp only [plaquette,spatial_word_nonincident V e p hn A,
    spatial_word_nonincident V e p hn 1,sub_self]

/-- Exact two-link section in the original spatial state, with arbitrary
noncommuting SU2 matrices. -/
theorem two_link_formula (A B : SU2) :
    observable (Function.update (PeriodicSpatialRowDependence.field B)
      PeriodicSpatialRowDependence.edge A)=halfTrace (A*B)-halfTrace A-halfTrace B+1 := by
  have h := weighted_change (PeriodicSpatialRowDependence.field B)
    PeriodicSpatialRowDependence.edge A
  rw [PeriodicSpatialRowDependence.field_update_one] at h
  have h0 : observable (PeriodicSpatialRowDependence.field B)=0 :=
    flat_fiber_zero PeriodicSpatialRowDependence.neighbor B
  rw [h0,sub_zero,PeriodicSpatialRowDependence.incident_exact] at h
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton] at h
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (-1 : ZMod 4).val=3 := by decide
  norm_num [weight,weightZ,signZ,plaquette,spatialWord,
    PeriodicSpatialRowDependence.field,PeriodicSpatialRowDependence.face01,
    PeriodicSpatialRowDependence.face02,PeriodicSpatialRowDependence.back01,
    PeriodicSpatialRowDependence.back02,PeriodicSpatialRowDependence.neighbor,
    PeriodicSpatialRowDependence.edge,shift,backshift,Function.update_apply,
    funext_iff,Fin.forall_fin_succ,h01,h10,hv,SU2WilsonConvolution.halfTrace_inv,
    SU2OpenLinkGaugeObstruction.halfTrace_one] at h
  change observable (Function.update (Function.update 1 (shift 0 0,1) B) (0,0) A)=_
  linarith

def witness : State := Function.update
  (PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne)
  PeriodicSpatialRowDependence.edge SU2StapleExtremes.minusOne

theorem observable_witness : observable witness=4 := by
  unfold witness
  rw [two_link_formula,SU2StrongCouplingCovariance.halfTrace_center_neg,
    SU2OpenLinkGaugeObstruction.halfTrace_minusOne]
  norm_num

def axisSection (s t : ℝ) : ℝ := observable (Function.update
  (PeriodicSpatialRowDependence.field (SU2JointPlaquetteCubic.axis 0 t))
  PeriodicSpatialRowDependence.edge (SU2JointPlaquetteCubic.axis 0 s))

theorem axisSection_formula (s t : ℝ) :
    axisSection s t=Real.cos (s+t)-Real.cos s-Real.cos t+1 := by
  have ht (z : ℝ) : halfTrace (SU2JointPlaquetteCubic.axis 0 z)=Real.cos z := by
    change SU2TraceHessianModel.traceReal
      (QuaternionSU2Representation.repr (SU2JointPlaquetteCubic.axisRaw 0 z))/2=_
    rw [repr_halfTrace]
    simp [SU2JointPlaquetteCubic.axisRaw]
  have hp : halfTrace (SU2JointPlaquetteCubic.axis 0 s*SU2JointPlaquetteCubic.axis 0 t)=
      Real.cos (s+t) := by
    unfold SU2JointPlaquetteCubic.axis
    rw [← hom.map_mul,halfTrace_map]
    change (SU2JointPlaquetteCubic.axisRaw 0 s*SU2JointPlaquetteCubic.axisRaw 0 t).re=_
    simp [SU2JointPlaquetteCubic.axisRaw,Quaternion.re_mul,Real.cos_add,sub_eq_add_neg]
  unfold axisSection
  rw [two_link_formula,hp,ht,ht]

theorem axis_first (t : ℝ) : deriv (fun s => axisSection s t) 0= -Real.sin t := by
  rw [show (fun s => axisSection s t)=(fun s => Real.cos (s+t)-Real.cos s-Real.cos t+1)
    from funext (fun s => axisSection_formula s t)]
  have hc := (Real.hasDerivAt_cos (0+t)).comp 0 ((hasDerivAt_id (0 : ℝ)).add_const t)
  have h := ((hc.sub (Real.hasDerivAt_cos 0)).sub_const (Real.cos t)).add_const 1
  convert h.deriv using 1 <;> simp

theorem mixed_derivative : deriv (fun t => deriv (fun s => axisSection s t) 0) 0= -1 := by
  rw [show (fun t => deriv (fun s => axisSection s t) 0)=(fun t => -Real.sin t)
    from funext axis_first]
  simpa using ((Real.hasDerivAt_sin 0).neg).deriv

theorem observable_nonconstant : ¬∃ c : ℝ, ∀ V, observable V=c := by
  rintro ⟨c,hc⟩
  have h1 := hc 1
  have h2 := hc witness
  rw [observable_one] at h1
  rw [observable_witness] at h2
  linarith

theorem weight_square (p : SpatialFace) : weight p^2=1 := by
  have h : weightZ p^2=1 := by
    unfold weightZ signZ
    rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
  unfold weight
  exact_mod_cast h

theorem weight_abs (p : SpatialFace) : |weight p|=1 := by
  nlinarith [weight_square p,sq_abs (weight p),abs_nonneg (weight p)]

theorem coefficient_norm : (∑ p : SpatialFace, weight p^2)=192 := by
  simp [weight_square,PeriodicTemporalSlab.face_count]

theorem observable_measurable : Measurable observable :=
  Finset.measurable_sum _ (fun p _ => (plaquette_measurable p).const_mul (weight p))

private theorem term_bound (p : SpatialFace) (V : State) : |weight p*plaquette p V|≤1 := by
  rw [abs_mul,weight_abs,one_mul]
  exact halfTrace_bound _

theorem observable_bound (V : State) : |observable V|≤192 :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun p _ => term_bound p V)).trans_eq
      (by simp [PeriodicTemporalSlab.face_count]))

theorem observable_memLp (μ : Measure State) [IsFiniteMeasure μ] :
    MemLp observable 2 μ :=
  MemLp.of_bound observable_measurable.aestronglyMeasurable 192
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using observable_bound V))

theorem observable_gauge (g : Gauge) (V : State) :
    observable (PeriodicSlabGauge.gaugeAction g V)=observable V := by
  unfold observable plaquette
  simp only [PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]

theorem observable_center_even (i : Fin 3) (V : State) :
    observable (PeriodicCenterSeam.flip i V)=observable V := by
  unfold observable plaquette
  simp only [PeriodicCenterSeam.spatial_word]

def rowVariance (β : ℝ) (U W V : State) (g h : Gauge) (e : SpatialEdge) : ℝ :=
  variance (fun A => observable (Function.update V e A))
    (PeriodicLinkDisintegration.conditionalKernel e β U W
      (((PeriodicLinkDisintegration.split e) (V,(g,h))).1))

theorem conditional_mean_flat (e : SpatialEdge) (β : ℝ) (U W : State) (g h : Gauge) :
    PeriodicNativeCompression.conditionalMean e β U W (fun q => observable q.1)
      (((PeriodicLinkDisintegration.split e) (1,(g,h))).1)=0 := by
  simp only [PeriodicNativeCompression.conditionalMean,PeriodicCubeConditionalGram.assemble_state,
    flat_fiber_zero,integral_zero]

theorem rowVariance_flat (β : ℝ) (U W : State) (g h : Gauge) (e : SpatialEdge) :
    rowVariance β U W 1 g h e=0 := by
  unfold rowVariance
  rw [show (fun A => observable (Function.update 1 e A))=(fun _ => 0) from
    funext (flat_fiber_zero e)]
  exact variance_zero _

def totalNoise (β : ℝ) (U W V : State) (g h : Gauge) : ℝ :=
  ∑ e : SpatialEdge, rowVariance β U W V g h e

theorem totalNoise_flat (β : ℝ) (U W : State) (g h : Gauge) :
    totalNoise β U W 1 g h=0 := by
  simp only [totalNoise,rowVariance_flat,Finset.sum_const_zero]

/-- A local plaquette-defect error cannot repair an all-plaquette coefficient
floor: this obstruction already occurs with every original defect equal to0. -/
theorem no_near_flat_coefficient_floor (β : ℝ) (U W : State) (κ ε : ℝ)
    (hκ : 0 < κ) (hε : 0 ≤ ε) :
    ¬∀ V : State, (∀ p : SpatialFace, 1-plaquette p V≤ε) →
      ∀ g h : Gauge, κ*(∑ p : SpatialFace, weight p^2)≤totalNoise β U W V g h := by
  intro h
  have hx := h 1 (fun p => by simpa only [plaquette_one,sub_self] using hε) 1 1
  rw [coefficient_norm,totalNoise_flat] at hx
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicFlatCheckerboardObstruction
