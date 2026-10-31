import Foundation.PeriodicBoundaryHaarReduction
import Foundation.PeriodicCenteredHolonomy
/-! Refined variation of a genuine center-even winding observable on the actual
periodic Wilson slice. Root winding readback, gauge/seam invariance, bounded
native domains and a ground-law operator residual bound are proved. The
quadratic increment correction is necessary. No quantitative centered variance,
center-even quasimode or continuum mass gap is claimed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicEvenWindingVariation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicSpatialHolonomy
open PeriodicBoundaryHaarReduction PeriodicGaugeSaturatedGround
open FourCubePinnedCoercivity PeriodicLoopVariation SU2WilsonConvolution
open PeriodicSlabGround PeriodicSlabJoint PeriodicSlabL2 PeriodicTemporalConcentration

private theorem imaginary_cs (a b : ℍ) :
    (a.imI*b.imI+a.imJ*b.imJ+a.imK*b.imK)^2 ≤
      (a.imI^2+a.imJ^2+a.imK^2)*(b.imI^2+b.imJ^2+b.imK^2) := by
  nlinarith [sq_nonneg (a.imI*b.imJ-a.imJ*b.imI),
    sq_nonneg (a.imI*b.imK-a.imK*b.imI),sq_nonneg (a.imJ*b.imK-a.imK*b.imJ)]

theorem refined_trace_change (A B : SU2) :
    (halfTrace A-halfTrace B)^2 ≤
      2*defect (A*B⁻¹)^2+4*(1-halfTrace A^2)*defect (A*B⁻¹) := by
  let H := A⁻¹*B
  have he : B=A*H := by dsimp [H]; group
  have hd : defect (A*B⁻¹)=defect H := by
    have hh : A*B⁻¹=A*H⁻¹*A⁻¹ := by dsimp [H]; group
    rw [hh,defect,halfTrace_conjugate,halfTrace_inv]
    rfl
  rw [hd,he]
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨h,hh⟩ := hom_surjective H
  rw [← hh]
  have hn (c : QuaternionAngularHaar.Group) : Quaternion.normSq (c : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
  have ha := hn a
  have hh := hn h
  have hc := imaginary_cs (a : ℍ) (h : ℍ)
  rw [← hom.map_mul,halfTrace_map,halfTrace_map,defect,halfTrace_map]
  change ((a : ℍ).re-((a : ℍ)*(h : ℍ)).re)^2 ≤
    2*(1-(h : ℍ).re)^2+4*(1-(a : ℍ).re^2)*(1-(h : ℍ).re)
  simp only [Quaternion.normSq_def'] at ha hh
  rw [Quaternion.re_mul]
  have ha2 : (a : ℍ).re^2 ≤ 1 := by
    nlinarith [sq_nonneg (a : ℍ).imI,sq_nonneg (a : ℍ).imJ,sq_nonneg (a : ℍ).imK]
  have hai : (a : ℍ).imI^2+(a : ℍ).imJ^2+(a : ℍ).imK^2=1-(a : ℍ).re^2 := by nlinarith
  have hhi : (h : ℍ).imI^2+(h : ℍ).imJ^2+(h : ℍ).imK^2=1-(h : ℍ).re^2 := by nlinarith
  rw [hai,hhi] at hc
  have ht : 0 ≤ 1-(a : ℍ).re^2 := by linarith
  have hprod := mul_nonneg ht (sq_nonneg (1-(h : ℍ).re))
  have hsum := sq_nonneg ((a : ℍ).re*(1-(h : ℍ).re)-
    ((a : ℍ).imI*(h : ℍ).imI+(a : ℍ).imJ*(h : ℍ).imJ+(a : ℍ).imK*(h : ℍ).imK))
  have hcs : ((a : ℍ).imI*(h : ℍ).imI+(a : ℍ).imJ*(h : ℍ).imJ+(a : ℍ).imK*(h : ℍ).imK)^2 ≤
      2*(1-(a : ℍ).re^2)*(1-(h : ℍ).re) := by nlinarith [hprod]
  have hx := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (1-(h : ℍ).re))
  nlinarith only [hcs,hx,hsum]


theorem trace_square_le_one (A : SU2) : halfTrace A^2 ≤ 1 := by
  have h := abs_le.mp (halfTrace_bound A)
  nlinarith

theorem refined_square_trace_change (A B : SU2) :
    (halfTrace A^2-halfTrace B^2)^2 ≤
      8*defect (A*B⁻¹)^2+16*(1-halfTrace A^2)*defect (A*B⁻¹) := by
  have hs : (halfTrace A+halfTrace B)^2 ≤ 4 := by
    nlinarith [trace_square_le_one A,trace_square_le_one B,
      sq_nonneg (halfTrace A-halfTrace B)]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (halfTrace A-halfTrace B))
  have he : (halfTrace A^2-halfTrace B^2)^2=
      (halfTrace A-halfTrace B)^2*(halfTrace A+halfTrace B)^2 := by ring
  rw [he]
  nlinarith [refined_trace_change A B]

def wrapChord (i : Fin 3) : ChordIndex := ⟨(thrice root i,i),by
  intro h
  exact h.1 (shift_four root i)⟩

private theorem axis_tree (i : Fin 3) :
    isTree (root,i) ∧ isTree (shift root i,i) ∧ isTree (twice root i,i) := by
  decide +revert

theorem axial_winding (q : Chords) (i : Fin 3) : winding (axialState q) root i=q (wrapChord i) := by
  obtain ⟨h0,h1,h2⟩ := axis_tree i
  simp only [winding,axialState,dif_pos h0,dif_pos h1,dif_pos h2,one_mul]
  exact dif_neg (wrapChord i).property

theorem reduced_winding (U : State) (i : Fin 3) : reduced U (wrapChord i)=winding U root i := by
  rw [← axial_winding (reduced U) i,← reconstruction,winding_gauge,rooted_root,one_mul,inv_one,mul_one]

def evenWinding (i : Fin 3) (U : State) : ℝ := 1-halfTrace (winding U root i)^2

theorem even_bounds (i : Fin 3) (U : State) : 0≤evenWinding i U ∧ evenWinding i U≤1 := by
  unfold evenWinding
  constructor
  · linarith [trace_square_le_one (winding U root i)]
  · linarith [sq_nonneg (halfTrace (winding U root i))]

theorem even_gauge (i : Fin 3) (a : Gauge) (U : State) :
    evenWinding i (PeriodicSlabGauge.gaugeAction a U)=evenWinding i U := by
  unfold evenWinding
  rw [trace_gauge]

theorem even_seam (i j : Fin 3) (U : State) :
    evenWinding i (PeriodicCenterSeam.flip j U)=evenWinding i U := by
  unfold evenWinding
  by_cases hij : i=j
  · subst j
    change 1-halfTrace (winding (PeriodicCenterSeam.flip i U) PeriodicCenteredHolonomy.origin i)^2=_
    rw [PeriodicCenteredHolonomy.winding_flip_same,SU2StrongCouplingCovariance.halfTrace_center_neg,neg_sq]
    rfl
  · rw [PeriodicCenteredHolonomy.winding_flip_other j i hij]

theorem even_measurable (i : Fin 3) : Measurable (evenWinding i) := by
  unfold evenWinding
  exact measurable_const.sub ((halfTrace_measurable.comp (by unfold winding; fun_prop)).pow_const 2)

theorem winding_defect_bound (U V : State) (a : Gauge) (v : SpatialVertex) (i : Fin 3) :
    defect (winding U v i*(winding (PeriodicSlabGauge.gaugeAction a V) v i)⁻¹) ≤
      16*PeriodicWilsonSlab.temporalAction U V a := by
  have hd := winding_distance U V a v i
  have hn : 0≤PeriodicWilsonSlab.temporalAction U V a :=
    (PeriodicWilsonSlab.temporal_action_bounds U V a).1
  have hs := Real.sq_sqrt (by linarith : 0≤2*PeriodicWilsonSlab.temporalAction U V a)
  have hsq := mul_self_le_mul_self (norm_nonneg (lift (winding U v i)-
    lift (winding (PeriodicSlabGauge.gaugeAction a V) v i))) hd
  change distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i)*
    distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i) ≤ _ at hsq
  have he := distance_sq (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i)
  nlinarith

theorem even_temporal_variation (U V : State) (a : Gauge) (i : Fin 3) :
    (evenWinding i U-evenWinding i V)^2 ≤
      2048*PeriodicWilsonSlab.temporalAction U V a^2+
        256*evenWinding i U*PeriodicWilsonSlab.temporalAction U V a := by
  have h := refined_square_trace_change (winding U root i)
    (winding (PeriodicSlabGauge.gaugeAction a V) root i)
  have hb := winding_defect_bound U V a root i
  have hn := defect_nonneg (winding U root i*(winding (PeriodicSlabGauge.gaugeAction a V) root i)⁻¹)
  have hs := mul_self_le_mul_self hn hb
  have hm := mul_le_mul_of_nonneg_left hb (even_bounds i U).1
  rw [trace_gauge] at h
  unfold evenWinding at hm ⊢
  nlinarith only [h,hs,hm]


theorem quadratic_term_necessary (C : ℝ) :
    ¬∀ A B : SU2,(halfTrace A^2-halfTrace B^2)^2 ≤
      C*(1-halfTrace A^2)*defect (A*B⁻¹) := by
  obtain ⟨B,D,hcomm,hB,hD,hBD⟩ := SU2HolonomyTraceObstruction.two_traces_can_vanish
  intro h
  have hh := h 1 B
  rw [SU2OpenLinkGaugeObstruction.halfTrace_one,hB] at hh
  norm_num at hh

variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance joint_probability : IsProbabilityMeasure (tripleLaw g) := triple_probability g

theorem even_memLp (i : Fin 3) : MemLp (evenWinding i) 2 g.stationary :=
  MemLp.of_bound (even_measurable i).aestronglyMeasurable 1
    (ae_of_all _ (fun U => by rw [Real.norm_eq_abs,abs_of_nonneg (even_bounds i U).1]; exact (even_bounds i U).2))

def weightedEnergy (i : Fin 3) (q : Triple) : ℝ := evenWinding i q.1.1*energy q

theorem weighted_integrable (i : Fin 3) : Integrable (weightedEnergy i) (tripleLaw g) := by
  apply Integrable.of_bound (((even_measurable i).comp (measurable_fst.comp measurable_fst)).mul
    energy_measurable).aestronglyMeasurable 768
  filter_upwards with q
  change ‖evenWinding i q.1.1*energy q‖≤768
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (even_bounds i q.1.1).1 (energy_bounds q).1)]
  change evenWinding i q.1.1*energy q≤768
  nlinarith [(even_bounds i q.1.1).1,(even_bounds i q.1.1).2,(energy_bounds q).1,(energy_bounds q).2]

theorem even_energy_variation (i : Fin 3) (q : Triple) :
    (evenWinding i q.1.2-evenWinding i q.1.1)^2 ≤
      2048*energy q^2+256*weightedEnergy i q := by
  have h := even_temporal_variation q.1.1 q.1.2 q.2 i
  have ht := temporal_le_energy q
  have hs := mul_self_le_mul_self (temporal_bounds q).1 ht
  have hm := mul_le_mul_of_nonneg_left ht (even_bounds i q.1.1).1
  change _≤2048*temporalEnergy q^2+256*evenWinding i q.1.1*temporalEnergy q at h
  unfold weightedEnergy
  nlinarith only [h,hs,hm]

theorem native_residual_bound (i : Fin 3) :
    ‖operator g ((even_memLp g i).toLp (evenWinding i))-
      (even_memLp g i).toLp (evenWinding i)‖^2 ≤
      2048*(∫ q,energy q^2 ∂tripleLaw g)+256*(∫ q,weightedEnergy i q ∂tripleLaw g) := by
  have hres := PeriodicTransferVariation.operator_residual g ((even_memLp g i).toLp (evenWinding i))
  have hsq := mul_self_le_mul_self (norm_nonneg _) hres
  have hnorm := PeriodicTransferVariation.edge_norm_square g (evenWinding i) (even_memLp g i)
  have hm : Measurable (fun p : State × State => (evenWinding i p.2-evenWinding i p.1)^2) :=
    (((even_measurable i).comp measurable_snd).sub ((even_measurable i).comp measurable_fst)).pow_const 2
  have hp := integral_map (μ := tripleLaw g) (φ := (Prod.fst : Triple → State × State))
    measurable_fst.aemeasurable hm.aestronglyMeasurable
  rw [(pair_preserving g).map_eq] at hp
  have hi := ((PeriodicCurvatureWeighted.energy_square_integrable g).const_mul 2048).add
    ((weighted_integrable g i).const_mul 256)
  have hle := integral_mono_of_nonneg
    (ae_of_all (tripleLaw g) (fun q : Triple => sq_nonneg (evenWinding i q.1.2-evenWinding i q.1.1)))
    hi (ae_of_all _ (even_energy_variation i))
  change (∫ q : Triple,(evenWinding i q.1.2-evenWinding i q.1.1)^2 ∂tripleLaw g)≤
    (∫ q : Triple,2048*energy q^2+256*weightedEnergy i q ∂tripleLaw g) at hle
  rw [integral_add ((PeriodicCurvatureWeighted.energy_square_integrable g).const_mul 2048)
    ((weighted_integrable g i).const_mul 256),integral_const_mul,integral_const_mul] at hle
  change (∫ p : State × State,(evenWinding i p.2-evenWinding i p.1)^2 ∂edgeLaw g)=
    (∫ q : Triple,(evenWinding i q.1.2-evenWinding i q.1.1)^2 ∂tripleLaw g) at hp
  nlinarith only [hsq,hnorm,hp,hle]


theorem native_residual_scale (hb : 16777216≤β) (i : Fin 3) :
    ‖operator g ((even_memLp g i).toLp (evenWinding i))-
      (even_memLp g i).toLp (evenWinding i)‖^2 ≤
      16384*ratioConstant/β^2+256*(∫ q,weightedEnergy i q ∂tripleLaw g) := by
  have h := native_residual_bound g i
  have he := mul_le_mul_of_nonneg_left (energy_square_uniform β hb g)
    (by norm_num : (0 : ℝ)≤2048)
  calc
    _ ≤ 2048*(8*ratioConstant/β^2)+256*(∫ q,weightedEnergy i q ∂tripleLaw g) := by linarith
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.PeriodicEvenWindingVariation
