import Foundation.PeriodicEndpointScore
/-! Actual spatial-link conditional components of the genuine endpoint score.
The row normalizer and rest-marginal response must be retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicConditionalEndpointScore
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq

def localDirection (U W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) : ℝ :=
  halfTrace (A*leftTemporal (PeriodicEndpointScore.left (Real.pi/2) U) a e)+
    halfTrace (A*rightTemporal (PeriodicEndpointScore.right (Real.pi/2) W) b e)

theorem localDirection_measurable (U W : State) (a b : Gauge) (e : SpatialEdge) :
    Measurable (localDirection U W a b e) :=
  (halfTrace_measurable.comp (measurable_id.mul measurable_const)).add
    (halfTrace_measurable.comp (measurable_id.mul measurable_const))

theorem localDirection_bound (U W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    |localDirection U W a b e A|≤2 := by
  unfold localDirection
  have hl := halfTrace_bound (A*leftTemporal (PeriodicEndpointScore.left (Real.pi/2) U) a e)
  have hr := halfTrace_bound (A*rightTemporal (PeriodicEndpointScore.right (Real.pi/2) W) b e)
  exact (abs_add_le _ _).trans (by linarith)

private theorem direction_temporal (U V W : State) (a b : Gauge) :
    PeriodicEndpointScore.direction U W (V,(a,b))=384-
      temporalAction (PeriodicEndpointScore.left (Real.pi/2) U) V a-
      temporalAction V (PeriodicEndpointScore.right (Real.pi/2) W) b := by
  have h := PeriodicEndpointScore.central_trace
    (PeriodicEndpointScore.left (Real.pi/2) U) (PeriodicEndpointScore.right (Real.pi/2) W) (V,(a,b))
  unfold PeriodicAugmentedBridge.centralAction at h
  unfold PeriodicEndpointScore.direction
  linarith

/-- Exact cancellation of all OTHER temporal plaquettes in a selected-link variation. -/
theorem direction_difference (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    PeriodicEndpointScore.direction U W (Function.update V e A,(a,b))-
      PeriodicEndpointScore.direction U W (Function.update V e 1,(a,b))=
        localDirection U W a b e A-localDirection U W a b e 1 := by
  rw [direction_temporal,direction_temporal]
  have hl := temporal_action_change_left (PeriodicEndpointScore.left (Real.pi/2) U) V a e A
  have hr := temporal_action_change_right V (PeriodicEndpointScore.right (Real.pi/2) W) b e A
  simp only [localDirection,one_mul]
  linarith

variable (e : SpatialEdge)

def source (β : ℝ) (U W : State) (z : PeriodicLinkDisintegration.Rest e × SU2) : ℝ :=
  PeriodicEndpointScore.score β U W ((PeriodicLinkDisintegration.split e).symm z)

theorem source_measurable (β : ℝ) (U W : State) : Measurable (source e β U W) :=
  (PeriodicEndpointScore.score_measurable β U W).comp (PeriodicLinkDisintegration.split e).symm.measurable

theorem source_bound (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (A : SU2) :
    |source e β U W (r,A)|≤768*|β| := PeriodicEndpointScore.score_bound β U W _

theorem source_memLp (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
    MemLp (fun A => source e β U W (r,A)) 2 (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  apply MemLp.of_bound ((source_measurable e β U W).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable (768*|β|)
  filter_upwards with A
  simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using source_bound e β U W r A

def restScore (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) : ℝ :=
  ∫ A,source e β U W (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r

def linkInnovation (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (A : SU2) : ℝ :=
  source e β U W (r,A)-restScore e β U W r

theorem restScore_measurable (β : ℝ) (U W : State) : Measurable (restScore e β U W) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  exact (source_measurable e β U W).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem restScore_bound (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
    |restScore e β U W r|≤768*|β| := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  simpa only [restScore,Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := PeriodicLinkDisintegration.conditionalKernel e β U W r)
    (f := fun A => source e β U W (r,A)) (C := 768*|β|)
    (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using source_bound e β U W r A))

theorem linkInnovation_mean_zero (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
    (∫ A,linkInnovation e β U W r A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=0 := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  unfold linkInnovation
  rw [integral_sub ((source_memLp e β U W r).integrable (by norm_num)) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,restScore,sub_self]

/-- A genuine conditional Fisher/Pythagorean split in the ORIGINAL row norm. -/
theorem row_fisher (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
    (∫ A,(source e β U W (r,A))^2 ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
      (∫ A,(linkInnovation e β U W r A)^2 ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)+
        (restScore e β U W r)^2 := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have h := variance_eq_sub (source_memLp e β U W r)
  have hf : Measurable (fun A => source e β U W (r,A)) := by
    simpa only [Function.comp_def,id_eq] using (source_measurable e β U W).comp
      (measurable_const.prodMk measurable_id)
  rw [variance_eq_integral hf.aemeasurable] at h
  change (∫ A,(linkInnovation e β U W r A)^2 ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
    (∫ A,(source e β U W (r,A))^2 ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)-
      (restScore e β U W r)^2 at h
  linarith

/-- Only TWO local temporal traces remain after true conditional centering. -/
theorem linkInnovation_local (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (A : SU2) :
    linkInnovation e β U W r A=β*(localDirection U W r.2.1 r.2.2 e A-
      ∫ B,localDirection U W r.2.1 r.2.2 e B ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hlm : MemLp (localDirection U W r.2.1 r.2.2 e) 2
      (PeriodicLinkDisintegration.conditionalKernel e β U W r) :=
    MemLp.of_bound (localDirection_measurable _ _ _ _ _).aestronglyMeasurable 2
      (ae_of_all _ (fun B => by simpa only [Real.norm_eq_abs] using localDirection_bound U W r.2.1 r.2.2 e B))
  let c : ℝ := source e β U W (r,1)-β*localDirection U W r.2.1 r.2.2 e 1
  have hs (B : SU2) : source e β U W (r,B)=β*localDirection U W r.2.1 r.2.2 e B+c := by
    dsimp only [c]
    have hd := direction_difference U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e B
    unfold source PeriodicEndpointScore.score
    rw [PeriodicLinkDisintegration.assemble,PeriodicLinkDisintegration.assemble]
    linear_combination β*hd
  unfold linkInnovation restScore
  simp_rw [hs]
  rw [integral_add ((hlm.integrable (by norm_num)).const_mul β) (integrable_const _),
    integral_const_mul,integral_const,probReal_univ,one_smul]
  ring

/-- The conditional centered channel has a two-trace bound without a full-slice factor. -/
theorem linkInnovation_bound (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (A : SU2) :
    |linkInnovation e β U W r A|≤4*|β| := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hm : |∫ B,localDirection U W r.2.1 r.2.2 e B
      ∂PeriodicLinkDisintegration.conditionalKernel e β U W r|≤2 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := PeriodicLinkDisintegration.conditionalKernel e β U W r)
      (f := localDirection U W r.2.1 r.2.2 e) (C := 2)
      (ae_of_all _ (fun B => by simpa only [Real.norm_eq_abs] using localDirection_bound U W r.2.1 r.2.2 e B))
  rw [linkInnovation_local,abs_mul]
  have hh : |localDirection U W r.2.1 r.2.2 e A-
      ∫ B,localDirection U W r.2.1 r.2.2 e B
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r|≤4 := by
    apply (abs_sub _ _).trans
    linarith [localDirection_bound U W r.2.1 r.2.2 e A]
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg β)).trans_eq (mul_comm _ _)

/-- Original conditional row integral, with its actual unnormalized density. -/
theorem kernel_integral (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (f : SU2 → ℝ) :
    (∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
      (∫ A,PeriodicAugmentedBridge.density β U W ((PeriodicLinkDisintegration.split e).symm (r,A))*f A ∂law)/
      (∫ A,PeriodicAugmentedBridge.density β U W ((PeriodicLinkDisintegration.split e).symm (r,A)) ∂law) := by
  rw [PeriodicLinkDisintegration.kernel_eq_linkLaw,linkLaw_eq_stapleLaw]
  have h := normalized_link_integral β U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e f
  have he : (fun A => f A*localDensity β U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e A)=
      (fun A => localDensity β U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e A*f A) := by
    funext A
    ring
  rw [he] at h
  simpa only [PeriodicLinkDisintegration.assemble,localDensity] using h.symm

private theorem kernel_central_integral (β : ℝ) (U W : State)
    (r : PeriodicLinkDisintegration.Rest e) (f : SU2 → ℝ) :
    (∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
      (∫ A,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W
        ((PeriodicLinkDisintegration.split e).symm (r,A)))*f A ∂law)/
      (∫ A,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W
        ((PeriodicLinkDisintegration.split e).symm (r,A))) ∂law) := by
  rw [kernel_integral]
  simp_rw [PeriodicAugmentedBridge.density_phase,mul_assoc,integral_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

def rowWeighted (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e)
    (f : SU2 → ℝ) (h : ℝ) : ℝ :=
  ∫ A,f A*Real.exp (PeriodicEndpointScore.phase β U W h
    ((PeriodicLinkDisintegration.split e).symm (r,A)))
      ∂PeriodicLinkDisintegration.conditionalKernel e β U W r

/-- The TRUE rotated row law, not an affine replacement of its tangent. -/
theorem rotated_kernel_integral (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e)
    (f : SU2 → ℝ) (h : ℝ) :
    (∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β
      (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W) r)=
        rowWeighted e β U W r f h/rowWeighted e β U W r (fun _ => 1) h := by
  rw [kernel_central_integral]
  unfold rowWeighted
  rw [kernel_central_integral,kernel_central_integral]
  simp only [one_mul]
  have hN : (∫ A,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W
      ((PeriodicLinkDisintegration.split e).symm (r,A)))*(f A*Real.exp
        (PeriodicEndpointScore.phase β U W h ((PeriodicLinkDisintegration.split e).symm (r,A)))) ∂law)=
      (∫ A,Real.exp (-β*PeriodicAugmentedBridge.centralAction
        (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W)
        ((PeriodicLinkDisintegration.split e).symm (r,A)))*f A ∂law) := by
    apply integral_congr_ae
    filter_upwards with A
    rw [PeriodicEndpointScore.central_weight_rotation]
    ring
  rw [hN]
  simp_rw [← PeriodicEndpointScore.central_weight_rotation]
  have hz : (∫ A,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W
      ((PeriodicLinkDisintegration.split e).symm (r,A))) ∂law)≠0 := by
    have hp := localDensity_integral_pos β U (PeriodicLinkDisintegration.baseField e r) W r.2.1 r.2.2 e
    change 0<(∫ A,PeriodicAugmentedBridge.density β U W
      (Function.update (PeriodicLinkDisintegration.baseField e r) e A,r.2) ∂law) at hp
    simp_rw [← PeriodicLinkDisintegration.assemble,PeriodicAugmentedBridge.density_phase,integral_const_mul] at hp
    exact (mul_ne_zero_iff.mp hp.ne').2
  exact (div_div_div_cancel_right₀ hz _ _).symm

attribute [local irreducible] PeriodicLinkDisintegration.split
  PeriodicLinkDisintegration.conditionalKernel PeriodicLinkDisintegration.joint PeriodicLinkDisintegration.marginal
  PeriodicAugmentedBridge.law PeriodicEndpointScore.traceSum PeriodicEndpointScore.direction
  PeriodicEndpointScore.phase PeriodicEndpointScore.phaseSlope

private theorem rowWeighted_zero (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (f : SU2 → ℝ) :
    rowWeighted e β U W r f 0=∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r := by
  simp only [rowWeighted,PeriodicEndpointScore.phase,Real.cos_zero,Real.sin_zero,sub_self,
    zero_mul,mul_zero,add_zero,Real.exp_zero,mul_one]

/-- The integral criterion is instantiated on the ACTUAL row probability. All
geometric derivative and domination inputs reuse the verified endpoint phase. -/
private theorem rowWeighted_derivative (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e)
    (f : SU2 → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ A,|f A|≤M) :
    HasDerivAt (rowWeighted e β U W r f)
      (∫ A,f A*(β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) 0 := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  let μ := PeriodicLinkDisintegration.conditionalKernel e β U W r
  let q := fun A : SU2 => (PeriodicLinkDisintegration.split e).symm (r,A)
  have hq : Measurable q := (PeriodicLinkDisintegration.split e).symm.measurable.comp
    (measurable_const.prodMk measurable_id)
  let F := fun h A => f A*Real.exp (PeriodicEndpointScore.phase β U W h (q A))
  let F' := fun h A => f A*Real.exp (PeriodicEndpointScore.phase β U W h (q A))*
    PeriodicEndpointScore.phaseSlope β U W h (q A)
  have hs : Set.Ioo (-1:ℝ) 1∈𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ h,AEStronglyMeasurable (F h) μ := fun h =>
    (hf.mul ((PeriodicEndpointScore.phase_measurable β U W h).comp hq).exp).aestronglyMeasurable
  have hint : Integrable (F 0) μ := by
    apply Integrable.mono' (integrable_const M) (hmeas 0)
    filter_upwards with A
    simpa only [F,PeriodicEndpointScore.phase,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,
      mul_zero,add_zero,Real.exp_zero,mul_one,Real.norm_eq_abs] using hfb A
  have hdmeas : AEStronglyMeasurable (F' 0) μ := by
    have hD : Measurable (fun A => PeriodicEndpointScore.direction U W (q A)) := by
      simpa only [PeriodicEndpointScore.direction,Function.comp_def] using
        (PeriodicEndpointScore.traceSum_measurable (PeriodicEndpointScore.left (Real.pi/2) U)
          (PeriodicEndpointScore.right (Real.pi/2) W)).comp hq
    have he : F' 0=(fun A => f A*(β*PeriodicEndpointScore.direction U W (q A))) := by
      funext A
      simp only [F',PeriodicEndpointScore.phase,PeriodicEndpointScore.phaseSlope,
        PeriodicEndpointScore.direction,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,mul_zero,
        one_mul,zero_add,add_zero,Real.exp_zero,mul_one,neg_zero]
    rw [he]
    exact (hf.mul (hD.const_mul β)).aestronglyMeasurable
  have hbound : ∀ᵐ A ∂μ,∀ h∈Set.Ioo (-1:ℝ) 1,‖F' h A‖≤M*Real.exp (1152*|β|)*(768*|β|) := by
    filter_upwards with A h _
    have he : Real.exp (PeriodicEndpointScore.phase β U W h (q A))≤Real.exp (1152*|β|) :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans (PeriodicEndpointScore.phase_bound β U W h (q A)))
    change ‖f A*Real.exp (PeriodicEndpointScore.phase β U W h (q A))*
      PeriodicEndpointScore.phaseSlope β U W h (q A)‖≤_
    rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hfb A) he (Real.exp_pos _).le hM)
      (PeriodicEndpointScore.phaseSlope_bound β U W h (q A)) (abs_nonneg _)
      (mul_nonneg hM (Real.exp_pos _).le)
  have hdiff : ∀ᵐ A ∂μ,∀ h∈Set.Ioo (-1:ℝ) 1,HasDerivAt (F · A) (F' h A) h := by
    filter_upwards with A h _
    have hd := (PeriodicEndpointScore.phase_hasDerivAt β U W h (q A)).exp.const_mul (f A)
    simpa only [F,F',Function.comp_def,mul_assoc] using hd
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) hint hdmeas hbound (integrable_const _) hdiff
  change HasDerivAt (fun h => ∫ A,f A*Real.exp (PeriodicEndpointScore.phase β U W h (q A)) ∂μ) _ 0
  simpa only [F,F',PeriodicEndpointScore.phase,PeriodicEndpointScore.phaseSlope,
    PeriodicEndpointScore.direction,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,mul_zero,
    one_mul,zero_add,add_zero,Real.exp_zero,mul_one,neg_zero] using hd

/-- Actual normalized conditional-row derivative, with both coefficient channels
of the nonlinear endpoint curve retained until differentiation. -/
theorem kernel_expectation_derivative (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e)
    (f : SU2 → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ A,|f A|≤M) :
    HasDerivAt (fun h => ∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β
      (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W) r)
      ((∫ A,f A*(β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)-
        (∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)*
          (∫ A,β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))
            ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)) 0 := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hn := rowWeighted_derivative e β U W r f hf M hM hfb
  have hd := rowWeighted_derivative e β U W r (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  have hz : rowWeighted e β U W r (fun _ => 1) 0=1 := by rw [rowWeighted_zero]; simp
  have h := hn.div hd (by rw [hz]; norm_num)
  simp only [rowWeighted_zero,hz,one_mul,mul_one,one_pow,div_one] at h
  convert h using 1
  funext t
  exact rotated_kernel_integral e β U W r f t

private theorem direction_row_integrable (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) :
    Integrable (fun A => PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))
      (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hm : Measurable (fun A => PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))) :=
    by
      simpa only [PeriodicEndpointScore.direction,Function.comp_def,id_eq] using
        (PeriodicEndpointScore.traceSum_measurable (PeriodicEndpointScore.left (Real.pi/2) U)
          (PeriodicEndpointScore.right (Real.pi/2) W)).comp
          ((PeriodicLinkDisintegration.split e).symm.measurable.comp (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable 384
  filter_upwards with A
  change ‖PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))‖≤384
  simpa only [PeriodicEndpointScore.direction,Real.norm_eq_abs] using
    PeriodicEndpointScore.traceSum_bound _ _ ((PeriodicLinkDisintegration.split e).symm (r,A))

private theorem linkInnovation_direction (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e) (A : SU2) :
    linkInnovation e β U W r A=β*(PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))-
      ∫ B,PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,B))
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  let c : ℝ := -β*(∫ q,PeriodicEndpointScore.direction U W q ∂PeriodicAugmentedBridge.law β U W)
  have hs (B : SU2) : source e β U W (r,B)=
      β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,B))+c := by
    unfold source PeriodicEndpointScore.score
    dsimp only [c]
    ring
  unfold linkInnovation restScore
  simp_rw [hs]
  rw [integral_add ((direction_row_integrable e β U W r).const_mul β) (integrable_const _),
    integral_const_mul,integral_const,probReal_univ,one_smul]
  ring

/-- The centered link field IS the derivative of the actual conditional kernel. -/
theorem kernel_expectation_score (β : ℝ) (U W : State) (r : PeriodicLinkDisintegration.Rest e)
    (f : SU2 → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ A,|f A|≤M) :
    HasDerivAt (fun h => ∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β
      (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W) r)
      (∫ A,f A*linkInnovation e β U W r A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) 0 := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have h := kernel_expectation_derivative e β U W r f hf M hM hfb
  have hfi : Integrable f (PeriodicLinkDisintegration.conditionalKernel e β U W r) :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ (fun A => by
      simpa only [Real.norm_eq_abs] using hfb A))
  have hdi : Integrable (fun A => f A*(β*PeriodicEndpointScore.direction U W
      ((PeriodicLinkDisintegration.split e).symm (r,A))))
      (PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
    have hm : Measurable (fun A => PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))) :=
      by
        simpa only [PeriodicEndpointScore.direction,Function.comp_def,id_eq] using
          (PeriodicEndpointScore.traceSum_measurable (PeriodicEndpointScore.left (Real.pi/2) U)
            (PeriodicEndpointScore.right (Real.pi/2) W)).comp
            ((PeriodicLinkDisintegration.split e).symm.measurable.comp (measurable_const.prodMk measurable_id))
    apply Integrable.of_bound (hf.mul (hm.const_mul β)).aestronglyMeasurable (M*(|β| *384))
    filter_upwards with A
    change ‖f A*(β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have hD : |PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))|≤384 := by
      simpa only [PeriodicEndpointScore.direction] using PeriodicEndpointScore.traceSum_bound
        (PeriodicEndpointScore.left (Real.pi/2) U) (PeriodicEndpointScore.right (Real.pi/2) W)
        ((PeriodicLinkDisintegration.split e).symm (r,A))
    exact mul_le_mul (hfb A) (mul_le_mul_of_nonneg_left hD
      (abs_nonneg β)) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM
  have he : (∫ A,f A*linkInnovation e β U W r A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
      (∫ A,f A*(β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)-
        (∫ A,f A ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)*
          (∫ A,β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A))
            ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
    have hp (A : SU2) : f A*linkInnovation e β U W r A=
        f A*(β*PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,A)))-
        f A*(β*∫ B,PeriodicEndpointScore.direction U W ((PeriodicLinkDisintegration.split e).symm (r,B))
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) := by
      rw [linkInnovation_direction]
      ring
    simp_rw [hp]
    rw [integral_sub hdi (hfi.mul_const _),integral_mul_const,integral_const_mul]
  rw [he]
  exact h

theorem rest_preserving (β : ℝ) (U W : State) :
    MeasurePreserving (fun q => ((PeriodicLinkDisintegration.split e) q).1)
      (PeriodicAugmentedBridge.law β U W) (PeriodicLinkDisintegration.marginal e β U W) := by
  refine ⟨measurable_fst.comp (PeriodicLinkDisintegration.split e).measurable,?_⟩
  change Measure.map (Prod.fst ∘ (PeriodicLinkDisintegration.split e)) (PeriodicAugmentedBridge.law β U W)=_
  rw [← Measure.map_map measurable_fst (PeriodicLinkDisintegration.split e).measurable]
  exact PeriodicLinkDisintegration.actual_rest_marginal e β U W

theorem rest_integral (β : ℝ) (U W : State) (f : PeriodicLinkDisintegration.Rest e → ℝ) (hf : Measurable f) :
    (∫ r,f r ∂PeriodicLinkDisintegration.marginal e β U W)=
      ∫ q,f (((PeriodicLinkDisintegration.split e) q).1) ∂PeriodicAugmentedBridge.law β U W := by
  rw [← (rest_preserving e β U W).map_eq,
    integral_map (rest_preserving e β U W).measurable.aemeasurable hf.aestronglyMeasurable]

theorem restScore_memLp (β : ℝ) (U W : State) :
    MemLp (restScore e β U W) 2 (PeriodicLinkDisintegration.marginal e β U W) := by
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  apply MemLp.of_bound (restScore_measurable e β U W).aestronglyMeasurable (768*|β|)
  filter_upwards with r
  simpa only [Real.norm_eq_abs] using restScore_bound e β U W r

private theorem innovation_measurable (β : ℝ) (U W : State) :
    Measurable (fun z : PeriodicLinkDisintegration.Rest e × SU2 => linkInnovation e β U W z.1 z.2) := by
  unfold linkInnovation
  exact (source_measurable e β U W).sub ((restScore_measurable e β U W).comp measurable_fst)

theorem linkInnovation_joint_memLp (β : ℝ) (U W : State) :
    MemLp (fun z : PeriodicLinkDisintegration.Rest e × SU2 => linkInnovation e β U W z.1 z.2)
      2 (PeriodicLinkDisintegration.joint e β U W) := by
  letI := PeriodicLinkDisintegration.joint_probability e β U W
  apply MemLp.of_bound (innovation_measurable e β U W).aestronglyMeasurable (4*|β|)
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using linkInnovation_bound e β U W z.1 z.2

private theorem split_integral (β : ℝ) (U W : State) (F : PeriodicLinkDisintegration.Rest e × SU2 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ z,|F z|≤C) :
    (∫ q,F ((PeriodicLinkDisintegration.split e) q) ∂PeriodicAugmentedBridge.law β U W)=
      ∫ r,∫ A,F (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r
        ∂PeriodicLinkDisintegration.marginal e β U W := by
  letI := PeriodicLinkDisintegration.joint_probability e β U W
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  have hi : Integrable F (PeriodicLinkDisintegration.joint e β U W) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hC z))
  rw [PeriodicLinkDisintegration.factorization] at hi
  have mp : MeasurePreserving (PeriodicLinkDisintegration.split e) (PeriodicAugmentedBridge.law β U W)
      ((PeriodicAugmentedBridge.law β U W).map (PeriodicLinkDisintegration.split e)) :=
    ⟨(PeriodicLinkDisintegration.split e).measurable,rfl⟩
  have h := mp.integral_comp' F
  rw [PeriodicLinkDisintegration.actual_factorization] at h
  exact h.trans (Measure.integral_compProd hi)

/-- Actual score pairing with arbitrary bounded rest observables. -/
theorem rest_pairing (β : ℝ) (U W : State) (f : PeriodicLinkDisintegration.Rest e → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ r,|f r|≤M) :
    (∫ q,f (((PeriodicLinkDisintegration.split e) q).1)*PeriodicEndpointScore.score β U W q
      ∂PeriodicAugmentedBridge.law β U W)=
      ∫ r,f r*restScore e β U W r ∂PeriodicLinkDisintegration.marginal e β U W := by
  let F := fun z : PeriodicLinkDisintegration.Rest e × SU2 => f z.1*source e β U W z
  have hF : Measurable F := (hf.comp measurable_fst).mul (source_measurable e β U W)
  have hB (z : PeriodicLinkDisintegration.Rest e × SU2) : |F z|≤M*(768*|β|) := by
    change |f z.1*source e β U W z|≤_
    rw [abs_mul]
    exact mul_le_mul (hb z.1) (source_bound e β U W z.1 z.2) (abs_nonneg _) hM
  have h := split_integral e β U W F hF _ hB
  calc
    _ = ∫ q,F ((PeriodicLinkDisintegration.split e) q) ∂PeriodicAugmentedBridge.law β U W := by
      apply integral_congr_ae
      filter_upwards with q
      simp only [F,source,MeasurableEquiv.symm_apply_apply]
    _ = _ := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      change (∫ A,f r*source e β U W (r,A)
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=f r*restScore e β U W r
      rw [integral_const_mul]
      rfl

/-- The rest conditional mean IS the actual marginal-law endpoint derivative. -/
theorem marginal_expectation_score (β : ℝ) (U W : State) (f : PeriodicLinkDisintegration.Rest e → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ r,|f r|≤M) :
    HasDerivAt (fun h => ∫ r,f r ∂PeriodicLinkDisintegration.marginal e β
      (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W))
      (∫ r,f r*restScore e β U W r ∂PeriodicLinkDisintegration.marginal e β U W) 0 := by
  have h := PeriodicEndpointScore.expectation_score β U W
    (fun q => f (((PeriodicLinkDisintegration.split e) q).1))
    (hf.comp (measurable_fst.comp (PeriodicLinkDisintegration.split e).measurable)) M hM
    (fun q => hb (((PeriodicLinkDisintegration.split e) q).1))
  rw [rest_pairing e β U W f hf M hM hb] at h
  convert h using 1
  funext t
  exact rest_integral e β (PeriodicEndpointScore.left t U) (PeriodicEndpointScore.right t W) f hf

/-- Actual native Fisher split after ANY measurable rest cutoff. No response
channel is discarded, and all integrations use the original joint/marginal. -/
theorem cut_fisher (β : ℝ) (U W : State) (S : Set (PeriodicLinkDisintegration.Rest e))
    (hS : MeasurableSet S) :
    (∫ z,((Prod.fst : PeriodicLinkDisintegration.Rest e × SU2 → PeriodicLinkDisintegration.Rest e) ⁻¹' S).indicator
      (fun z => (source e β U W z)^2) z ∂PeriodicLinkDisintegration.joint e β U W)=
      (∫ r,S.indicator (fun r => ∫ A,(linkInnovation e β U W r A)^2
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) r ∂PeriodicLinkDisintegration.marginal e β U W)+
      (∫ r,S.indicator (fun r => (restScore e β U W r)^2) r ∂PeriodicLinkDisintegration.marginal e β U W) := by
  letI := PeriodicLinkDisintegration.joint_probability e β U W
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  let E : Set (PeriodicLinkDisintegration.Rest e × SU2) := Prod.fst ⁻¹' S
  let F := E.indicator (fun z => (source e β U W z)^2)
  have hF : Measurable F := (source_measurable e β U W |>.pow_const 2).indicator (measurable_fst hS)
  have hB (z : PeriodicLinkDisintegration.Rest e × SU2) : |F z|≤(768*|β|)^2 := by
    by_cases hz : z∈E
    · change |E.indicator (fun z => (source e β U W z)^2) z|≤_
      rw [Set.indicator_of_mem hz,abs_of_nonneg (sq_nonneg _)]
      have hb := source_bound e β U W z.1 z.2
      nlinarith [abs_nonneg (source e β U W z),sq_abs (source e β U W z)]
    · change |E.indicator (fun z => (source e β U W z)^2) z|≤_
      rw [Set.indicator_of_notMem hz,abs_zero]
      exact sq_nonneg _
  have hi : Integrable F (PeriodicLinkDisintegration.joint e β U W) :=
    Integrable.of_bound hF.aestronglyMeasurable _ (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hB z))
  have hl := (linkInnovation_joint_memLp e β U W).integrable_sq
  rw [PeriodicLinkDisintegration.factorization] at hl
  have hli : Integrable (fun r => ∫ A,(linkInnovation e β U W r A)^2
      ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) (PeriodicLinkDisintegration.marginal e β U W) := by
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,sq_abs] using
      ((Measure.integrable_compProd_iff hl.aestronglyMeasurable).mp hl).2
  change (∫ z,F z ∂PeriodicLinkDisintegration.joint e β U W)=_
  rw [PeriodicLinkDisintegration.factorization] at hi ⊢
  rw [Measure.integral_compProd hi]
  have hrow (r : PeriodicLinkDisintegration.Rest e) :
      (∫ A,F (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
        S.indicator (fun r => ∫ A,(linkInnovation e β U W r A)^2
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r) r+
        S.indicator (fun r => (restScore e β U W r)^2) r := by
    by_cases hr : r∈S
    · have hp (A : SU2) : F (r,A)=(source e β U W (r,A))^2 :=
        Set.indicator_of_mem (show (r,A)∈E from hr) _
      simp_rw [hp]
      rw [Set.indicator_of_mem hr,Set.indicator_of_mem hr]
      exact row_fisher e β U W r
    · have hp (A : SU2) : F (r,A)=0 :=
        Set.indicator_of_notMem (show (r,A)∉E from hr) _
      simp_rw [hp]
      rw [integral_zero,Set.indicator_of_notMem hr,Set.indicator_of_notMem hr,zero_add]
  simp_rw [hrow]
  exact integral_add (hli.indicator hS) ((restScore_memLp e β U W).integrable_sq.indicator hS)

def badLinkEnergy (β : ℝ) (U W : State) : ℝ :=
  ∫ r,PeriodicCancellingRestTail.restBad.indicator
    (fun r => ∫ A,(linkInnovation PeriodicCancellingBoundaryResponse.edge β U W r A)^2
      ∂PeriodicLinkDisintegration.conditionalKernel PeriodicCancellingBoundaryResponse.edge β U W r) r
        ∂PeriodicLinkDisintegration.marginal PeriodicCancellingBoundaryResponse.edge β U W

def badRestEnergy (β : ℝ) (U W : State) : ℝ :=
  ∫ r,PeriodicCancellingRestTail.restBad.indicator
    (fun r => (restScore PeriodicCancellingBoundaryResponse.edge β U W r)^2) r
      ∂PeriodicLinkDisintegration.marginal PeriodicCancellingBoundaryResponse.edge β U W

/-- Both actual conditional derivative channels account for ALL of the existing
bad-event score energy, under the true selected-link disintegration. -/
theorem badEnergy_split (β : ℝ) (U W : State) :
    PeriodicEndpointScore.badEnergy β U W=badLinkEnergy β U W+badRestEnergy β U W := by
  let e0 := PeriodicCancellingBoundaryResponse.edge
  let E : Set (PeriodicLinkDisintegration.Rest e0 × SU2) := Prod.fst ⁻¹' PeriodicCancellingRestTail.restBad
  let F := E.indicator (fun z => (source e0 β U W z)^2)
  have hc (q : PeriodicAugmentedBridge.Space) :
      ((PeriodicLinkDisintegration.split e0) q).1∈PeriodicCancellingRestTail.restBad ↔
        q.1∈PeriodicCancellingRestTail.bad := by
    change PeriodicLinkDisintegration.baseField e0 (((PeriodicLinkDisintegration.split e0) q).1)
      ∈PeriodicCancellingRestTail.bad ↔ q.1∈PeriodicCancellingRestTail.bad
    have hv : Function.update
        (PeriodicLinkDisintegration.baseField e0 (((PeriodicLinkDisintegration.split e0) q).1))
        e0 (((PeriodicLinkDisintegration.split e0) q).2)=q.1 :=
      congrArg Prod.fst ((PeriodicLinkDisintegration.assemble e0 _ _).symm.trans
        ((PeriodicLinkDisintegration.split e0).symm_apply_apply q))
    rw [← hv,PeriodicCancellingRestTail.bad_update]
  have hL : (∫ q,F ((PeriodicLinkDisintegration.split e0) q) ∂PeriodicAugmentedBridge.law β U W)=
      PeriodicEndpointScore.badEnergy β U W := by
    unfold PeriodicEndpointScore.badEnergy
    apply integral_congr_ae
    filter_upwards with q
    change E.indicator (fun z => (source e0 β U W z)^2) ((PeriodicLinkDisintegration.split e0) q)=_
    by_cases hr : ((PeriodicLinkDisintegration.split e0) q).1∈PeriodicCancellingRestTail.restBad
    · rw [Set.indicator_of_mem (show (PeriodicLinkDisintegration.split e0) q∈E from hr),
        Set.indicator_of_mem (show q∈(fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad from (hc q).mp hr)]
      simp only [source,MeasurableEquiv.symm_apply_apply]
    · rw [Set.indicator_of_notMem (show (PeriodicLinkDisintegration.split e0) q∉E from hr),
        Set.indicator_of_notMem (show q∉(fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad from fun h => hr ((hc q).mpr h))]
  have mp : MeasurePreserving (PeriodicLinkDisintegration.split e0) (PeriodicAugmentedBridge.law β U W)
      ((PeriodicAugmentedBridge.law β U W).map (PeriodicLinkDisintegration.split e0)) :=
    ⟨(PeriodicLinkDisintegration.split e0).measurable,rfl⟩
  have h := mp.integral_comp' F
  rw [PeriodicLinkDisintegration.split_augmented_law] at h
  rw [hL] at h
  exact h.trans (cut_fisher e0 β U W PeriodicCancellingRestTail.restBad PeriodicCancellingRestTail.restBad_measurable)

theorem bad_sum_measurable (β : ℝ) :
    Measurable (fun p : State × State => badLinkEnergy β p.1 p.2+badRestEnergy β p.1 p.2) := by
  simpa only [← badEnergy_split] using PeriodicEndpointScore.badEnergy_measurable β

/-- The combined actual conditional score energies inherit the correct
stationary TWO-step endpoint average. No fixed-rest contraction follows. -/
theorem averaged_bad_sum {β : ℝ} (hb : 16777216≤β) (g : PeriodicSlabGround.GroundData β) :
    (∫ U,∫ W,(badLinkEnergy β U W+badRestEnergy β U W)
      ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary)≤
      (768*|β|)^2*(PeriodicGroundHaarScale.upperConstant/
        PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-β) := by
  simp_rw [← badEnergy_split]
  exact PeriodicEndpointScore.averaged_badEnergy hb g

theorem averaged_bad_sum_tendsto (g : ∀ β : ℝ,PeriodicSlabGround.GroundData β) :
    Tendsto (fun β => ∫ U,∫ W,(badLinkEnergy β U W+badRestEnergy β U W)
      ∂(((g β).transition ∘ₖ (g β).transition) U) ∂(g β).stationary) atTop (𝓝 0) := by
  simpa only [← badEnergy_split] using PeriodicEndpointScore.averaged_badEnergy_tendsto g

/-- Exact TWO-channel reconstruction of the actual endpoint response for bounded
joint observables. The conditional rest response is part of the formula. -/
theorem joint_expectation_reconstruction (β : ℝ) (U W : State)
    (F : PeriodicLinkDisintegration.Rest e × SU2 → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0≤M) (hb : ∀ z,|F z|≤M) :
    HasDerivAt (fun h => ∫ q,F ((PeriodicLinkDisintegration.split e) q)
      ∂PeriodicAugmentedBridge.law β (PeriodicEndpointScore.left h U) (PeriodicEndpointScore.right h W))
      ((∫ r,∫ A,F (r,A)*linkInnovation e β U W r A
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r ∂PeriodicLinkDisintegration.marginal e β U W)+
       (∫ r,(∫ A,F (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)*restScore e β U W r
          ∂PeriodicLinkDisintegration.marginal e β U W)) 0 := by
  let G1 := fun z : PeriodicLinkDisintegration.Rest e × SU2 => F z*linkInnovation e β U W z.1 z.2
  let G2 := fun z : PeriodicLinkDisintegration.Rest e × SU2 => F z*restScore e β U W z.1
  have hm1 : Measurable G1 := hF.mul (innovation_measurable e β U W)
  have hm2 : Measurable G2 := hF.mul ((restScore_measurable e β U W).comp measurable_fst)
  have hb1 (z : PeriodicLinkDisintegration.Rest e × SU2) : |G1 z|≤M*(4*|β|) := by
    change |F z*linkInnovation e β U W z.1 z.2|≤_
    rw [abs_mul]
    exact mul_le_mul (hb z) (linkInnovation_bound e β U W z.1 z.2) (abs_nonneg _) hM
  have hb2 (z : PeriodicLinkDisintegration.Rest e × SU2) : |G2 z|≤M*(768*|β|) := by
    change |F z*restScore e β U W z.1|≤_
    rw [abs_mul]
    exact mul_le_mul (hb z) (restScore_bound e β U W z.1) (abs_nonneg _) hM
  have hi1 : Integrable (fun q => G1 ((PeriodicLinkDisintegration.split e) q))
      (PeriodicAugmentedBridge.law β U W) :=
    Integrable.of_bound (hm1.comp (PeriodicLinkDisintegration.split e).measurable).aestronglyMeasurable
      _ (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using hb1 ((PeriodicLinkDisintegration.split e) q)))
  have hi2 : Integrable (fun q => G2 ((PeriodicLinkDisintegration.split e) q))
      (PeriodicAugmentedBridge.law β U W) :=
    Integrable.of_bound (hm2.comp (PeriodicLinkDisintegration.split e).measurable).aestronglyMeasurable
      _ (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using hb2 ((PeriodicLinkDisintegration.split e) q)))
  have h := PeriodicEndpointScore.expectation_score β U W
    (fun q => F ((PeriodicLinkDisintegration.split e) q)) (hF.comp (PeriodicLinkDisintegration.split e).measurable)
    M hM (fun q => hb ((PeriodicLinkDisintegration.split e) q))
  have hc : (∫ q,F ((PeriodicLinkDisintegration.split e) q)*PeriodicEndpointScore.score β U W q
      ∂PeriodicAugmentedBridge.law β U W)=
      ((∫ r,∫ A,F (r,A)*linkInnovation e β U W r A
        ∂PeriodicLinkDisintegration.conditionalKernel e β U W r ∂PeriodicLinkDisintegration.marginal e β U W)+
       (∫ r,(∫ A,F (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)*restScore e β U W r
          ∂PeriodicLinkDisintegration.marginal e β U W)) := by
    calc
      _ = (∫ q,G1 ((PeriodicLinkDisintegration.split e) q) ∂PeriodicAugmentedBridge.law β U W)+
          (∫ q,G2 ((PeriodicLinkDisintegration.split e) q) ∂PeriodicAugmentedBridge.law β U W) := by
        rw [← integral_add hi1 hi2]
        apply integral_congr_ae
        filter_upwards with q
        have hs : PeriodicEndpointScore.score β U W q=
            linkInnovation e β U W (((PeriodicLinkDisintegration.split e) q).1)
              (((PeriodicLinkDisintegration.split e) q).2)+
            restScore e β U W (((PeriodicLinkDisintegration.split e) q).1) := by
          unfold linkInnovation
          rw [sub_add_cancel]
          unfold source
          have he : ((((PeriodicLinkDisintegration.split e) q).1),(((PeriodicLinkDisintegration.split e) q).2))=
              (PeriodicLinkDisintegration.split e) q := by
            cases hq : (PeriodicLinkDisintegration.split e) q
            rfl
          rw [he,MeasurableEquiv.symm_apply_apply]
        dsimp only [G1,G2]
        rw [hs,mul_add]
      _ = _ := by
        rw [split_integral e β U W G1 hm1 _ hb1,split_integral e β U W G2 hm2 _ hb2]
        apply congrArg (fun y => (∫ r,∫ A,F (r,A)*linkInnovation e β U W r A
          ∂PeriodicLinkDisintegration.conditionalKernel e β U W r ∂PeriodicLinkDisintegration.marginal e β U W)+y)
        apply integral_congr_ae
        filter_upwards with r
        change (∫ A,F (r,A)*restScore e β U W r ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)=
          (∫ A,F (r,A) ∂PeriodicLinkDisintegration.conditionalKernel e β U W r)*restScore e β U W r
        rw [integral_mul_const]
  rw [hc] at h
  exact h
end OperatorDerivativeRewrite.Foundation.PeriodicConditionalEndpointScore
