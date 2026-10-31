import Foundation.PeriodicQuarticNativeObstruction
import Foundation.PeriodicPlaquetteSeamSelection
/-! Center-even native quartic-tail obstructions for the actual Wilson transfer.
Positive three-seam averaging preserves a fixed Rayleigh lower bound (with
factor 1/8), gauge invariance and avoidance of every fixed flat kinetic tube.
The resulting nonzero probes have strictly positive stationary mean. This
removes a center-odd explanation of the tail obstruction, not the separate
centering or physical mass-gap obligations. All laws are the actual finite
periodic lattice ground construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticCenterEven
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicCenterSeam PeriodicGroundSeamParity PeriodicPlaquetteSeamSelection
attribute [local irreducible] boundaryHaar kernel temporalAction
variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance edge_probability : IsProbabilityMeasure (edgeLaw g) := by
  let := g.transition_markov
  unfold edgeLaw
  infer_instance

def average (i : Fin 3) (f : State → ℝ) (U : State) : ℝ := (f U+f (flip i U))/2

theorem flip_commute (i j : Fin 3) (U : State) : flip i (flip j U)=flip j (flip i U) := by
  funext e
  change seam i e*(seam j e*U e)=seam j e*(seam i e*U e)
  rw [← mul_assoc,seam_commute,mul_assoc]

theorem average_measurable (i : Fin 3) (f : State → ℝ) (hf : Measurable f) :
    Measurable (average i f) := (hf.add (hf.comp (flip_measurable i))).div_const 2

theorem average_bound (i : Fin 3) (f : State → ℝ) (B : ℝ) (hb : ∀ U,|f U|≤B) (U : State) :
    |average i f U|≤B := by
  unfold average
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)).trans (by linarith [hb U,hb (flip i U)])

theorem average_nonneg (i : Fin 3) (f : State → ℝ) (hf : ∀ U,0≤f U) (U : State) :
    0≤average i f U := div_nonneg (add_nonneg (hf U) (hf _)) (by norm_num)

theorem average_even (i : Fin 3) (f : State → ℝ) (U : State) : average i f (flip i U)=average i f U := by
  simp only [average,flip_involutive i U]
  ring

theorem average_preserves_even (i j : Fin 3) (f : State → ℝ)
    (hf : ∀ U,f (flip j U)=f U) (U : State) : average i f (flip j U)=average i f U := by
  unfold average
  rw [hf,flip_commute i j,hf]

def square (f : State → ℝ) : ℝ := ∫ U,f U^2 ∂g.stationary
def form (f : State → ℝ) : ℝ := ∫ p : State × State,f p.1*f p.2 ∂edgeLaw g

theorem square_integrable (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ U,|f U|≤B) :
    Integrable (fun U => f U^2) g.stationary := by
  apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (|B|^2)
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((hb U).trans (le_abs_self B)) 2

theorem edge_integrable (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (B C : ℝ) (hb : ∀ U,|f U|≤B) (hc : ∀ U,|h U|≤C) :
    Integrable (fun p : State × State => f p.1*h p.2) (edgeLaw g) := by
  apply Integrable.of_bound ((hf.comp measurable_fst).mul (hh.comp measurable_snd)).aestronglyMeasurable (|B| * |C|)
  filter_upwards with p
  change ‖f p.1*h p.2‖≤|B| * |C|
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((hb _).trans (le_abs_self B)) ((hc _).trans (le_abs_self C)) (abs_nonneg _) (abs_nonneg _)

theorem square_flip (i : Fin 3) (f : State → ℝ) : square g (fun U => f (flip i U))=square g f :=
  stationary_integral_flip g i (fun U => f U^2)

theorem form_flip (i : Fin 3) (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ U,|f U|≤B) :
    form g (fun U => f (flip i U))=form g f := by
  unfold form
  rw [edge_pairing g (fun U => f (flip i U)) (fun U => f (flip i U)) (hf.comp (flip_measurable i)) (hf.comp (flip_measurable i)) B B
    (fun U => hb (flip i U)) (fun U => hb (flip i U)),edge_pairing g f f hf hf B B hb hb]
  change (∫ U,f (flip i U)*transfer g (fun V => f (flip i V)) U ∂g.stationary)=_
  simp_rw [← transfer_flip]
  exact stationary_integral_flip g i (fun U => f U*transfer g f U)

theorem average_square_le (i : Fin 3) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) : square g (average i f)≤square g f := by
  have ha := square_integrable g (average i f) (average_measurable i f hf) B (average_bound i f B hb)
  have h0 := square_integrable g f hf B hb
  have h1 := square_integrable g (fun U => f (flip i U)) (hf.comp (flip_measurable i)) B (fun U => hb _)
  have hp : ∀ U,(average i f U)^2≤(f U^2+f (flip i U)^2)/2 := by
    intro U
    dsimp [average]
    nlinarith [sq_nonneg (f U-f (flip i U))]
  have hi := integral_mono ha ((h0.add h1).div_const 2) hp
  change square g (average i f)≤_ at hi
  simp only [Pi.add_apply] at hi
  rw [integral_div,integral_add h0 h1] at hi
  change square g (average i f)≤(square g f+square g (fun U => f (flip i U)))/2 at hi
  rw [square_flip] at hi
  linarith

theorem average_form_lower (i : Fin 3) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) (hn : ∀ U,0≤f U) : form g f/2≤form g (average i f) := by
  have h0 := edge_integrable g f f hf hf B B hb hb
  have h1 := edge_integrable g (fun U => f (flip i U)) (fun U => f (flip i U))
    (hf.comp (flip_measurable i)) (hf.comp (flip_measurable i)) B B (fun U => hb _) (fun U => hb _)
  have ha := edge_integrable g (average i f) (average i f) (average_measurable i f hf)
    (average_measurable i f hf) B B (average_bound i f B hb) (average_bound i f B hb)
  have hp : ∀ p : State × State,(f p.1*f p.2+f (flip i p.1)*f (flip i p.2))/4≤
      average i f p.1*average i f p.2 := by
    intro p
    dsimp [average]
    nlinarith [mul_nonneg (hn p.1) (hn (flip i p.2)),mul_nonneg (hn (flip i p.1)) (hn p.2)]
  have hi := integral_mono ((h0.add h1).div_const 4) ha hp
  simp only [Pi.add_apply] at hi
  rw [integral_div,integral_add h0 h1] at hi
  change (form g f+form g (fun U => f (flip i U)))/4≤form g (average i f) at hi
  rw [form_flip g i f hf B hb] at hi
  linarith


theorem average_square_lower (i : Fin 3) (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) (hn : ∀ U,0≤f U) : square g f/4≤square g (average i f) := by
  have h0 := square_integrable g f hf B hb
  have ha := square_integrable g (average i f) (average_measurable i f hf) B (average_bound i f B hb)
  have hp : ∀ U,f U^2/4≤average i f U^2 := by
    intro U
    dsimp [average]
    nlinarith [mul_nonneg (hn U) (hn (flip i U)),sq_nonneg (f (flip i U))]
  have hi := integral_mono (h0.div_const 4) ha hp
  simpa only [integral_div,square] using hi

def evenPart (f : State → ℝ) : State → ℝ := average 2 (average 1 (average 0 f))

theorem evenPart_measurable (f : State → ℝ) (hf : Measurable f) : Measurable (evenPart f) :=
  average_measurable 2 _ (average_measurable 1 _ (average_measurable 0 f hf))

theorem evenPart_bound (f : State → ℝ) (B : ℝ) (hb : ∀ U,|f U|≤B) : ∀ U,|evenPart f U|≤B :=
  average_bound 2 _ B (average_bound 1 _ B (average_bound 0 f B hb))

theorem evenPart_nonneg (f : State → ℝ) (hn : ∀ U,0≤f U) : ∀ U,0≤evenPart f U :=
  average_nonneg 2 _ (average_nonneg 1 _ (average_nonneg 0 f hn))

theorem evenPart_even (f : State → ℝ) (i : Fin 3) (U : State) : evenPart f (flip i U)=evenPart f U := by
  fin_cases i
  · exact average_preserves_even 2 0 _ (average_preserves_even 1 0 _ (average_even 0 f)) U
  · exact average_preserves_even 2 1 _ (average_even 1 _) U
  · exact average_even 2 _ U

theorem evenPart_square_le (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ U,|f U|≤B) :
    square g (evenPart f)≤square g f := by
  exact (average_square_le g 2 _ (average_measurable 1 _ (average_measurable 0 f hf)) B
    (average_bound 1 _ B (average_bound 0 f B hb))).trans
    ((average_square_le g 1 _ (average_measurable 0 f hf) B (average_bound 0 f B hb)).trans
      (average_square_le g 0 f hf B hb))

theorem evenPart_square_lower (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) (hn : ∀ U,0≤f U) : square g f/64≤square g (evenPart f) := by
  have h0 := average_square_lower g 0 f hf B hb hn
  have h1 := average_square_lower g 1 _ (average_measurable 0 f hf) B
    (average_bound 0 f B hb) (average_nonneg 0 f hn)
  have h2 := average_square_lower g 2 _ (average_measurable 1 _ (average_measurable 0 f hf)) B
    (average_bound 1 _ B (average_bound 0 f B hb)) (average_nonneg 1 _ (average_nonneg 0 f hn))
  change _≤square g (evenPart f) at h2
  linarith

theorem evenPart_form_lower (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) (hn : ∀ U,0≤f U) : form g f/8≤form g (evenPart f) := by
  have h0 := average_form_lower g 0 f hf B hb hn
  have h1 := average_form_lower g 1 _ (average_measurable 0 f hf) B
    (average_bound 0 f B hb) (average_nonneg 0 f hn)
  have h2 := average_form_lower g 2 _ (average_measurable 1 _ (average_measurable 0 f hf)) B
    (average_bound 1 _ B (average_bound 0 f B hb)) (average_nonneg 1 _ (average_nonneg 0 f hn))
  change _≤form g (evenPart f) at h2
  linarith

theorem flip_gauge (i : Fin 3) (a : Gauge) (U : State) :
    flip i (PeriodicSlabGauge.gaugeAction a U)=PeriodicSlabGauge.gaugeAction a (flip i U) := by
  funext e
  change seam i e*(a e.1*U e*(a (shift e.1 e.2))⁻¹)=a e.1*(seam i e*U e)*(a (shift e.1 e.2))⁻¹
  rw [← mul_assoc,← mul_assoc,seam_commute i e (a e.1)]
  simp only [mul_assoc]

theorem average_invariant (i : Fin 3) (f : State → ℝ)
    (hf : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) (a : Gauge) (U : State) :
    average i f (PeriodicSlabGauge.gaugeAction a U)=average i f U := by
  unfold average
  rw [hf,flip_gauge,hf]

theorem evenPart_invariant (f : State → ℝ)
    (hf : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) (a : Gauge) (U : State) :
    evenPart f (PeriodicSlabGauge.gaugeAction a U)=evenPart f U :=
  average_invariant 2 _ (average_invariant 1 _ (average_invariant 0 f hf)) a U

theorem temporal_simultaneous (i : Fin 3) (U V : State) (a : Gauge) :
    temporalAction (flip i U) (flip i V) a=temporalAction U V a := by
  unfold temporalAction
  simp_rw [PeriodicCenterSeam.temporal_word]

def AvoidsFlat (β M : ℝ) (f : State → ℝ) : Prop :=
  ∀ U V : State,spatialAction V=0 → ∀ a : Gauge,β*temporalAction U V a<M → f U=0

theorem average_avoids (i : Fin 3) (f : State → ℝ) (M : ℝ) (hf : AvoidsFlat β M f) :
    AvoidsFlat β M (average i f) := by
  intro U V hV a hclose
  have h0 := hf U V hV a hclose
  have hV' : spatialAction (flip i V)=0 := (spatial_action i V).trans hV
  have hclose' : β*temporalAction (flip i U) (flip i V) a<M := by rwa [temporal_simultaneous]
  have h1 := hf (flip i U) (flip i V) hV' a hclose'
  simp [average,h0,h1]

theorem evenPart_avoids (f : State → ℝ) (M : ℝ) (hf : AvoidsFlat β M f) :
    AvoidsFlat β M (evenPart f) :=
  average_avoids 2 _ M (average_avoids 1 _ M (average_avoids 0 f M hf))

theorem bounded_memLp (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ U,|f U|≤B) :
    MemLp f 2 g.stationary :=
  MemLp.of_bound hf.aestronglyMeasurable B (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hb U))

theorem native_square (f : State → ℝ) (hm : MemLp f 2 g.stationary) :
    ‖hm.toLp f‖^2=square g f := PeriodicTransferVariation.state_norm_square g f hm

theorem native_form (f : State → ℝ) (hm : MemLp f 2 g.stationary) :
    inner ℝ (operator g (hm.toLp f)) (hm.toLp f)=form g f := by
  rw [operator_pairing]
  apply integral_congr_ae
  have hl := (left_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm)
  have hr := (right_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm)
  filter_upwards [hl,hr] with p hp hq
  change hm.toLp f p.1=f p.1 at hp
  change hm.toLp f p.2=f p.2 at hq
  rw [hp,hq]



theorem evenPart_rayleigh (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U,|f U|≤B) (hn : ∀ U,0≤f U) (c : ℝ) (hc : 0≤c)
    (hform : c*square g f≤form g f) : (c/8)*square g (evenPart f)≤form g (evenPart f) := by
  have hs := mul_le_mul_of_nonneg_left (evenPart_square_le g f hf B hb) hc
  have hp := evenPart_form_lower g f hf B hb hn
  linarith

open PeriodicQuarticNativeObstruction

def centerTrial (t r : ℝ) : State → ℝ := evenPart (trial g (packetRegion t r))

theorem centerTrial_measurable (t r : ℝ) : Measurable (centerTrial g t r) :=
  evenPart_measurable _ (trial_measurable g _ (packetRegion_measurable t r))

theorem centerTrial_bound (t r : ℝ) : ∀ U,|centerTrial g t r U|≤1/g.lower :=
  evenPart_bound _ _ (trial_bound g _)

theorem trial_nonneg (B : Set State) (U : State) : 0≤trial g B U := by
  unfold trial chi
  exact div_nonneg (Set.indicator_nonneg (fun _ _ => by norm_num) _) (g.function_pos U).le

theorem centerTrial_nonneg (t r : ℝ) : ∀ U,0≤centerTrial g t r U :=
  evenPart_nonneg _ (trial_nonneg g _)

theorem centerTrial_even (t r : ℝ) (i : Fin 3) (U : State) :
    centerTrial g t r (flip i U)=centerTrial g t r U := evenPart_even _ i U

theorem centerTrial_invariant (t r : ℝ) (a : Gauge) (U : State) :
    centerTrial g t r (PeriodicSlabGauge.gaugeAction a U)=centerTrial g t r U :=
  evenPart_invariant _ (trial_region_invariant g t r) a U

theorem centerTrial_memLp (t r : ℝ) : MemLp (centerTrial g t r) 2 g.stationary :=
  bounded_memLp g _ (centerTrial_measurable g t r) _ (centerTrial_bound g t r)

def nativeCenter (t r : ℝ) : StateL2 g := (centerTrial_memLp g t r).toLp (centerTrial g t r)

theorem nativeCenter_even (t r : ℝ) (i : Fin 3) :
    ∀ᵐ U ∂g.stationary,nativeCenter g t r (flip i U)=nativeCenter g t r U := by
  have h := MemLp.coeFn_toLp (centerTrial_memLp g t r)
  have hi := (stationary_preserving g i).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h,hi] with U hU hiU
  change nativeCenter g t r U=centerTrial g t r U at hU
  change nativeCenter g t r (flip i U)=centerTrial g t r (flip i U) at hiU
  rw [hU,hiU,centerTrial_even]

theorem nativeCenter_norm_pos (t r : ℝ) (hpos : 0<‖nativeTrial g t r‖) :
    0<‖nativeCenter g t r‖ := by
  have h := evenPart_square_lower g _ (trial_measurable g _ (packetRegion_measurable t r))
    _ (trial_bound g _) (trial_nonneg g _)
  have h0 := native_square g _ (trial_memLp g _ (packetRegion_measurable t r))
  have h1 := native_square g _ (centerTrial_memLp g t r)
  change ‖nativeTrial g t r‖^2=square g _ at h0
  change ‖nativeCenter g t r‖^2=square g (evenPart (trial g (packetRegion t r))) at h1
  rw [← h0,← h1] at h
  nlinarith [norm_nonneg (nativeCenter g t r)]

theorem nativeCenter_lower (t r : ℝ)
    (hform : nativeConstant*‖nativeTrial g t r‖^2≤ inner ℝ (operator g (nativeTrial g t r)) (nativeTrial g t r)) :
    (nativeConstant/8)*‖nativeCenter g t r‖^2≤ inner ℝ (operator g (nativeCenter g t r)) (nativeCenter g t r) := by
  have h0 := native_square g _ (trial_memLp g _ (packetRegion_measurable t r))
  have hF := native_form g _ (trial_memLp g _ (packetRegion_measurable t r))
  change ‖nativeTrial g t r‖^2=_ at h0
  change inner ℝ (operator g (nativeTrial g t r)) (nativeTrial g t r)=_ at hF
  rw [h0,hF] at hform
  unfold nativeCenter
  rw [native_square,native_form]
  exact evenPart_rayleigh g _ (trial_measurable g _ (packetRegion_measurable t r))
    _ (trial_bound g _) (trial_nonneg g _) nativeConstant nativeConstant_pos.le hform

theorem centerTrial_avoids (t r M : ℝ)
    (hsep : ∀ U∈packetRegion t r,∀ V : State,spatialAction V=0 → ∀ a : Gauge,M≤β*temporalAction U V a) :
    AvoidsFlat β M (centerTrial g t r) := by
  apply evenPart_avoids
  intro U V hV a hclose
  have hn : U∉packetRegion t r := by
    intro hu
    exact (not_lt_of_ge (hsep U hu V hV a)) hclose
  simp [trial,chi,hn]

theorem nativeCenter_avoids (t r M : ℝ) (hf : AvoidsFlat β M (centerTrial g t r)) :
    ∀ᵐ U ∂g.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
      β*temporalAction U V a<M → nativeCenter g t r U=0 := by
  filter_upwards [MemLp.coeFn_toLp (centerTrial_memLp g t r)] with U hU
  change nativeCenter g t r U=centerTrial g t r U at hU
  intro V hV a hc
  rw [hU]
  exact hf U V hV a hc

open Filter
open scoped Topology

theorem eventual_even_family : ∀ᶠ x : ℝ in 𝓝[>] 0,∀ q : GroundData (1/x^6),
    0<‖nativeCenter q (x^2) (x^3)‖ ∧
      (nativeConstant/8)*‖nativeCenter q (x^2) (x^3)‖^2≤ inner ℝ
        (operator q (nativeCenter q (x^2) (x^3))) (nativeCenter q (x^2) (x^3)) ∧
      AvoidsFlat (1/x^6) (1/(256*x^2)) (centerTrial q (x^2) (x^3)) := by
  filter_upwards [eventual_native_family] with x hx q
  obtain ⟨hn,hf,_,hsep⟩ := hx q
  exact ⟨nativeCenter_norm_pos q _ _ hn,nativeCenter_lower q _ _ hf,centerTrial_avoids q _ _ _ hsep⟩

theorem arbitrarily_large_even_native (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ t r : ℝ,0<‖nativeCenter q t r‖ ∧
      (nativeConstant/8)*‖nativeCenter q t r‖^2≤ inner ℝ (operator q (nativeCenter q t r)) (nativeCenter q t r) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → nativeCenter q t r U=0) := by
  have hb := coupling_diverges.eventually (eventually_ge_atTop (max M 1))
  have he := flat_distance_diverges.eventually (eventually_ge_atTop M)
  obtain ⟨x,hfamily,hbeta,hescape⟩ := (eventual_even_family.and (hb.and he)).exists
  let q := ground (1/x^6)
  obtain ⟨hn,hf,ha⟩ := hfamily q
  refine ⟨1/x^6,(le_max_right M 1).trans hbeta,(le_max_left M 1).trans hbeta,q,x^2,x^3,hn,hf,?_⟩
  apply nativeCenter_avoids
  intro U V hV a hclose
  exact ha U V hV a (hclose.trans_le hescape)

theorem even_error_lower (t r : ℝ) (hn : 0<‖nativeCenter g t r‖)
    (hf : (nativeConstant/8)*‖nativeCenter g t r‖^2≤ inner ℝ
      (operator g (nativeCenter g t r)) (nativeCenter g t r))
    (Q : StateL2 g →L[ℝ] StateL2 g) (hQ : Q (nativeCenter g t r)=0) :
    nativeConstant/8≤‖operator g-Q‖ := by
  have he : (operator g-Q) (nativeCenter g t r)=operator g (nativeCenter g t r) := by
    rw [sub_apply,hQ,sub_zero]
  have hc := real_inner_le_norm ((operator g-Q) (nativeCenter g t r)) (nativeCenter g t r)
  have ho := ContinuousLinearMap.le_opNorm (operator g-Q) (nativeCenter g t r)
  rw [he] at hc ho
  have hh := hf.trans (hc.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg _)))
  have h : (nativeConstant/8)*‖nativeCenter g t r‖^2≤‖operator g-Q‖*‖nativeCenter g t r‖^2 := by
    convert hh using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp h

theorem arbitrarily_large_even_obstruction (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ t r : ℝ,0<‖nativeCenter q t r‖ ∧
      (∀ i : Fin 3,∀ᵐ U ∂q.stationary,nativeCenter q t r (flip i U)=nativeCenter q t r U) ∧
      (∀ Q : StateL2 q →L[ℝ] StateL2 q,Q (nativeCenter q t r)=0 → nativeConstant/8≤‖operator q-Q‖) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → nativeCenter q t r U=0) := by
  obtain ⟨β,hb,hM,q,t,r,hn,hf,ha⟩ := arbitrarily_large_even_native M
  exact ⟨β,hb,hM,q,t,r,hn,nativeCenter_even q t r,fun Q hQ => even_error_lower q t r hn hf Q hQ,ha⟩


theorem centerTrial_mean_pos (t r : ℝ) (hn : 0<‖nativeCenter g t r‖) :
    0<∫ U,centerTrial g t r U ∂g.stationary := by
  have hi : Integrable (centerTrial g t r) g.stationary :=
    Integrable.of_bound (centerTrial_measurable g t r).aestronglyMeasurable (1/g.lower)
      (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using centerTrial_bound g t r U))
  have hnon := centerTrial_nonneg g t r
  have hle : 0≤∫ U,centerTrial g t r U ∂g.stationary :=
    MeasureTheory.integral_nonneg (f := centerTrial g t r) hnon
  by_contra hp
  have hz : (∫ U,centerTrial g t r U ∂g.stationary)=0 := le_antisymm (le_of_not_gt hp) hle
  have he := (integral_eq_zero_iff_of_nonneg (f := centerTrial g t r) hnon hi).mp hz
  have hs : square g (centerTrial g t r)=0 := by
    unfold square
    calc
      _ = ∫ _ : State,(0 : ℝ) ∂g.stationary := by
        apply integral_congr_ae
        filter_upwards [he] with U hU
        simp [hU]
      _ = 0 := integral_zero _ _
  have hn2 := native_square g _ (centerTrial_memLp g t r)
  change ‖nativeCenter g t r‖^2=_ at hn2
  rw [hs] at hn2
  nlinarith

theorem nativeCenter_mean_pos (t r : ℝ) (hn : 0<‖nativeCenter g t r‖) :
    0<∫ U,nativeCenter g t r U ∂g.stationary := by
  have he := integral_congr_ae (MemLp.coeFn_toLp (centerTrial_memLp g t r))
  change (∫ U,nativeCenter g t r U ∂g.stationary)=(∫ U,centerTrial g t r U ∂g.stationary) at he
  rw [he]
  exact centerTrial_mean_pos g t r hn

end OperatorDerivativeRewrite.Foundation.PeriodicQuarticCenterEven
