import Foundation.PeriodicGroundMass
import Foundation.SU2HaarSmallCap
import Foundation.FourCubeBoundaryCoercivity
import Foundation.PeriodicTemporalConcentration

/-!
# Quantitative Haar blocks for the actual periodic Wilson transfer

Reuse the verified SU(2) cap mass and the actual positive-ground block estimate.
All 192 spatial links and all 64 temporal gauge links are integrated. The
coarse positive eigenvalue bound has power beta^(-384); it is not sharp and
does not control a normalized local variance quotient or a physical mass gap.
The true stationary and joint-energy tail estimates retain their different
eigenvalue powers and do not replace the stationary law by spatial Gibbs.
-/

noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.PeriodicPolynomialGround
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open SU2HaarSmallCap FourCubePinnedCoercivity
attribute [local irreducible] PeriodicWilsonSlab.kernel boundaryHaar gaugeHaar

def boundaryBox (t : ℝ) : Set State := Set.univ.pi (fun _ : SpatialEdge => cap t)
def temporalBox (t : ℝ) : Set Gauge := Set.univ.pi (fun _ : SpatialVertex => cap t)

theorem boundaryBox_measurable (t : ℝ) : MeasurableSet (boundaryBox t) :=
  MeasurableSet.univ_pi (fun _ => cap_measurable t)
theorem temporalBox_measurable (t : ℝ) : MeasurableSet (temporalBox t) :=
  MeasurableSet.univ_pi (fun _ => cap_measurable t)

theorem boundary_mass (t : ℝ) : boundaryHaar.real (boundaryBox t)=(law.real (cap t))^192 := by
  change (boundaryHaar (boundaryBox t)).toReal=(law (cap t)).toReal^192
  simp [boundaryHaar,boundaryBox,Measure.pi_pi,ENNReal.toReal_prod,Finset.prod_const,
    Finset.card_univ,edge_count,ENNReal.toReal_pow]
theorem temporal_mass (t : ℝ) : gaugeHaar.real (temporalBox t)=(law.real (cap t))^64 := by
  change (gaugeHaar (temporalBox t)).toReal=(law (cap t)).toReal^64
  simp [gaugeHaar,temporalBox,Measure.pi_pi,ENNReal.toReal_prod,Finset.prod_const,
    Finset.card_univ,SpatialVertex,Fintype.card_fun,ENNReal.toReal_pow]

private theorem four_defect (U V W Z : SU2) :
    defect (U*V*W⁻¹*Z⁻¹) ≤ 9*(defect U+defect V+defect W+defect Z) := by
  have h1 := FourCubeBoundaryCoercivity.defect_mul (U*V) (W⁻¹*Z⁻¹)
  have h2 := FourCubeBoundaryCoercivity.defect_mul U V
  have h3 := FourCubeBoundaryCoercivity.defect_mul W⁻¹ Z⁻¹
  rw [defect_inv,defect_inv] at h3
  have he : U*V*W⁻¹*Z⁻¹=(U*V)*(W⁻¹*Z⁻¹) := by group
  rw [he]
  linarith

private theorem spatial_upper (t : ℝ) (U : State) (hU : ∀ e,defect (U e) ≤ 3*t^2) :
    spatialAction U ≤ 20736*t^2 := by
  have hp (p : SpatialFace) : defect (spatialWord U p) ≤ 108*t^2 := by
    unfold spatialWord
    have h := four_defect (U (p.val.1,p.val.2.1))
      (U (shift p.val.1 p.val.2.1,p.val.2.2))
      (U (shift p.val.1 p.val.2.2,p.val.2.1)) (U (p.val.1,p.val.2.2))
    linarith [hU (p.val.1,p.val.2.1),hU (shift p.val.1 p.val.2.1,p.val.2.2),
      hU (shift p.val.1 p.val.2.2,p.val.2.1),hU (p.val.1,p.val.2.2)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  simp only [Finset.sum_const,Finset.card_univ,face_count,nsmul_eq_mul] at h
  change (∑ p : SpatialFace,defect (spatialWord U p)) ≤ _
  convert h using 1 <;> ring

private theorem temporal_upper (t : ℝ) (U V : State) (g : Gauge)
    (hU : ∀ e,defect (U e) ≤ 3*t^2) (hV : ∀ e,defect (V e) ≤ 3*t^2)
    (hg : ∀ v,defect (g v) ≤ 3*t^2) : temporalAction U V g ≤ 20736*t^2 := by
  have he (e : SpatialEdge) : defect (temporalWord U V g e) ≤ 108*t^2 := by
    have h := four_defect (U e) (g (shift e.1 e.2)) (V e) (g e.1)
    change defect (temporalWord U V g e) ≤ _ at h
    linarith [hU e,hV e,hg (shift e.1 e.2),hg e.1]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => he e)
  simp only [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul] at h
  change (∑ e : SpatialEdge,defect (temporalWord U V g e)) ≤ _
  convert h using 1 <;> ring

theorem action_cap_upper (t : ℝ) (U V : State) (g : Gauge)
    (hU : U ∈ boundaryBox t) (hV : V ∈ boundaryBox t) (hg : g ∈ temporalBox t) :
    halfAction U V g ≤ 41472*t^2 := by
  have hu (e : SpatialEdge) : defect (U e) ≤ 3*t^2 := hU e (Set.mem_univ e)
  have hv (e : SpatialEdge) : defect (V e) ≤ 3*t^2 := hV e (Set.mem_univ e)
  have ha (v : SpatialVertex) : defect (g v) ≤ 3*t^2 := hg v (Set.mem_univ v)
  have hA := spatial_upper t U hu
  have hB := spatial_upper t V hv
  have hT := temporal_upper t U V g hu hv ha
  unfold halfAction
  linarith

theorem kernel_block (beta t : ℝ) (hb : 0 ≤ beta) (U V : State)
    (hU : U ∈ boundaryBox t) (hV : V ∈ boundaryBox t) :
    (law.real (cap t))^64*Real.exp (-41472*beta*t^2) ≤ kernel beta U V := by
  have hpoint (g : Gauge) (hg : g ∈ temporalBox t) :
      Real.exp (-41472*beta*t^2) ≤ weight beta U V g := by
    have hh := action_cap_upper t U V g hU hV hg
    apply Real.exp_le_exp.mpr
    change -41472*beta*t^2 ≤ -beta*halfAction U V g
    nlinarith [mul_le_mul_of_nonneg_left hh hb]
  have hi := setIntegral_mono_on (integrable_const (Real.exp (-41472*beta*t^2))).integrableOn
    (weight_integrable beta U V).integrableOn (temporalBox_measurable t) hpoint
  rw [setIntegral_const,smul_eq_mul,temporal_mass] at hi
  have hj := setIntegral_le_integral (s := temporalBox t) (weight_integrable beta U V)
    (ae_of_all gaugeHaar (fun _ => (Real.exp_pos _).le))
  unfold PeriodicWilsonSlab.kernel
  exact hi.trans hj

variable {beta : ℝ} (d : GroundData beta)

theorem eigenvalue_cap_lower (t : ℝ) (ht : 0<t) (h1 : t ≤ 1) (hb : 0 ≤ beta) :
    (law.real (cap t))^256*Real.exp (-41472*beta*t^2) ≤ d.value := by
  have hp : 0 < law.real (cap t) :=
    (mul_pos (by positivity : 0 < 1/(4*Real.pi^2)) (pow_pos ht 3)).trans_le (mass_lower t ht.le h1)
  have hm : 0 < boundaryHaar.real (boundaryBox t) := by rw [boundary_mass]; exact pow_pos hp 192
  have h := PeriodicGroundMass.eigenvalue_block_lower d (boundaryBox t) (boundaryBox_measurable t) hm
    ((law.real (cap t))^64*Real.exp (-41472*beta*t^2)) (fun U hU V hV => kernel_block beta t hb U V hU hV)
  rw [boundary_mass] at h
  convert h using 1 <;> ring

def lowerConstant : ℝ := (1/(4*Real.pi^2))^256*Real.exp (-41472)
theorem lowerConstant_pos : 0 < lowerConstant := by unfold lowerConstant; positivity

theorem eigenvalue_polynomial (t : ℝ) (ht : 0<t) (h1 : t ≤ 1)
    (hb : 0 ≤ beta) (hscale : beta*t^2 ≤ 1) : lowerConstant*t^768 ≤ d.value := by
  have hm := pow_le_pow_left₀
    (mul_nonneg (by positivity : 0 ≤ 1/(4*Real.pi^2)) (pow_nonneg ht.le 3)) (mass_lower t ht.le h1) 256
  have hm' : (1/(4*Real.pi^2))^256*t^768 ≤ (law.real (cap t))^256 := by
    convert hm using 1 <;> ring
  have he : Real.exp (-41472) ≤ Real.exp (-41472*beta*t^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hp := mul_le_mul hm' he (Real.exp_pos (-41472)).le (pow_nonneg measureReal_nonneg 256)
  have h := hp.trans (eigenvalue_cap_lower d t ht h1 hb)
  convert h using 1 <;> unfold lowerConstant <;> ring

theorem eigenvalue_beta (hb : 1 ≤ beta) : lowerConstant/beta^384 ≤ d.value := by
  let t : ℝ := 1/Real.sqrt beta
  have hp : 0<beta := by linarith
  have hs : 0<Real.sqrt beta := Real.sqrt_pos.mpr hp
  have ht : 0<t := div_pos zero_lt_one hs
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hs).mpr (by simpa using Real.sqrt_le_sqrt hb)
  have ht2 : t^2=1/beta := by
    dsimp [t]
    rw [div_pow,one_pow,Real.sq_sqrt hp.le]
  have hscale : beta*t^2 ≤ 1 := by rw [ht2,mul_one_div_cancel hp.ne']
  have hpower : t^768=1/beta^384 := by
    calc
      _ = (t^2)^384 := by ring
      _ = _ := by rw [ht2,div_pow,one_pow]
  have h := eigenvalue_polynomial d t ht ht1 hp.le hscale
  rw [hpower] at h
  simpa only [mul_one_div] using h

theorem energy_tail_polynomial (hb : 1 ≤ beta) (eps : ℝ) :
    (PeriodicSlabJoint.tripleLaw d).real {q | eps ≤ PeriodicTemporalConcentration.energy q} ≤
      (beta^384/lowerConstant)*Real.exp (-beta*eps) := by
  have hp : 0<beta := by linarith
  have hc := lowerConstant_pos
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-beta*eps)).le
    (div_pos hc (pow_pos hp 384)) (eigenvalue_beta d hb)
  have h := (PeriodicTemporalConcentration.tail_eigenfactor d hp.le eps).trans hdiv
  convert h using 1 <;> field_simp <;> ring

theorem spatial_tail_polynomial (hb : 1 ≤ beta) (eps : ℝ) :
    d.stationary.real {U | eps ≤ spatialAction U} ≤
      (beta^768/lowerConstant^2)*Real.exp (-beta*eps) := by
  have hp : 0<beta := by linarith
  have hc := lowerConstant_pos
  have hs := pow_le_pow_left₀ (div_pos hc (pow_pos hp 384)).le (eigenvalue_beta d hb) 2
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-beta*eps)).le
    (sq_pos_of_pos (div_pos hc (pow_pos hp 384))) hs
  have h := (PeriodicGroundMass.action_tail_eigenfactor d hp.le eps).trans hdiv
  convert h using 1 <;> field_simp <;> ring

theorem energy_bound (hb : 1 ≤ beta) (eps : ℝ) (he : 0 ≤ eps) :
    (∫ q,PeriodicTemporalConcentration.energy q ∂PeriodicSlabJoint.tripleLaw d) ≤
      eps+768*((beta^384/lowerConstant)*Real.exp (-beta*eps)) := by
  exact (PeriodicTemporalConcentration.energy_from_tail d eps he).trans
    (add_le_add (le_refl eps) (mul_le_mul_of_nonneg_left (energy_tail_polynomial d hb eps)
      (by norm_num : (0 : ℝ) ≤ 768)))

end OperatorDerivativeRewrite.Foundation.PeriodicPolynomialGround
