import Foundation.FourCubeHaarChannels

/-! Three boundary axes on the existing full72-face cell.
The target is an actual Haar variance difference, not a formal Taylor vertex. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeIntegratedCubic
open QuaternionSU2Representation SU2JointPlaquetteCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex FourCubeChordIncidence
open FourCubeHaarParity FourCubeHaarChannels
attribute [local irreducible] edges upperFaces

def base : Vertex := ![0,0,1,1]
def chosenEdge : Interior := ⟨(base,0),by norm_num [edges,base]⟩
def chosen : Upper := ⟨(chosenEdge.val,2),by norm_num [upperFaces,edges,chosenEdge,base]⟩
def partner : Upper := ⟨(chosenEdge.val,3),by norm_num [upperFaces,edges,chosenEdge,base]⟩

def boundaryData (x y z : ℝ) : Boundary → SU2
  | .inl c => if c.val=(capHigh chosen).val then axis 0 x else
      if c.val=(capLow chosen).val then (axis 2 z)⁻¹ else 1
  | .inr p => if p.val=chosen.val then (axis 1 y)⁻¹ else 1

def fill (b : Boundary → SU2) (s : InteriorState) : FullEdge → SU2
  | .inl e => s e
  | .inr c => b c

def word (b : Boundary → SU2) (p : Upper) : SU2 :=
  b (.inl (capHigh p))*(b (.inr p))⁻¹*(b (.inl (capLow p)))⁻¹

def ribbonChannel (b : Boundary → SU2) (p : Upper) : InteriorState → ℝ :=
  linkProbe (ribbonInterior p) (word b p)

def ribbonSum (b : Boundary → SU2) (s : InteriorState) : ℝ := ∑ p : Upper,ribbonChannel b p s

def cellAction (x y z : ℝ) (s : InteriorState) : ℝ :=
  FourCubeBoundaryCubic.fullAction (fill (boundaryData x y z) s)

theorem fill_measurable (b : Boundary → SU2) : Measurable (fill b) := by
  apply measurable_pi_iff.mpr
  intro e
  cases e with
  | inl e => exact measurable_pi_apply e
  | inr c => exact measurable_const

theorem cellAction_measurable (x y z : ℝ) : Measurable (cellAction x y z) :=
  FourCubeHaarParity.fullAction_measurable.comp (fill_measurable _)

theorem cellAction_bounds (x y z : ℝ) (s : InteriorState) :
    0 ≤ cellAction x y z s ∧ cellAction x y z s ≤ 144 :=
  FourCubeHaarParity.fullAction_bounds _

theorem retained_fill (b : Boundary → SU2) (s : InteriorState) :
    FourCubeBoundaryCubic.retained (fill b s)=coreField s := by
  funext e
  by_cases he : e∈edges <;> simp [FourCubeBoundaryCubic.retained,fill,coreField,he]

theorem ribbon_fill (b : Boundary → SU2) (p : Upper) (s : InteriorState) :
    FourCubeBoundaryCubic.ribbonWord (fill b s) p=s (ribbonInterior p)*word b p := by
  simp [FourCubeBoundaryCubic.ribbonWord,fill,word,mul_assoc]

theorem action_decomposition (b : Boundary → SU2) (s : InteriorState) :
    FourCubeBoundaryCubic.fullAction (fill b s)=internalAction s+48-ribbonSum b s := by
  unfold FourCubeBoundaryCubic.fullAction
  rw [retained_fill]
  simp_rw [ribbon_fill,SU2WilsonConvolution.halfTrace_mul_comm (s (ribbonInterior _))]
  change internalAction s+(∑ p : Upper,(1-ribbonChannel b p s))=_
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,OneSidedBlockRank.upper_card,nsmul_eq_mul,mul_one]
  norm_num [ribbonSum] <;> ring

theorem word_chosen (x y z : ℝ) : word (boundaryData x y z) chosen=axis 0 x*axis 1 y*axis 2 z := by
  norm_num [word,boundaryData,chosen,chosenEdge,base,capHigh,capLow,shifted,
    funext_iff,Fin.forall_fin_succ,Function.update_apply]

theorem word_partner (x y z : ℝ) : word (boundaryData x y z) partner=1 := by
  norm_num [word,boundaryData,chosen,partner,chosenEdge,base,capHigh,capLow,shifted,
    funext_iff,Fin.forall_fin_succ,Function.update_apply]

theorem word_other_y (x y y' z : ℝ) (p : Upper) (hp : p ≠ chosen) :
    word (boundaryData x y z) p=word (boundaryData x y' z) p := by
  have hv : p.val ≠ chosen.val := fun h => hp (Subtype.ext h)
  simp [word,boundaryData,hv]

theorem edge_fiber (p : Upper) : ribbonInterior p=chosenEdge ↔ p=chosen ∨ p=partner := by
  constructor
  · intro he
    have hp : p.val∈upperFaces := p.property
    simp only [upperFaces,Finset.mem_filter,Finset.mem_univ,true_and] at hp
    have hv : p.val.1=chosenEdge.val := congrArg Subtype.val he
    have hh : p.val.1.1 p.val.2=1 := hp.2.2
    rw [hv] at hh
    have hj : p.val.2=2 ∨ p.val.2=3 := by
      generalize hg : p.val.2=j at hh ⊢
      fin_cases j <;> simp_all [chosenEdge,base]
    rcases hj with hj | hj
    · exact Or.inl (Subtype.ext (Prod.ext hv hj))
    · exact Or.inr (Subtype.ext (Prod.ext hv hj))
  · rintro (rfl | rfl) <;> rfl

theorem chosen_edge : ribbonInterior chosen=chosenEdge := rfl
theorem partner_edge : ribbonInterior partner=chosenEdge := rfl

def boundaryGauge (g : FullVertex → SU2) (b : Boundary → SU2) : Boundary → SU2 :=
  fun e => g (OneSidedCapComplex.source (.inr e))*b e*(g (OneSidedCapComplex.target (.inr e)))⁻¹

theorem word_boundaryGauge (g : FullVertex → SU2) (b : Boundary → SU2) (p : Upper) :
    word (boundaryGauge g b) p=
      g (.inl (shifted p.val.1.1 p.val.1.2))*word b p*(g (.inl p.val.1.1))⁻¹ := by
  unfold word boundaryGauge OneSidedCapComplex.source OneSidedCapComplex.target
  change (g (.inl (shifted p.val.1.1 p.val.1.2))*b (.inl (capHigh p))*(g (.inr (capHigh p)))⁻¹)*
    (g (.inr (capLow p))*b (.inr p)*(g (.inr (capHigh p)))⁻¹)⁻¹*
    (g (.inl p.val.1.1)*b (.inl (capLow p))*(g (.inr (capLow p)))⁻¹)⁻¹=_
  group

/-- The surviving shared-edge covariance is a closed six-boundary-link Wilson
trace, invariant under ALL48 actual vertex gauges. -/
theorem pair_trace_gauge (g : FullVertex → SU2) (b : Boundary → SU2) :
    halfTrace (word (boundaryGauge g b) chosen*(word (boundaryGauge g b) partner)⁻¹)=
      halfTrace (word b chosen*(word b partner)⁻¹) := by
  rw [word_boundaryGauge,word_boundaryGauge]
  change halfTrace ((g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2))*word b chosen*
      (g (.inl chosenEdge.val.1))⁻¹)*
    (g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2))*word b partner*
      (g (.inl chosenEdge.val.1))⁻¹)⁻¹)=_
  have he : (g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2))*word b chosen*
      (g (.inl chosenEdge.val.1))⁻¹)*
    (g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2))*word b partner*
      (g (.inl chosenEdge.val.1))⁻¹)⁻¹=
    g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2))*(word b chosen*(word b partner)⁻¹)*
      (g (.inl (shifted chosenEdge.val.1 chosenEdge.val.2)))⁻¹ := by group
  rw [he,halfTrace_conjugate]

theorem pair_trace_odd_y (x y z : ℝ) :
    halfTrace (word (boundaryData x y z) chosen*(word (boundaryData x y z) partner)⁻¹)-
      halfTrace (word (boundaryData x (-y) z) chosen*(word (boundaryData x (-y) z) partner)⁻¹)=
      -2*(Real.sin x*Real.sin y*Real.sin z) := by
  rw [word_chosen,word_partner,word_chosen,word_partner]
  simp only [inv_one,mul_one]
  have hp := FourCubeWilsonCubic.triple_action x y z
  have hm := FourCubeWilsonCubic.triple_action x (-y) z
  rw [SU2JointPlaquetteCubic.action_formula] at hp hm
  simp only [Real.cos_neg,Real.sin_neg,mul_neg,neg_mul] at hm
  linarith

theorem chosen_ne_partner : chosen ≠ partner := by
  intro h
  have hj := congrArg (fun p : Upper => p.val.2) h
  norm_num [chosen,partner] at hj

theorem ribbonSum_memLp (b : Boundary → SU2) : MemLp (ribbonSum b) 2 interiorHaar :=
  memLp_finsetSum Finset.univ (fun p _ => linkProbe_memLp (ribbonInterior p) (word b p))

theorem ribbonSum_covariance (b : Boundary → SU2) (A : SU2) :
    covariance (ribbonSum b) (linkProbe chosenEdge A) interiorHaar=
      halfTrace (word b chosen*A⁻¹)/4+halfTrace (word b partner*A⁻¹)/4 := by
  unfold ribbonSum ribbonChannel
  rw [covariance_fun_sum_left (fun p => linkProbe_memLp (ribbonInterior p) (word b p))
    (linkProbe_memLp chosenEdge A)]
  simp only [ribbonChannel,linkProbe_covariance]
  calc
    _ = ∑ p∈({chosen,partner} : Finset Upper),
        if ribbonInterior p=chosenEdge then halfTrace (word b p*A⁻¹)/4 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hp
      have he : ribbonInterior p ≠ chosenEdge := by
        intro he
        rcases (edge_fiber p).mp he with he | he
        · subst p; simp at hp
        · subst p; simp at hp
      simp [he]
    _ = _ := by rw [Finset.sum_pair chosen_ne_partner,chosen_edge,partner_edge]; simp

def residualAction (x z : ℝ) (s : InteriorState) : ℝ :=
  cellAction x 0 z s+linkProbe chosenEdge (axis 0 x*axis 1 0*axis 2 z) s

theorem ribbonSum_replace (x y y' z : ℝ) (s : InteriorState) :
    ribbonSum (boundaryData x y z) s-ribbonSum (boundaryData x y' z) s=
      linkProbe chosenEdge (axis 0 x*axis 1 y*axis 2 z) s-
      linkProbe chosenEdge (axis 0 x*axis 1 y'*axis 2 z) s := by
  have hs : (∑ p : Upper, (ribbonChannel (boundaryData x y z) p s-
      ribbonChannel (boundaryData x y' z) p s))=
      ribbonChannel (boundaryData x y z) chosen s-ribbonChannel (boundaryData x y' z) chosen s := by
    apply Finset.sum_eq_single chosen
    · intro p _ hp
      unfold ribbonChannel
      rw [word_other_y x y y' z p hp,sub_self]
    · intro hn
      exact False.elim (hn (Finset.mem_univ chosen))
  rw [Finset.sum_sub_distrib] at hs
  unfold ribbonSum
  simpa only [ribbonChannel,word_chosen,chosen_edge] using hs

theorem cellAction_residual (x y z : ℝ) : cellAction x y z=
    fun s => residualAction x z s-linkProbe chosenEdge (axis 0 x*axis 1 y*axis 2 z) s := by
  funext s
  have hr := ribbonSum_replace x y 0 z s
  unfold residualAction
  simp only [cellAction,action_decomposition]
  linarith

theorem cellAction_memLp (x y z : ℝ) : MemLp (cellAction x y z) 2 interiorHaar :=
  MemLp.of_bound (cellAction_measurable x y z).aestronglyMeasurable 144
    (Filter.Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (cellAction_bounds x y z s).1] using (cellAction_bounds x y z s).2)

theorem residualAction_memLp (x z : ℝ) : MemLp (residualAction x z) 2 interiorHaar :=
  (cellAction_memLp x 0 z).add (linkProbe_memLp chosenEdge (axis 0 x*axis 1 0*axis 2 z))

private theorem action_probe_covariance (x z : ℝ) (A : SU2) :
    covariance (cellAction x 0 z) (linkProbe chosenEdge A) interiorHaar=
      -(halfTrace (word (boundaryData x 0 z) chosen*A⁻¹)/4+
        halfTrace (word (boundaryData x 0 z) partner*A⁻¹)/4) := by
  have he : cellAction x 0 z=(fun s => internalAction s+48-ribbonSum (boundaryData x 0 z) s) :=
    funext (fun s => action_decomposition _ s)
  have hplus : MemLp (fun s : InteriorState => internalAction s+48) 2 interiorHaar :=
    internalAction_memLp.add (memLp_const (48:ℝ))
  rw [he,covariance_fun_sub_left hplus
    (ribbonSum_memLp (boundaryData x 0 z)) (linkProbe_memLp chosenEdge A),
    covariance_add_const_left (internalAction_memLp.integrable (by norm_num)) 48,
    internal_link_covariance,ribbonSum_covariance]
  ring

theorem residualAction_probe_covariance (x z : ℝ) (A : SU2) :
    covariance (residualAction x z) (linkProbe chosenEdge A) interiorHaar= -halfTrace A/4 := by
  change covariance (cellAction x 0 z+linkProbe chosenEdge (axis 0 x*axis 1 0*axis 2 z))
    (linkProbe chosenEdge A) interiorHaar=_
  rw [covariance_add_left (cellAction_memLp x 0 z)
    (linkProbe_memLp chosenEdge _) (linkProbe_memLp chosenEdge A),
    action_probe_covariance,linkProbe_covariance]
  simp only [ite_true,word_chosen,word_partner,one_mul,SU2WilsonConvolution.halfTrace_inv]
  ring

/-- Exact dependence of the ACTUAL32-link Haar variance on the middle boundary
axis. The boundary-independent internal variance need not be recomputed. -/
theorem variance_formula (x y z : ℝ) : variance (cellAction x y z) interiorHaar=
    variance (residualAction x z) interiorHaar+1/4+
      halfTrace (axis 0 x*axis 1 y*axis 2 z)/2 := by
  rw [cellAction_residual,variance_fun_sub (residualAction_memLp x z)
    (linkProbe_memLp chosenEdge _),residualAction_probe_covariance,linkProbe_variance]
  ring

theorem variance_odd_y (x y z : ℝ) : variance (cellAction x y z) interiorHaar-
    variance (cellAction x (-y) z) interiorHaar= -(Real.sin x*Real.sin y*Real.sin z) := by
  rw [variance_formula,variance_formula]
  have hp := FourCubeWilsonCubic.triple_action x y z
  have hm := FourCubeWilsonCubic.triple_action x (-y) z
  rw [SU2JointPlaquetteCubic.action_formula] at hp hm
  simp only [Real.cos_neg,Real.sin_neg,mul_neg,neg_mul] at hm
  linarith

theorem variance_explicit_odd_witness :
    variance (cellAction (Real.pi/6) (Real.pi/6) (Real.pi/6)) interiorHaar-
      variance (cellAction (Real.pi/6) (-(Real.pi/6)) (Real.pi/6)) interiorHaar= -(1/8:ℝ) := by
  rw [variance_odd_y,Real.sin_pi_div_six]
  norm_num

end OperatorDerivativeRewrite.Foundation.FourCubeIntegratedCubic
