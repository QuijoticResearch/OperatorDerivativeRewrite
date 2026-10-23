import Foundation.IBMJointPredictableMultiplier

/-! Bounded predictable multiplication descends through the full signed-energy
null quotient and extends to the genuine stochastic Hilbert completion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedPredictableMultiplier
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMMultichannelCompletion IBMJointPredictableMultiplier
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
variable {ι : Type*} [DecidableEq ι] (F : ι → JointL2)

def rawMap (g : BoundedPredictable) : Raw F →ₗ[ℝ] Raw F :=
  DirectSum.toModule ℝ ι (Raw F) (fun i =>
    (DirectSum.lof ℝ ι (fun i => PredictableL2 (F i)) i).comp (multiplier g (F i)).toLinearMap)

theorem rawMap_single (g : BoundedPredictable) (i : ι) (H : PredictableL2 (F i)) :
    rawMap F g (DirectSum.lof ℝ ι _ i H) =
      DirectSum.lof ℝ ι _ i (multiplier g (F i) H) := by
  simp only [rawMap, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

def modifiedIntegral (g : BoundedPredictable) : Raw F →ₗ[ℝ] JointL2 :=
  DirectSum.toModule ℝ ι JointL2 (fun i =>
    (IBMFullPredictableIntegral.integral (F i)).toLinearMap.comp (multiplier g (F i)).toLinearMap)

theorem rawMap_integral (g : BoundedPredictable) :
    (rawIntegral F).comp (rawMap F g) = modifiedIntegral F g := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro H
  simp only [LinearMap.comp_apply, rawMap_single, rawIntegral_single,
    modifiedIntegral, DirectSum.toModule_lof]
  rfl

theorem modifiedIntegral_sum (g : BoundedPredictable) (u : Raw F) :
    modifiedIntegral F g u = ∑ i ∈ u.support,
      IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) (u i)) := by
  classical
  change DFinsupp.sumAddHom (fun i =>
    ((IBMFullPredictableIntegral.integral (F i)).toLinearMap.comp
      (multiplier g (F i)).toLinearMap).toAddMonoidHom) u = _
  rw [DFinsupp.sumAddHom_apply]
  rfl

theorem raw_bound (g : BoundedPredictable) (u : Raw F) :
    ‖rawIntegral F (rawMap F g u)‖ ≤ g.bound*‖rawIntegral F u‖ := by
  change ‖((rawIntegral F).comp (rawMap F g)) u‖ ≤ _
  rw [rawMap_integral, modifiedIntegral_sum, rawIntegral_sum]
  exact finite_stochastic_bound g F u.support (fun i => u i)

theorem preserves_null (g : BoundedPredictable) :
    Null F ≤ (Null F).comap (rawMap F g) := by
  intro u hu
  have hz : rawIntegral F u = 0 := hu
  have hn := raw_bound F g u
  rw [hz,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

def quotientMap (g : BoundedPredictable) : EnergyQuotient F →ₗ[ℝ] EnergyQuotient F :=
  (Null F).mapQ (Null F) (rawMap F g) (preserves_null F g)

theorem quotientMap_mk (g : BoundedPredictable) (u : Raw F) :
    quotientMap F g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (rawMap F g u) := rfl

theorem quotient_bound (g : BoundedPredictable) (q : EnergyQuotient F) :
    ‖quotientMap F g q‖ ≤ g.bound*‖q‖ := by
  induction q using Submodule.Quotient.induction_on with
  | _ u =>
    change ‖quotientIntegral F (quotientMap F g (Submodule.Quotient.mk u))‖ ≤
      g.bound*‖quotientIntegral F (Submodule.Quotient.mk u)‖
    rw [quotientMap_mk, quotientIntegral_mk, quotientIntegral_mk]
    exact raw_bound F g u

def quotientOperator (g : BoundedPredictable) : EnergyQuotient F →L[ℝ] EnergyQuotient F :=
  (quotientMap F g).mkContinuous g.bound (quotient_bound F g)

def operator (g : BoundedPredictable) : Completed F →L[ℝ] Completed F :=
  (quotientOperator F g).completion

theorem operator_embed (g : BoundedPredictable) (u : Raw F) :
    operator F g (embed F u) = embed F (rawMap F g u) := by
  change (quotientOperator F g).completion (Submodule.Quotient.mk u : EnergyQuotient F) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

theorem operator_single (g : BoundedPredictable) (i : ι) (H : PredictableL2 (F i)) :
    operator F g (embed F (DirectSum.lof ℝ ι _ i H)) =
      embed F (DirectSum.lof ℝ ι _ i (multiplier g (F i) H)) := by
  rw [operator_embed, rawMap_single]

theorem operator_bound (g : BoundedPredictable) (z : Completed F) :
    ‖operator F g z‖ ≤ g.bound*‖z‖ := by
  refine (embed_dense F).induction_on z
    (isClosed_le ((operator F g).continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro u
  rw [operator_embed, ← (completedIntegral F).norm_map, ← (completedIntegral F).norm_map (embed F u),
    completedIntegral_embed, completedIntegral_embed]
  exact raw_bound F g u

theorem actual_finite_integral (g : BoundedPredictable) (u : Raw F) :
    completedIntegral F (operator F g (embed F u)) =
      ∑ i ∈ u.support, IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) (u i)) := by
  rw [operator_embed, completedIntegral_embed]
  change ((rawIntegral F).comp (rawMap F g)) u = _
  rw [rawMap_integral, modifiedIntegral_sum]

theorem operator_unique (g : BoundedPredictable) (T : Completed F →L[ℝ] Completed F)
    (hT : ∀ i H, T (embed F (DirectSum.lof ℝ ι _ i H)) =
      embed F (DirectSum.lof ℝ ι _ i (multiplier g (F i) H))) : T = operator F g := by
  have hr : T.toLinearMap.comp (embed F) = (operator F g).toLinearMap.comp (embed F) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro H
    exact (hT i H).trans (operator_single F g i H).symm
  apply ContinuousLinearMap.ext
  intro z
  exact (embed_dense F).induction_on z (isClosed_eq T.continuous (operator F g).continuous)
    (fun u => DFunLike.congr_fun hr u)



theorem operator_congr (g h : BoundedPredictable) (he : ∀ p, g.function p=h.function p) :
    operator F g = operator F h := by
  apply (operator_unique F h (operator F g))
  intro i H
  rw [operator_single, multiplier_congr g h he]

theorem operator_constant (a : ℝ) :
    operator F (constant a) = a • ContinuousLinearMap.id ℝ (Completed F) := by
  symm
  apply operator_unique F (constant a)
  intro i H
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    multiplier_constant, map_smul]

theorem operator_add (g h : BoundedPredictable) :
    operator F (add g h) = operator F g+operator F h := by
  symm
  apply operator_unique F (add g h)
  intro i H
  simp only [add_apply, operator_single, multiplier_add, map_add]

theorem operator_mul (g h : BoundedPredictable) :
    operator F (mul g h) = (operator F g).comp (operator F h) := by
  symm
  apply operator_unique F (mul g h)
  intro i H
  simp only [ContinuousLinearMap.comp_apply, operator_single, multiplier_mul]

theorem operator_commute (g h : BoundedPredictable) :
    (operator F g).comp (operator F h) = (operator F h).comp (operator F g) := by
  rw [← operator_mul, ← operator_mul]
  apply operator_congr
  intro p
  exact mul_comm _ _

theorem operator_norm (g : BoundedPredictable) : ‖operator F g‖ ≤ g.bound :=
  ContinuousLinearMap.opNorm_le_bound _ g.bound_nonneg (operator_bound F g)

def indicator (E : Set Space) (hE : MeasurableSet E) : BoundedPredictable where
  function := E.indicator (fun _ => 1)
  measurable := measurable_const.indicator hE
  bound := 1
  bound_nonneg := by norm_num
  bounded p := by
    by_cases hp : p ∈ E <;> simp [Set.indicator, hp]

theorem indicator_idempotent (E : Set Space) (hE : MeasurableSet E) :
    (operator F (indicator E hE)).comp (operator F (indicator E hE)) = operator F (indicator E hE) := by
  rw [← operator_mul]
  apply operator_congr
  intro p
  by_cases hp : p ∈ E <;> simp [indicator, mul, Set.indicator, hp]

theorem timeSet_multiplier (t : ℝ≥0) (G : JointL2) (H : PredictableL2 G) :
    multiplier (indicator (IBMPredictableTimeCutoff.timeSet t)
      (IBMPredictableTimeCutoff.timeSet_measurable t)) G H = IBMPredictableTimeCutoff.cutoff G t H := by
  apply Lp.ext
  filter_upwards [multiplier_ae (indicator (IBMPredictableTimeCutoff.timeSet t)
    (IBMPredictableTimeCutoff.timeSet_measurable t)) G H, IBMPredictableTimeCutoff.cutoff_ae G t H]
    with p hp hq
  rw [hp,hq]
  by_cases hh : p ∈ IBMPredictableTimeCutoff.timeSet t <;>
    simp [indicator, Set.indicator, hh]

local instance : DecidableEq IBMFixedStochasticFamily.basisSet := Classical.decEq _

theorem operator_timeSet (t : ℝ≥0) :
    operator fixedFamily (indicator (IBMPredictableTimeCutoff.timeSet t)
      (IBMPredictableTimeCutoff.timeSet_measurable t)) = IBMCompletedTimeCutoff.stop t := by
  symm
  apply operator_unique fixedFamily
  intro i H
  rw [IBMCompletedTimeCutoff.stopped_single, timeSet_multiplier]

theorem completed_series (g : BoundedPredictable) (H : ∀ i, PredictableL2 (F i))
    (z : Completed F) (hz : HasSum (fun i => embed F (DirectSum.lof ℝ ι _ i (H i))) z) :
    HasSum (fun i => embed F (DirectSum.lof ℝ ι _ i (multiplier g (F i) (H i)))) (operator F g z) := by
  have hs := hz.mapL (operator F g)
  simpa only [operator_single] using hs

theorem actual_series (g : BoundedPredictable) (H : ∀ i, PredictableL2 (F i))
    (z : Completed F) (hz : HasSum (fun i => embed F (DirectSum.lof ℝ ι _ i (H i))) z) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) (H i)))
      (completedIntegral F (operator F g z)) := by
  have hs := (completedIntegral F).continuous.continuousAt.tendsto.comp (completed_series F g H z hz)
  change Tendsto (fun s : Finset ι => ∑ i ∈ s,
    IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) (H i))) atTop
    (𝓝 (completedIntegral F (operator F g z)))
  change Tendsto (fun s : Finset ι => completedIntegral F
    (∑ i ∈ s, embed F (DirectSum.lof ℝ ι _ i (multiplier g (F i) (H i))))) atTop
    (𝓝 (completedIntegral F (operator F g z))) at hs
  simpa only [map_sum, completedIntegral_embed, rawIntegral_single] using hs

theorem canonical_actual_series (g : BoundedPredictable) (z : Completed fixedFamily) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i)
      (multiplier g (fixedFamily i) (IBMCompletedCoordinates.coordinates z i)))
      (completedIntegral fixedFamily (operator fixedFamily g z)) :=
  actual_series fixedFamily g _ z (IBMCompletedCoordinates.coordinates_completed_sum z)



theorem operator_difference_bound (g h : BoundedPredictable) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ p, ‖g.function p-h.function p‖ ≤ δ) :
    ‖operator F g-operator F h‖ ≤ δ := by
  let d : BoundedPredictable :=
    ⟨(fun p => g.function p-h.function p), g.measurable.sub h.measurable, δ, hδ, hd⟩
  have he : operator F g-operator F h = operator F d := by
    apply operator_unique F d
    intro i H
    simp only [sub_apply, operator_single, ← map_sub]
    congr 1
    congr 1
    apply Lp.ext
    filter_upwards [multiplier_ae g (F i) H, multiplier_ae h (F i) H,
      multiplier_ae d (F i) H, Lp.coeFn_sub (multiplier g (F i) H) (multiplier h (F i) H)]
      with p hg hh hd hs
    rw [hs,Pi.sub_apply,hg,hh,hd]
    change g.function p*H p-h.function p*H p = (g.function p-h.function p)*H p
    ring
  rw [he]
  exact operator_norm F d

theorem uniform_operator_limit (g : ℕ → BoundedPredictable) (h : BoundedPredictable)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hd : ∀ n p, ‖(g n).function p-h.function p‖ ≤ δ n) :
    Tendsto (fun n => operator F (g n)) atTop (𝓝 (operator F h)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => operator_difference_bound F (g n) h (δ n) (hδ n) (hd n)) hlim

end OperatorDerivativeRewrite.Foundation.IBMCompletedPredictableMultiplier
