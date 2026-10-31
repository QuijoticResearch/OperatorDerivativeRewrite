import Foundation.PeriodicBoundaryHaarReduction
import Foundation.PeriodicSlabL2
/-! Exact physical-sector reduction of the actual side-four periodic Wilson
transfer. Boundary Haar integration remains. The temporal product density is
normalized by the actual single-link Laplace mass; native transition ratios
retain the constructed dressed ground. No spectral or continuum gap follows. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalKineticReduction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicGaugeSaturatedGround

theorem invariant_section (β : ℝ) (U : State) (a : Gauge) (f : State → ℝ)
    (hf : ∀ a V,f (gaugeAction a V)=f V) :
    (∫ V,weight β U V a*f V ∂boundaryHaar)=(∫ V,weight β U V 1*f V ∂boundaryHaar) := by
  have hh := (action_boundary_preserving a).integral_comp (gaugeEquiv_embedding a)
    (fun V : State => weight β U V 1*f V)
  simpa only [weight_right,one_mul,hf] using hh

private theorem invariant_joint_integrable (β : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (hi : Integrable f boundaryHaar) :
    Integrable (fun q : State × Gauge => weight β U q.1 q.2*f q.1) (boundaryHaar.prod gaugeHaar) := by
  have hm0 : Measurable (fun q : State × Gauge => ((U,q.1),q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hm := ((weight_joint_measurable β).comp hm0).mul (hf.comp measurable_fst)
  have hb := (hi.norm.comp_fst gaugeHaar).const_mul
    (Real.exp (768*|β|))
  simp only [Real.norm_eq_abs] at hb
  apply hb.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro q
  change ‖weight β U q.1 q.2 * f q.1‖ ≤ Real.exp (768*|β|)*|f q.1|
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by unfold weight; exact Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (weight_bounds β U q.1 q.2).2 (abs_nonneg _)

/-- Actual full-Haar transfer on a genuine real L1 gauge-invariant domain.
The boundary integral remains; this is not pointwise fixed-root replacement. -/
theorem invariant_transfer (β : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (hi : Integrable f boundaryHaar)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) :
    (∫ V,kernel β U V*f V ∂boundaryHaar)=(∫ V,weight β U V 1*f V ∂boundaryHaar) := by
  unfold kernel
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap (invariant_joint_integrable β U f hf hi)]
  simp_rw [invariant_section β U _ f hInv]
  simp only [integral_const,probReal_univ,one_smul]


open CubeHaarUpper PeriodicGroundHaarScale PeriodicSlabGround

def multiplier (β : ℝ) (U : State) : ℝ := Real.exp (-β*spatialAction U/2)
def kineticDensity (β : ℝ) (U V : State) : ℝ :=
  Real.exp (-β*temporalAction U V 1)/(laplace β^192)
def kinetic (β : ℝ) (f : State → ℝ) (U : State) : ℝ :=
  ∫ V, kineticDensity β U V*f V ∂boundaryHaar

theorem kinetic_mass (β : ℝ) (hb : 0 ≤ β) (U : State) :
    (∫ V,kineticDensity β U V ∂boundaryHaar)=1 := by
  unfold kineticDensity
  rw [integral_div,temporal_integral,div_self (pow_pos (laplace_pos β hb) _).ne']

theorem weight_factor (β : ℝ) (hb : 0 ≤ β) (U V : State) :
    weight β U V 1=laplace β^192*multiplier β U*kineticDensity β U V*multiplier β V := by
  have hl : laplace β ≠ 0 := (laplace_pos β hb).ne'
  unfold weight halfAction multiplier kineticDensity
  rw [show -β*(spatialAction U/2+temporalAction U V 1+spatialAction V/2)=
    (-β*spatialAction U/2)+(-β*temporalAction U V 1)+(-β*spatialAction V/2) by ring,
    Real.exp_add,Real.exp_add]
  field_simp

theorem invariant_factorization (β : ℝ) (hb : 0 ≤ β) (U : State) (f : State → ℝ)
    (hf : Measurable f) (hi : Integrable f boundaryHaar)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) :
    (∫ V,kernel β U V*f V ∂boundaryHaar)=
      laplace β^192*multiplier β U*kinetic β (fun V => multiplier β V*f V) U := by
  rw [invariant_transfer β U f hf hi hInv]
  unfold kinetic
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with V
  rw [weight_factor β hb]
  ring

/-- The actual native L2 domain supplies the required Haar-L1 integrability.
The density is the constructed ground square, not a guessed flat Haar law. -/
theorem native_weighted_integrable {β : ℝ} (g : GroundData β) (f : State → ℝ)
    (hf : Measurable f) (hmem : MemLp f 2 g.stationary) :
    Integrable (fun V => g.function V*f V) boundaryHaar := by
  have hs := (PeriodicBoundaryHaarReduction.stationary_integrable_iff g (fun V => f V^2)).mp
    hmem.integrable_sq
  have he : (fun V => g.function V^2*f V^2)=(fun V => (g.function V*f V)^2) :=
    funext (fun V => by ring)
  rw [he] at hs
  have hm := (memLp_two_iff_integrable_sq (g.measurable.mul hf).aestronglyMeasurable).mpr hs
  exact hm.integrable (by norm_num)

theorem native_transition_factorization {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) (U : State) :
    (∫ V,f V ∂g.transition U)=
      (laplace β^192*multiplier β U*
        kinetic β (fun V => multiplier β V*(g.function V*f V)) U)/(g.value*g.function U) := by
  rw [g.transition_integral]
  congr 1
  exact invariant_factorization β hb U _ (g.measurable.mul hf) (native_weighted_integrable g f hf hmem)
    (fun a V => by rw [g.invariant,hInv])

theorem dressed_ground_equation {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State) :
    laplace β^192*multiplier β U*kinetic β (fun V => multiplier β V*g.function V) U=
      g.value*g.function U := by
  have hi : Integrable g.function boundaryHaar := Integrable.of_bound
    g.measurable.aestronglyMeasurable g.upper
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using (g.bounds V).2))
  rw [← invariant_factorization β hb U g.function g.measurable hi g.invariant]
  exact g.eigen U

theorem dressed_ground_average_pos {β : ℝ} (hb : 0 ≤ β) (g : GroundData β) (U : State) :
    0 < kinetic β (fun V => multiplier β V*g.function V) U := by
  have he := dressed_ground_equation hb g U
  have hp : 0 < laplace β^192*multiplier β U :=
    mul_pos (pow_pos (laplace_pos β hb) _) (Real.exp_pos _)
  exact (mul_pos_iff_of_pos_left hp).mp (he.symm ▸ mul_pos g.value_pos (g.function_pos U))

/-- Exact Doob ratio on the full native L2 representative domain. The dressed
constructed ground is retained; this is not bare kinetic row normalization. -/
theorem native_transition_ratio {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) (U : State) :
    (∫ V,f V ∂g.transition U)=
      kinetic β (fun V => multiplier β V*(g.function V*f V)) U /
        kinetic β (fun V => multiplier β V*g.function V) U := by
  rw [native_transition_factorization hb g f hf hmem hInv U,
    ← dressed_ground_equation hb g U]
  have hp : laplace β^192*multiplier β U ≠ 0 :=
    (mul_pos (pow_pos (laplace_pos β hb) _) (Real.exp_pos _)).ne'
  exact mul_div_mul_left _ _ hp

/-- Agreement with the already constructed stationary Hilbert operator on its
bounded physical core, using the existing operator-to-kernel theorem. -/
theorem native_operator_ratio {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hmem : MemLp f 2 g.stationary)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) (B : ℝ) (hB : ∀ U,|f U| ≤ B) :
    (fun U => PeriodicSlabL2.operator g (hmem.toLp f) U) =ᵐ[g.stationary]
      (fun U => kinetic β (fun V => multiplier β V*(g.function V*f V)) U /
        kinetic β (fun V => multiplier β V*g.function V) U) := by
  rw [PeriodicSlabL2.operator_toLp g f hmem hf B hB]
  filter_upwards [MemLp.coeFn_toLp (PeriodicSlabL2.transfer_memLp g f hf B hB)] with U hU
  exact hU.trans (native_transition_ratio hb g f hf hmem hInv U)
end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalKineticReduction
