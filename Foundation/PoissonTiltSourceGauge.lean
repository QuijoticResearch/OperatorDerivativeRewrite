import Foundation.PoissonTiltHellingerGeometry
import Foundation.PoissonWeightedScalarGeometry
import Foundation.WeightedL2Transport

/-! Physical half-density unitary and coherent displacement of the actual
normalized maximal Poisson difference graph. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonTiltSourceGauge
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCoordinateEvaluation PoissonWeightedScalarGeometry
open PoissonExponentialTilt PoissonTiltHellingerGeometry

theorem rootDensity_pos (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : 0<rootDensity rate θ n := Real.exp_pos _

theorem tiltedRate_pos (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) : 0<tiltedRate rate θ := by
  change (0 : ℝ)<(rate : ℝ)*Real.exp θ
  exact mul_pos hr (Real.exp_pos θ)

theorem weightedMeasure_eq (rate : ℝ≥0) (θ : ℝ) :
    WeightedL2Transport.weightedMeasure (poissonLaw rate) (rootDensity rate θ)=poissonLaw (tiltedRate rate θ) := by
  rw [WeightedL2Transport.weightedMeasure]
  have he : (fun n => ENNReal.ofReal ((rootDensity rate θ n)^2))=
      (fun n => ENNReal.ofReal (density rate θ n)) := funext fun n => congrArg ENNReal.ofReal (rootDensity_sq rate θ n)
  rw [he]
  exact tiltedMeasure_eq_poisson rate θ

theorem base_absolutelyContinuous_tilt (rate : ℝ≥0) (θ : ℝ) :
    poissonLaw rate ≪ poissonLaw (tiltedRate rate θ) := by
  rw [← weightedMeasure_eq]
  exact WeightedL2Transport.absolutelyContinuous_weightedMeasure _ _ (by fun_prop)
    (Eventually.of_forall fun n => ne_of_gt (rootDensity_pos rate θ n))

theorem gauge_memLp (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) :
    MemLp (fun n => rootDensity rate θ n*f n) 2 (poissonLaw rate) := by
  have hf : MemLp (fun n => f n) 2
      (WeightedL2Transport.weightedMeasure (poissonLaw rate) (rootDensity rate θ)) := by
    rw [weightedMeasure_eq]
    exact Lp.memLp f
  exact WeightedL2Transport.memLp_mul _ _ (by fun_prop)
    (Eventually.of_forall fun n => ne_of_gt (rootDensity_pos rate θ n)) hf

def gaugeClass (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) : ScalarL2 rate :=
  (gauge_memLp rate θ f).toLp (fun n => rootDensity rate θ n*f n)

theorem gaugeClass_coeFn (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) :
    gaugeClass rate θ f =ᵐ[poissonLaw rate] fun n => rootDensity rate θ n*f n :=
  (gauge_memLp rate θ f).coeFn_toLp

def gaugeLinear (rate : ℝ≥0) (θ : ℝ) : ScalarL2 (tiltedRate rate θ) →ₗ[ℝ] ScalarL2 rate where
  toFun := gaugeClass rate θ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [gaugeClass_coeFn rate θ (f+g),gaugeClass_coeFn rate θ f,gaugeClass_coeFn rate θ g,
      Lp.coeFn_add (gaugeClass rate θ f) (gaugeClass rate θ g),
      (base_absolutelyContinuous_tilt rate θ).ae_eq (Lp.coeFn_add f g)] with n hfg hf hg hadd hsum
    simp only [Pi.add_apply] at hsum hadd
    rw [hfg,hsum,hadd,hf,hg,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [gaugeClass_coeFn rate θ (c • f),gaugeClass_coeFn rate θ f,
      Lp.coeFn_smul c (gaugeClass rate θ f),
      (base_absolutelyContinuous_tilt rate θ).ae_eq (Lp.coeFn_smul c f)] with n hcf hf hscalar hsmul
    simp only [Pi.smul_apply,smul_eq_mul] at hscalar hsmul
    change gaugeClass rate θ (c • f) n=(c • gaugeClass rate θ f) n
    rw [hcf,hsmul,hscalar,hf]
    ring

theorem gaugeClass_norm (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) :
    ‖gaugeClass rate θ f‖=‖f‖ := by
  have he : ‖gaugeClass rate θ f‖^2=‖f‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral,BochnerL2Dominated.norm_sq_integral]
    calc
      _ = ∫ n, density rate θ n*(f n)^2 ∂poissonLaw rate := by
        apply integral_congr_ae
        filter_upwards [gaugeClass_coeFn rate θ f] with n hn
        rw [hn,Real.norm_eq_abs,sq_abs,mul_pow,rootDensity_sq]
      _ = _ := by
        rw [← integral_transfer]
        simp only [Real.norm_eq_abs,sq_abs]
  nlinarith [norm_nonneg (gaugeClass rate θ f),norm_nonneg f]

def gaugeIsometry (rate : ℝ≥0) (θ : ℝ) : ScalarL2 (tiltedRate rate θ) →ₗᵢ[ℝ] ScalarL2 rate where
  __ := gaugeLinear rate θ
  norm_map' := gaugeClass_norm rate θ

theorem inverse_memLp (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 rate) :
    MemLp (fun n => f n/rootDensity rate θ n) 2 (poissonLaw (tiltedRate rate θ)) := by
  rw [← weightedMeasure_eq]
  exact WeightedL2Transport.memLp_div _ _ (by fun_prop)
    (Eventually.of_forall fun n => ne_of_gt (rootDensity_pos rate θ n)) (Lp.memLp f)

theorem gauge_surjective (rate : ℝ≥0) (θ : ℝ) : Function.Surjective (gaugeIsometry rate θ) := by
  intro f
  let g := (inverse_memLp rate θ f).toLp (fun n => f n/rootDensity rate θ n)
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [gaugeClass_coeFn rate θ g,
    (base_absolutelyContinuous_tilt rate θ).ae_eq (inverse_memLp rate θ f).coeFn_toLp] with n hu hv
  change gaugeClass rate θ g n=f n
  change g n=f n/rootDensity rate θ n at hv
  rw [hu,hv,mul_div_cancel₀ _ (ne_of_gt (rootDensity_pos rate θ n))]

def gauge (rate : ℝ≥0) (θ : ℝ) : ScalarL2 (tiltedRate rate θ) ≃ₗᵢ[ℝ] ScalarL2 rate :=
  LinearIsometryEquiv.ofSurjective (gaugeIsometry rate θ) (gauge_surjective rate θ)

theorem gauge_coeFn (rate : ℝ≥0) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) :
    gauge rate θ f =ᵐ[poissonLaw rate] fun n => rootDensity rate θ n*f n :=
  gaugeClass_coeFn rate θ f

theorem gauge_apply (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (f : ScalarL2 (tiltedRate rate θ)) (n : ℕ) :
    gauge rate θ f n=rootDensity rate θ n*f n :=
  ae_eq_implies_pointwise rate hr (gauge_coeFn rate θ f) n

theorem rootDensity_succ (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    rootDensity rate θ (n+1)=Real.exp (θ/2)*rootDensity rate θ n := by
  rw [rootDensity,rootDensity,← Real.exp_add]
  push_cast
  congr 1
  ring

def annihilationGraph (rate : ℝ≥0) (hr : 0<rate) (f g : ScalarL2 rate) : Prop :=
  (f,toField rate g)∈(maximalDifference rate hr).graph

theorem annihilationGraph_iff (rate : ℝ≥0) (hr : 0<rate) (f g : ScalarL2 rate) :
    annihilationGraph rate hr f g ↔ ∀ n, g n=Real.sqrt rate*(f (n+1)-f n) := by
  rw [annihilationGraph,maximalDifference_graph]
  have hs : Real.sqrt rate≠0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  constructor
  · intro hg n
    have he := hg n
    rw [toField_apply rate hr] at he
    have hh := congrArg (fun x : ℝ => Real.sqrt rate*x) he
    simpa only [← mul_assoc,mul_inv_cancel₀ hs,one_mul] using hh
  · intro hg n
    rw [toField_apply rate hr,hg n,← mul_assoc,inv_mul_cancel₀ hs,one_mul]

def displacement (rate : ℝ≥0) (θ : ℝ) : ℝ := Real.sqrt (tiltedRate rate θ)-Real.sqrt rate

theorem annihilation_gauge_iff (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (f g : ScalarL2 (tiltedRate rate θ)) :
    annihilationGraph (tiltedRate rate θ) (tiltedRate_pos rate hr θ) f g ↔
      annihilationGraph rate hr (gauge rate θ f)
        (gauge rate θ g+displacement rate θ • gauge rate θ f) := by
  rw [annihilationGraph_iff,annihilationGraph_iff]
  apply forall_congr'
  intro n
  rw [scalar_add_apply rate hr,scalar_smul_apply rate hr,
    gauge_apply rate hr θ g n,gauge_apply rate hr θ f n,gauge_apply rate hr θ f (n+1),rootDensity_succ]
  rw [displacement,← sqrtRate_eq_sqrt_tilted rate θ]
  simp only [sqrtRate]
  let ρ := rootDensity rate θ n
  let s := Real.sqrt (rate : ℝ)
  let e := Real.exp (θ/2)
  change (g n=s*e*(f (n+1)-f n)) ↔
    (ρ*g n+(s*e-s)*(ρ*f n)=s*(e*ρ*f (n+1)-ρ*f n))
  constructor
  · intro hg
    rw [hg]
    ring
  · intro hg
    apply mul_left_cancel₀ (show ρ≠0 from ne_of_gt (rootDensity_pos rate θ n))
    linear_combination hg

def creationExpr (rate : ℝ≥0) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => -Real.sqrt rate*g 0
  | n+1 => (n+1 : ℝ)*(Real.sqrt rate)⁻¹*g n-Real.sqrt rate*g (n+1)

def creationGraph (rate : ℝ≥0) (hr : 0<rate) (g f : ScalarL2 rate) : Prop :=
  (toField rate g,f)∈(maximalDivergence rate hr).graph

theorem creationGraph_iff (rate : ℝ≥0) (hr : 0<rate) (g f : ScalarL2 rate) :
    creationGraph rate hr g f ↔ ∀ n, f n=creationExpr rate g n := by
  have hs : Real.sqrt rate≠0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hscale : (rate : ℝ)*(Real.sqrt rate)⁻¹=Real.sqrt rate := by
    calc
      _ = (Real.sqrt rate)^2*(Real.sqrt rate)⁻¹ := by rw [Real.sq_sqrt rate.coe_nonneg]
      _ = _ := by rw [pow_two,mul_assoc,mul_inv_cancel₀ hs,mul_one]
  rw [creationGraph,maximalDivergence_graph]
  change (∀ n, f n=maximalDivergenceExpr rate (toField rate g) n) ↔ _
  apply forall_congr'
  intro n
  cases n <;> simp only [maximalDivergenceExpr,creationExpr,toField_apply rate hr,
    neg_mul,← mul_assoc,hscale]

theorem creationExpr_gauge (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (g : ScalarL2 (tiltedRate rate θ)) (n : ℕ) :
    creationExpr rate (gauge rate θ g) n=rootDensity rate θ n*creationExpr (tiltedRate rate θ) g n+
      displacement rate θ*(rootDensity rate θ n*g n) := by
  have hs : Real.sqrt rate≠0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have he : Real.exp (θ/2)≠0 := ne_of_gt (Real.exp_pos _)
  cases n with
  | zero =>
    rw [creationExpr,creationExpr,gauge_apply rate hr θ g 0,
      displacement,← sqrtRate_eq_sqrt_tilted rate θ]
    simp only [sqrtRate]
    ring
  | succ n =>
    rw [creationExpr,creationExpr,gauge_apply rate hr θ g n,gauge_apply rate hr θ g (n+1),
      rootDensity_succ,displacement,← sqrtRate_eq_sqrt_tilted rate θ]
    simp only [sqrtRate]
    field_simp
    ring

theorem creation_gauge_iff (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (g f : ScalarL2 (tiltedRate rate θ)) :
    creationGraph (tiltedRate rate θ) (tiltedRate_pos rate hr θ) g f ↔
      creationGraph rate hr (gauge rate θ g)
        (gauge rate θ f+displacement rate θ • gauge rate θ g) := by
  rw [creationGraph_iff,creationGraph_iff]
  apply forall_congr'
  intro n
  rw [scalar_add_apply rate hr,scalar_smul_apply rate hr,gauge_apply rate hr θ f n,
    gauge_apply rate hr θ g n,creationExpr_gauge rate hr θ g n]
  constructor
  · intro hf
    rw [hf]
  · intro hf
    apply mul_left_cancel₀ (ne_of_gt (rootDensity_pos rate θ n))
    linear_combination hf

end OperatorDerivativeRewrite.Foundation.PoissonTiltSourceGauge
