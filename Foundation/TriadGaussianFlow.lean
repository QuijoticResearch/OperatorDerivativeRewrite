import Foundation.QuadraticTriadGaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-! The actual global finite inviscid triad flow and its invariant Gaussian law.
The parameter-dependent rotation is nonlinear on the full three-coordinate state. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.TriadGaussianFlow
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev State := ℝ × Plane
abbrev γ : Measure ℝ := GaussianCore.γ
abbrev planeGaussian : Measure Plane := stdGaussian Plane
abbrev law : Measure State := γ.prod planeGaussian
abbrev vectorGaussian : Measure Vector := Measure.pi (fun _ : Fin 3 => γ)

def rotateLinear (θ : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun z := WithLp.toLp 2 ![Real.cos θ*z 0+Real.sin θ*z 1,
    -Real.sin θ*z 0+Real.cos θ*z 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem rotateLinear_norm (θ : ℝ) (z : Plane) : ‖rotateLinear θ z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  have hs : (Real.cos θ)^2+(Real.sin θ)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  simp only [Fin.sum_univ_two]
  change (Real.cos θ*z 0+Real.sin θ*z 1)^2+
    (-Real.sin θ*z 0+Real.cos θ*z 1)^2=(z 0)^2+(z 1)^2
  calc
    _ = ((Real.cos θ)^2+(Real.sin θ)^2)*((z 0)^2+(z 1)^2) := by
      ring
    _ = _ := by rw [hs]; ring

def rotate (θ : ℝ) : Plane ≃ₗᵢ[ℝ] Plane :=
  (show Plane →ₗᵢ[ℝ] Plane from
    { rotateLinear θ with norm_map' := rotateLinear_norm θ }).toLinearIsometryEquiv rfl

theorem rotate_apply (θ : ℝ) (z : Plane) : rotate θ z=
    WithLp.toLp 2 ![Real.cos θ*z 0+Real.sin θ*z 1,-Real.sin θ*z 0+Real.cos θ*z 1] := rfl

theorem rotate_zero (z : Plane) : rotate 0 z=z := by
  ext i
  fin_cases i <;> simp [rotate_apply]

theorem rotate_add (θ φ : ℝ) (z : Plane) : rotate (θ+φ) z=rotate θ (rotate φ z) := by
  ext i
  fin_cases i <;> simp [rotate_apply,Real.sin_add,Real.cos_add] <;> ring

theorem rotate_preserving (θ : ℝ) : MeasurePreserving (rotate θ) planeGaussian planeGaussian :=
  ⟨(rotate θ).continuous.measurable,stdGaussian_map (rotate θ)⟩

def flow (t : ℝ) (x : State) : State := (x.1,rotate (t*x.1) x.2)

theorem flow_zero (x : State) : flow 0 x=x := by simp [flow,rotate_zero]

theorem flow_add (s t : ℝ) (x : State) : flow (s+t) x=flow s (flow t x) := by
  simp only [flow,add_mul,rotate_add]

theorem flow_inverse (t : ℝ) (x : State) : flow (-t) (flow t x)=x := by
  rw [← flow_add]
  simp [flow_zero]

theorem flow_continuous (t : ℝ) : Continuous (flow t) := by
  change Continuous (fun x : State => (x.1,WithLp.toLp 2
    ![Real.cos (t*x.1)*x.2 0+Real.sin (t*x.1)*x.2 1,
      -Real.sin (t*x.1)*x.2 0+Real.cos (t*x.1)*x.2 1]))
  fun_prop

theorem flow_preserving (t : ℝ) : MeasurePreserving (flow t) law law := by
  change MeasurePreserving (fun x : State => (id x.1,rotate (t*x.1) x.2))
    (γ.prod planeGaussian) (γ.prod planeGaussian)
  refine (MeasurePreserving.id γ).skew_product
    (g := fun c z => rotate (t*c) z) ?_ ?_
  · exact (continuous_snd.comp (flow_continuous t)).measurable
  · exact ae_of_all _ (fun c => (rotate_preserving (t*c)).map_eq)

def decode (x : State) : Vector := ![x.2 0,x.2 1,x.1]
def encode (x : Vector) : State := (x 2,WithLp.toLp 2 ![x 0,x 1])

theorem decode_encode (x : Vector) : decode (encode x)=x := by
  ext i
  fin_cases i <;> rfl

theorem encode_decode (x : State) : encode (decode x)=x := by
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

theorem decode_continuous : Continuous decode := by unfold decode; fun_prop
theorem encode_continuous : Continuous encode := by unfold encode; fun_prop

def coordinates : State ≃ᵐ Vector where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode
  measurable_toFun := decode_continuous.measurable
  measurable_invFun := encode_continuous.measurable

theorem encode_preserving : MeasurePreserving encode vectorGaussian law := by
  have hp : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane)
      (Measure.pi (fun _ : Fin 2 => γ)) planeGaussian :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hs := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => γ) (2 : Fin 3)
  have ht := ((MeasurePreserving.id γ).prod hp).comp hs
  convert ht using 1
  funext x
  apply Prod.ext
  · rfl
  · ext i; fin_cases i <;> rfl

theorem decode_preserving : MeasurePreserving decode law vectorGaussian :=
  MeasurePreserving.symm coordinates.symm encode_preserving

def vectorFlow (t : ℝ) (x : Vector) : Vector := decode (flow t (encode x))

theorem vectorFlow_formula (t : ℝ) (x : Vector) : vectorFlow t x=
    ![Real.cos (t*x 2)*x 0+Real.sin (t*x 2)*x 1,
      -Real.sin (t*x 2)*x 0+Real.cos (t*x 2)*x 1,x 2] := rfl

theorem vectorFlow_zero (x : Vector) : vectorFlow 0 x=x := by
  rw [vectorFlow,flow_zero,decode_encode]

theorem vectorFlow_add (s t : ℝ) (x : Vector) :
    vectorFlow (s+t) x=vectorFlow s (vectorFlow t x) := by
  simp only [vectorFlow,encode_decode,flow_add]

theorem vectorFlow_preserving (t : ℝ) : MeasurePreserving (vectorFlow t) vectorGaussian vectorGaussian :=
  decode_preserving.comp ((flow_preserving t).comp encode_preserving)

theorem gaussian_invariant (t : ℝ) : vectorGaussian.map (vectorFlow t)=vectorGaussian :=
  (vectorFlow_preserving t).map_eq

theorem vectorFlow_inverse (t : ℝ) (x : Vector) : vectorFlow (-t) (vectorFlow t x)=x := by
  rw [← vectorFlow_add]
  simp [vectorFlow_zero]

theorem third_fixed (t : ℝ) (x : Vector) : vectorFlow t x 2=x 2 := rfl

theorem plane_square_preserved (t : ℝ) (x : Vector) :
    (vectorFlow t x 0)^2+(vectorFlow t x 1)^2=(x 0)^2+(x 1)^2 := by
  have hs : (Real.cos (t*x 2))^2+(Real.sin (t*x 2))^2=1 := by
    linarith [Real.sin_sq_add_cos_sq (t*x 2)]
  calc
    _ = ((Real.cos (t*x 2))^2+(Real.sin (t*x 2))^2)*((x 0)^2+(x 1)^2) := by
      simp only [vectorFlow_formula,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    _ = _ := by rw [hs]; ring

theorem weighted_square_preserved (α β t : ℝ) (x : Vector) :
    α*(vectorFlow t x 0)^2+α*(vectorFlow t x 1)^2+β*(vectorFlow t x 2)^2=
      α*(x 0)^2+α*(x 1)^2+β*(x 2)^2 := by
  have h := plane_square_preserved t x
  rw [third_fixed]
  linear_combination α*h

/-- The full Gaussian-preserving transformation is genuinely nonlinear. -/
theorem nonadditive :
    vectorFlow (Real.pi/2) (![1,0,0]+![0,0,1]) ≠
      vectorFlow (Real.pi/2) ![1,0,0]+vectorFlow (Real.pi/2) ![0,0,1] := by
  intro h
  have he := congrFun h 0
  norm_num [vectorFlow_formula,Pi.add_apply] at he

/-- The explicit finite flow solves the actual inviscid retained triad drift at every time. -/
theorem vectorFlow_derivative (x : Vector) (t : ℝ) :
    HasDerivAt (fun s => vectorFlow s x)
      (DictionaryTriadPotential.drift 0 (vectorFlow t x)) t := by
  have ha : HasDerivAt (fun s : ℝ => s*x 2) (x 2) t := by
    simpa using (hasDerivAt_id t).mul_const (x 2)
  have hc := ha.cos
  have hs := ha.sin
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (hc.mul_const (x 0)).add (hs.mul_const (x 1)) using 1 <;> (try funext s) <;>
      simp [vectorFlow_formula,DictionaryTriadPotential.drift] <;> ring
  · convert (hs.neg.mul_const (x 0)).add (hc.mul_const (x 1)) using 1 <;> (try funext s) <;>
      simp [vectorFlow_formula,DictionaryTriadPotential.drift] <;> ring
  · simpa [vectorFlow_formula,DictionaryTriadPotential.drift] using hasDerivAt_const t (x 2)

/-- The original Gaussian product's first three actual evaluation coordinates. -/
def sampleVector (ω : InfiniteGaussian.SampleSpace) : Vector :=
  fun i => InfiniteGaussian.coordinate (i : ℕ) ω

theorem sampleVector_preserving : MeasurePreserving sampleVector
    InfiniteGaussian.gaussianProduct vectorGaussian := by
  have hi := iIndepFun.precomp (g := fun i : Fin 3 => (i : ℕ)) Fin.val_injective
    InfiniteGaussian.coordinates_independent
  have hm (i : Fin 3) : AEMeasurable (InfiniteGaussian.coordinate (i : ℕ))
      InfiniteGaussian.gaussianProduct :=
    (InfiniteGaussian.coordinate_measurePreserving _).measurable.aemeasurable
  refine ⟨?_, ?_⟩
  · unfold sampleVector InfiniteGaussian.coordinate
    fun_prop
  · change InfiniteGaussian.gaussianProduct.map
      (fun ω : InfiniteGaussian.SampleSpace => fun i : Fin 3 =>
        InfiniteGaussian.coordinate (i : ℕ) ω)=Measure.pi (fun _ : Fin 3 => GaussianCore.γ)
    simpa only [InfiniteGaussian.coordinate_law] using iIndepFun.map_fun_eq_pi_map hm hi

def sourceFlow (t : ℝ) (ω : InfiniteGaussian.SampleSpace) : Vector := vectorFlow t (sampleVector ω)

theorem sourceFlow_preserving (t : ℝ) : MeasurePreserving (sourceFlow t)
    InfiniteGaussian.gaussianProduct vectorGaussian :=
  (vectorFlow_preserving t).comp sampleVector_preserving

theorem sourceFlow_law (t : ℝ) :
    InfiniteGaussian.gaussianProduct.map (sourceFlow t)=vectorGaussian :=
  (sourceFlow_preserving t).map_eq

/-- The process on the original source space has the previously constructed
quadratic field as its actual initial velocity, almost everywhere. -/
theorem sourceFlow_initial_velocity : ∀ᵐ ω ∂InfiniteGaussian.gaussianProduct,
    HasDerivAt (fun t => sourceFlow t ω)
      (fun i : Fin 3 => TriadGaussianHodge.component (i : ℕ) QuadraticTriadGaussian.field ω) 0 := by
  filter_upwards [QuadraticTriadGaussian.components_equal_triad,
    TriadGaussianHodge.coordinate_coeFn 0,TriadGaussianHodge.coordinate_coeFn 1,
    TriadGaussianHodge.coordinate_coeFn 2] with ω hcomp h0 h1 h2
  have hv : sampleVector ω=![TriadGaussianHodge.coordinate 0 ω,
      TriadGaussianHodge.coordinate 1 ω,TriadGaussianHodge.coordinate 2 ω] := by
    ext i
    fin_cases i <;> simp [sampleVector,h0,h1,h2]
  have he : DictionaryTriadPotential.drift 0 (sampleVector ω)=
      fun i : Fin 3 => TriadGaussianHodge.component (i : ℕ) QuadraticTriadGaussian.field ω := by
    funext i
    rw [hcomp i,← hv]
  have hd := vectorFlow_derivative (sampleVector ω) 0
  rw [vectorFlow_zero,he] at hd
  exact hd

end OperatorDerivativeRewrite.Foundation.TriadGaussianFlow
