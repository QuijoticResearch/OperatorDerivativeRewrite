import Foundation.OneSidedCapComplex

/-! An ordered-path potential and its exact discrete Stokes error formula. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubePathPoincare
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

abbrev EdgeField := EdgeData → ℝ

def pathPrefix (v : Vertex) (j : Fin 4) : Vertex := fun i => if i<j then v i else 0

def pathMap : EdgeField →ₗ[ℝ] (Vertex → ℝ) := LinearMap.pi (fun v =>
  ∑ i : Fin 4, if v i=1 then (LinearMap.proj (pathPrefix v i,i) : EdgeField →ₗ[ℝ] ℝ) else 0)

theorem pathMap_apply (f : EdgeField) (v : Vertex) :
    pathMap f v=∑ i : Fin 4, if v i=1 then f (pathPrefix v i,i) else 0 := by
  simp [pathMap,LinearMap.sum_apply,apply_ite,ite_apply]

def curlRow (p : FaceData) : EdgeField →ₗ[ℝ] ℝ :=
  (LinearMap.proj (p.1,p.2.1) : EdgeField →ₗ[ℝ] ℝ)+LinearMap.proj (shifted p.1 p.2.1,p.2.2)-
    LinearMap.proj (shifted p.1 p.2.2,p.2.1)-LinearMap.proj (p.1,p.2.2)

theorem curlRow_apply (f : EdgeField) (p : FaceData) : curlRow p f=realCurl f p := by
  simp [curlRow,realCurl]

def correction : EdgeField →ₗ[ℝ] (Interior → ℝ) := LinearMap.pi (fun e =>
  (LinearMap.proj (shifted e.val.1 e.val.2)).comp pathMap-
    (LinearMap.proj e.val.1).comp pathMap-LinearMap.proj e.val)

def curlCombination : EdgeField →ₗ[ℝ] (Interior → ℝ) := LinearMap.pi (fun e =>
  ∑ j : Fin 4, if e.val.2<j ∧ e.val.1 j=1 then curlRow (pathPrefix e.val.1 j,(e.val.2,j)) else 0)

theorem correction_apply (f : EdgeField) (e : Interior) :
    correction f e=pathMap f (shifted e.val.1 e.val.2)-pathMap f e.val.1-f e.val := by
  simp [correction]

theorem curlCombination_apply (f : EdgeField) (e : Interior) : curlCombination f e=
    ∑ j : Fin 4, if e.val.2<j ∧ e.val.1 j=1 then realCurl f (pathPrefix e.val.1 j,(e.val.2,j)) else 0 := by
  simp [curlCombination,LinearMap.sum_apply,apply_ite,ite_apply,curlRow_apply]

def intPath (f : EdgeData → ℤ) (v : Vertex) : ℤ :=
  ∑ i : Fin 4, if v i=1 then f (pathPrefix v i,i) else 0

theorem pathMap_integer (f : EdgeData → ℤ) (v : Vertex) :
    pathMap (fun e => (f e : ℝ)) v=(intPath f v : ℝ) := by
  simp [pathMap_apply,intPath,Int.cast_sum,apply_ite]

theorem realCurl_integer (f : EdgeData → ℤ) (p : FaceData) :
    realCurl (fun e => (f e : ℝ)) p=(curl f p : ℝ) := by
  simp [realCurl,curl,Int.cast_add,Int.cast_sub]

def intDelta (q e : EdgeData) : ℤ := if q=e then 1 else 0

theorem integer_stokes : ∀ e : Interior, ∀ q : EdgeData,
    intPath (intDelta q) (shifted e.val.1 e.val.2)-intPath (intDelta q) e.val.1-
      intDelta q e.val=
      ∑ j : Fin 4, if e.val.2<j ∧ e.val.1 j=1 then
        curl (intDelta q) (pathPrefix e.val.1 j,(e.val.2,j)) else 0 := by decide +kernel

theorem correction_eq_curls : correction=curlCombination := by
  apply (Pi.basisFun ℝ EdgeData).ext
  intro q
  rw [Pi.basisFun_apply]
  have he : (Pi.single q (1 : ℝ) : EdgeField)=
      (fun e : EdgeData => (intDelta q e : ℝ)) := by
    funext e
    by_cases h : q=e <;> simp [Pi.single_apply,intDelta,h,eq_comm]
  rw [he]
  funext e
  simp only [correction_apply,curlCombination_apply,pathMap_integer,realCurl_integer]
  exact_mod_cast integer_stokes e q

theorem prefix_face_mem : ∀ e : Interior, ∀ j : Fin 4,
    e.val.2<j ∧ e.val.1 j=1 → (pathPrefix e.val.1 j,(e.val.2,j))∈innerFaces := by decide

theorem path_stokes (f : EdgeField) (e : Interior) :
    pathMap f (shifted e.val.1 e.val.2)-pathMap f e.val.1-f e.val=
      ∑ j : Fin 4, if e.val.2<j ∧ e.val.1 j=1 then
        realCurl f (pathPrefix e.val.1 j,(e.val.2,j)) else 0 := by
  have h := congrArg (fun L : EdgeField →ₗ[ℝ] (Interior → ℝ) => L f e) correction_eq_curls
  simpa only [correction_apply,curlCombination_apply] using h

theorem cube_poincare (f : EdgeField) (hf : ∀ p∈innerFaces, realCurl f p=0) (e : Interior) :
    pathMap f (shifted e.val.1 e.val.2)-pathMap f e.val.1=f e.val := by
  have h := path_stokes f e
  have hz : (∑ j : Fin 4, if e.val.2<j ∧ e.val.1 j=1 then
      realCurl f (pathPrefix e.val.1 j,(e.val.2,j)) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · exact hf _ (prefix_face_mem e j hj)
    · rfl
  rw [hz] at h
  linarith

theorem path_origin (f : EdgeField) : pathMap f origin=0 := by
  simp [pathMap_apply,origin]

end OperatorDerivativeRewrite.Foundation.CubePathPoincare
