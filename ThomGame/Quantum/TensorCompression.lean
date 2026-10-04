module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! Compression of tensor observables along local isometric embeddings. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped TensorProduct

variable {H₁ H₂ K₁ K₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  [CompleteSpace (H₁ ⊗[ℂ] H₂)] [CompleteSpace (K₁ ⊗[ℂ] K₂)]

/-- Compressing the tensor product of two operators gives the tensor product of
their local compressions. -/
theorem tensor_compression (V₁ : H₁ →ₗᵢ[ℂ] K₁) (V₂ : H₂ →ₗᵢ[ℂ] K₂)
    (P : K₁ →L[ℂ] K₁) (Q : K₂ →L[ℂ] K₂) :
    (TensorProduct.mapIsometry V₁ V₂).toContinuousLinearMap.adjoint ∘L
        TensorProduct.mapL P Q ∘L
        (TensorProduct.mapIsometry V₁ V₂).toContinuousLinearMap =
      TensorProduct.mapL
        (V₁.toContinuousLinearMap.adjoint ∘L P ∘L V₁.toContinuousLinearMap)
        (V₂.toContinuousLinearMap.adjoint ∘L Q ∘L V₂.toContinuousLinearMap) := by
  simp only [TensorProduct.toContinuousLinearMap_mapIsometry,
    TensorProduct.adjoint_mapL, ← TensorProduct.mapL_comp]

/-- Local dilations preserve every bipartite Born expectation. The tensor
embedding is `TensorProduct.mapIsometry`, so it also preserves unit states. -/
theorem inner_tensor_compression (V₁ : H₁ →ₗᵢ[ℂ] K₁) (V₂ : H₂ →ₗᵢ[ℂ] K₂)
    (P : K₁ →L[ℂ] K₁) (Q : K₂ →L[ℂ] K₂)
    (E : H₁ →L[ℂ] H₁) (F : H₂ →L[ℂ] H₂)
    (hE : V₁.toContinuousLinearMap.adjoint ∘L P ∘L V₁.toContinuousLinearMap = E)
    (hF : V₂.toContinuousLinearMap.adjoint ∘L Q ∘L V₂.toContinuousLinearMap = F)
    (ξ ζ : H₁ ⊗[ℂ] H₂) :
    inner ℂ (TensorProduct.mapIsometry V₁ V₂ ξ)
        (TensorProduct.mapL P Q (TensorProduct.mapIsometry V₁ V₂ ζ)) =
      inner ℂ ξ (TensorProduct.mapL E F ζ) := by
  let V := (TensorProduct.mapIsometry V₁ V₂).toContinuousLinearMap
  change inner ℂ (V ξ) (TensorProduct.mapL P Q (V ζ)) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ξ ((V.adjoint ∘L TensorProduct.mapL P Q ∘L V) ζ) = _
  rw [tensor_compression, hE, hF]

/-- The real Born probabilities are unchanged by local compression. -/
theorem re_inner_tensor_compression (V₁ : H₁ →ₗᵢ[ℂ] K₁) (V₂ : H₂ →ₗᵢ[ℂ] K₂)
    (P : K₁ →L[ℂ] K₁) (Q : K₂ →L[ℂ] K₂)
    (E : H₁ →L[ℂ] H₁) (F : H₂ →L[ℂ] H₂)
    (hE : V₁.toContinuousLinearMap.adjoint ∘L P ∘L V₁.toContinuousLinearMap = E)
    (hF : V₂.toContinuousLinearMap.adjoint ∘L Q ∘L V₂.toContinuousLinearMap = F)
    (ξ : H₁ ⊗[ℂ] H₂) :
    (inner ℂ (TensorProduct.mapIsometry V₁ V₂ ξ)
        (P.rTensor K₂ (Q.lTensor K₁ (TensorProduct.mapIsometry V₁ V₂ ξ)))).re =
      (inner ℂ ξ (E.rTensor H₂ (F.lTensor H₁ ξ))).re :=
  congrArg Complex.re (inner_tensor_compression V₁ V₂ P Q E F hE hF ξ ξ)

/-- The bilinear form version of local compression implies operator compression. -/
theorem compression_eq_of_inner (V : H₁ →ₗᵢ[ℂ] K₁)
    (P : K₁ →L[ℂ] K₁) (E : H₁ →L[ℂ] H₁)
    (h : ∀ ξ ζ, inner ℂ (V ξ) (P (V ζ)) = inner ℂ ξ (E ζ)) :
    V.toContinuousLinearMap.adjoint ∘L P ∘L V.toContinuousLinearMap = E := by
  ext ζ
  apply ext_inner_left ℂ
  intro ξ
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, LinearIsometry.coe_toContinuousLinearMap] using
      h ξ ζ

/-- Tensor compression expressed directly by the local bilinear form identities
supplied by a Naimark dilation. -/
theorem inner_tensor_compression_of_inner (V₁ : H₁ →ₗᵢ[ℂ] K₁)
    (V₂ : H₂ →ₗᵢ[ℂ] K₂) (P : K₁ →L[ℂ] K₁) (Q : K₂ →L[ℂ] K₂)
    (E : H₁ →L[ℂ] H₁) (F : H₂ →L[ℂ] H₂)
    (hE : ∀ ξ ζ, inner ℂ (V₁ ξ) (P (V₁ ζ)) = inner ℂ ξ (E ζ))
    (hF : ∀ ξ ζ, inner ℂ (V₂ ξ) (Q (V₂ ζ)) = inner ℂ ξ (F ζ))
    (ξ ζ : H₁ ⊗[ℂ] H₂) :
    inner ℂ (TensorProduct.mapIsometry V₁ V₂ ξ)
        (TensorProduct.mapL P Q (TensorProduct.mapIsometry V₁ V₂ ζ)) =
      inner ℂ ξ (TensorProduct.mapL E F ζ) :=
  inner_tensor_compression V₁ V₂ P Q E F
    (compression_eq_of_inner V₁ P E hE) (compression_eq_of_inner V₂ Q F hF) ξ ζ

/-- Equality of real tensor expectations from local bilinear form identities. -/
theorem re_inner_tensor_compression_of_inner (V₁ : H₁ →ₗᵢ[ℂ] K₁)
    (V₂ : H₂ →ₗᵢ[ℂ] K₂) (P : K₁ →L[ℂ] K₁) (Q : K₂ →L[ℂ] K₂)
    (E : H₁ →L[ℂ] H₁) (F : H₂ →L[ℂ] H₂)
    (hE : ∀ ξ ζ, inner ℂ (V₁ ξ) (P (V₁ ζ)) = inner ℂ ξ (E ζ))
    (hF : ∀ ξ ζ, inner ℂ (V₂ ξ) (Q (V₂ ζ)) = inner ℂ ξ (F ζ))
    (ξ : H₁ ⊗[ℂ] H₂) :
    (inner ℂ (TensorProduct.mapIsometry V₁ V₂ ξ)
        (TensorProduct.mapL P Q (TensorProduct.mapIsometry V₁ V₂ ξ))).re =
      (inner ℂ ξ (TensorProduct.mapL E F ξ)).re :=
  congrArg Complex.re (inner_tensor_compression_of_inner V₁ V₂ P Q E F hE hF ξ ξ)

end ThomGame.Quantum
