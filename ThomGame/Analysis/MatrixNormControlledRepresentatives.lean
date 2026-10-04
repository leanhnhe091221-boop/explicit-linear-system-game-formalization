module

public import ThomGame.Analysis.MatrixOperatorProduct
public import ThomGame.Analysis.CStarNormLift
public import ThomGame.Analysis.MatrixFiniteOperatorAlgebra

/-!
# Representatives controlled by the norm of the represented operator

The supremum norm product maps to the concrete finite operator algebra.
Clipping self-adjoint parts in this genuine C-star algebra domain gives
matrix representatives bounded by twice the norm of the image. This
uses no norm or completeness assumption on the algebraic quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i) (U : Ultrafilter ι)

noncomputable def matrixProductToFinite :
    MatrixOperatorProduct dims hd →⋆ₐ[ℂ] MatrixFiniteOperatorAlgebra dims hd U :=
  (matrixFiniteEmbedding dims hd U).comp
    ((matrixQuotientStarAlgHom dims (U : Filter ι)).comp (matrixOperatorProductEquiv dims hd).toStarAlgHom)

theorem matrixProductToFinite_apply (A : MatrixOperatorProduct dims hd) :
    matrixProductToFinite dims hd U A = matrixFiniteEmbedding dims hd U
      (matrixQuotientMk dims (U : Filter ι) (matrixOperatorProductEquiv dims hd A)) := rfl

theorem matrixFiniteEmbedding_norm (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ‖matrixFiniteEmbedding dims hd U x‖ = ‖matrixLeftRepresentation dims hd U x‖ := rfl

theorem exists_matrixRepresentative_bounded (x : MatrixTracialQuotient dims (U : Filter ι))
    (K : ℝ) (hK : 0 ≤ K) (hx : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, (∀ i, matrixOpNorm (B.val i) ≤ 2 * K) ∧
      matrixQuotientMk dims (U : Filter ι) B = x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  let p := (matrixOperatorProductEquiv dims hd).symm A
  have hp : matrixProductToFinite dims hd U p =
      matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A) := by
    rw [matrixProductToFinite_apply, show matrixOperatorProductEquiv dims hd p = A from
      (matrixOperatorProductEquiv dims hd).apply_symm_apply A]
  obtain ⟨b, hb, heq⟩ := exists_cstar_norm_lift (matrixProductToFinite dims hd U) p K hK
    (by rw [hp, matrixFiniteEmbedding_norm]; exact hx)
  refine ⟨matrixOperatorProductEquiv dims hd b, ?_, ?_⟩
  · intro i
    exact (matrixOperatorProduct_apply_norm_le dims hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    rw [← matrixProductToFinite_apply, ← hp]
    exact heq

theorem exists_matrixRepresentative_norm_le (x : MatrixTracialQuotient dims (U : Filter ι)) :
    ∃ B : BoundedMatrixSequence dims,
      (∀ i, matrixOpNorm (B.val i) ≤ 2 * ‖matrixLeftRepresentation dims hd U x‖) ∧
      matrixQuotientMk dims (U : Filter ι) B = x :=
  exists_matrixRepresentative_bounded dims hd U x _ (norm_nonneg _) le_rfl

theorem exists_matrixSelfAdjointRepresentative_bounded
    (x : MatrixTracialQuotient dims (U : Filter ι)) (hx : IsSelfAdjoint x)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ‖matrixLeftRepresentation dims hd U x‖ ≤ K) :
    ∃ B : BoundedMatrixSequence dims, IsSelfAdjoint B ∧
      (∀ i, matrixOpNorm (B.val i) ≤ K) ∧ matrixQuotientMk dims (U : Filter ι) B = x := by
  obtain ⟨A, rfl⟩ := matrixQuotientMk_surjective dims (U : Filter ι) x
  let p := (matrixOperatorProductEquiv dims hd).symm A
  let φ := matrixProductToFinite dims hd U
  have hp : φ p = matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A) := by
    rw [show φ p = matrixProductToFinite dims hd U p from rfl, matrixProductToFinite_apply,
      show matrixOperatorProductEquiv dims hd p = A from
        (matrixOperatorProductEquiv dims hd).apply_symm_apply A]
  have hsp : IsSelfAdjoint (φ p) := hp ▸ hx.map (matrixFiniteEmbedding dims hd U)
  have hreal : φ (realPart p : MatrixOperatorProduct dims hd) = φ p := by
    rw [map_realPart, hsp.coe_realPart]
  obtain ⟨b, hbs, hb, heq⟩ := exists_selfAdjoint_norm_lift φ (realPart p) (realPart p).property K hK
    (by rw [hreal, hp, matrixFiniteEmbedding_norm]; exact hbound)
  refine ⟨matrixOperatorProductEquiv dims hd b, hbs.map (matrixOperatorProductEquiv dims hd), ?_, ?_⟩
  · intro i
    exact (matrixOperatorProduct_apply_norm_le dims hd b i).trans hb
  · apply matrixFiniteEmbedding_injective dims hd U
    change φ b = matrixFiniteEmbedding dims hd U (matrixQuotientMk dims (U : Filter ι) A)
    rw [heq, hreal, hp]

end ThomGame.Analysis
