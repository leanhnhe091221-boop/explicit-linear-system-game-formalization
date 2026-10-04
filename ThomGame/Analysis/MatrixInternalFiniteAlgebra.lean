module

public import ThomGame.Analysis.MatrixInternalWOTIdentification

/-!
# The concrete finite algebra of an internal matrix subalgebra

The internal image inherits the actual operator norm and faithful trace.
For the natural number hyperfilter it is a complete C-star algebra, and
both the finite and weak closure identifications preserve the original
matrix ultratrace.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat)
  (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

noncomputable def matrixInternalFiniteAlgebra : StarSubalgebra ℂ (MatrixFiniteOperatorAlgebra dims hd U) :=
  StarSubalgebra.map (matrixFiniteEmbedding dims hd U) (matrixInternalQuotient dims S (U : Filter Nat))

theorem mem_matrixInternalFiniteAlgebra (T : MatrixFiniteOperatorAlgebra dims hd U) :
    T ∈ matrixInternalFiniteAlgebra dims S hd U ↔
      ContinuousLinearMapWOT.ofCLM T.val ∈ matrixInternalWOTAlgebra dims S hd U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    exact ⟨x, hx, Subtype.ext (congrArg ContinuousLinearMapWOT.toCLM hxe)⟩

theorem matrixInternalFiniteAlgebra_isClosed (hU : (U : Filter Nat) ≤ atTop) :
    IsClosed (matrixInternalFiniteAlgebra dims S hd U : Set (MatrixFiniteOperatorAlgebra dims hd U)) := by
  have he : (matrixInternalFiniteAlgebra dims S hd U : Set _) =
      (fun T : MatrixFiniteOperatorAlgebra dims hd U => ContinuousLinearMapWOT.ofCLM T.val) ⁻¹'
        (matrixInternalWOTAlgebra dims S hd U : Set _) := by
    ext T
    exact mem_matrixInternalFiniteAlgebra dims S hd U T
  rw [he]
  exact (matrixInternalWOTAlgebra_isClosed dims S hd U hU).preimage
    (ContinuousLinearMapWOT.continuous_ofCLM.comp continuous_subtype_val)

instance matrixInternalFiniteAlgebra_hyperfilter_isClosed :
    IsClosed (matrixInternalFiniteAlgebra dims S hd (hyperfilter Nat) :
      Set (MatrixFiniteOperatorAlgebra dims hd (hyperfilter Nat))) :=
  matrixInternalFiniteAlgebra_isClosed dims S hd (hyperfilter Nat) Nat.hyperfilter_le_atTop

noncomputable abbrev MatrixInternalFiniteCStarAlgebra := matrixInternalFiniteAlgebra dims S hd (hyperfilter Nat)

noncomputable def matrixInternalFiniteEmbedding :
    matrixInternalQuotient dims S (U : Filter Nat) →⋆ₐ[ℂ] matrixInternalFiniteAlgebra dims S hd U :=
  ((matrixFiniteEmbedding dims hd U).comp (matrixInternalQuotient dims S (U : Filter Nat)).subtype).codRestrict _
    (fun x => ⟨x.val, x.property, rfl⟩)

theorem matrixInternalFiniteEmbedding_bijective :
    Function.Bijective (matrixInternalFiniteEmbedding dims S hd U) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact matrixFiniteEmbedding_injective dims hd U (congrArg Subtype.val h)
  · intro T
    obtain ⟨x, hx, heq⟩ := T.property
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩

noncomputable def matrixInternalFiniteEquiv :
    matrixInternalQuotient dims S (U : Filter Nat) ≃⋆ₐ[ℂ] matrixInternalFiniteAlgebra dims S hd U :=
  StarAlgEquiv.ofBijective (matrixInternalFiniteEmbedding dims S hd U)
    (matrixInternalFiniteEmbedding_bijective dims S hd U)

noncomputable def matrixInternalFiniteTrace : matrixInternalFiniteAlgebra dims S hd U →L[ℂ] ℂ :=
  (matrixFiniteTrace dims hd U).comp
    ⟨(matrixInternalFiniteAlgebra dims S hd U).subtype.toAlgHom.toLinearMap, continuous_subtype_val⟩

theorem matrixInternalFiniteEquiv_trace (x : matrixInternalQuotient dims S (U : Filter Nat)) :
    matrixInternalFiniteTrace dims S hd U (matrixInternalFiniteEquiv dims S hd U x) =
      matrixUltratrace dims hd U x.val :=
  matrixFiniteTrace_embedding dims hd U x.val

@[simp] theorem matrixInternalFiniteTrace_one : matrixInternalFiniteTrace dims S hd U 1 = 1 :=
  matrixFiniteTrace_one dims hd U

theorem matrixInternalFiniteTrace_mul_comm (A B : matrixInternalFiniteAlgebra dims S hd U) :
    matrixInternalFiniteTrace dims S hd U (A * B) = matrixInternalFiniteTrace dims S hd U (B * A) :=
  matrixFiniteTrace_mul_comm dims hd U A.val B.val

theorem matrixInternalFiniteTrace_gram_nonneg (A : matrixInternalFiniteAlgebra dims S hd U) :
    0 ≤ (matrixInternalFiniteTrace dims S hd U (star A * A)).re :=
  matrixFiniteTrace_gram_nonneg dims hd U A.val

theorem matrixInternalFiniteTrace_faithful (A : matrixInternalFiniteAlgebra dims S hd U) :
    matrixInternalFiniteTrace dims S hd U (star A * A) = 0 ↔ A = 0 := by
  change matrixFiniteTrace dims hd U (star A.val * A.val) = 0 ↔ A = 0
  rw [matrixFiniteTrace_faithful]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

noncomputable def matrixInternalWOTClosureInclusion :
    (matrixInternalWOTAlgebra dims S hd U).topologicalClosure →⋆ₐ[ℂ] MatrixWOTClosure dims hd U :=
  StarSubalgebra.inclusion (matrixInternalWOTAlgebra_closure_le dims S hd U)

theorem matrixInternalWOTEquiv_trace (hU : (U : Filter Nat) ≤ atTop)
    (x : matrixInternalQuotient dims S (U : Filter Nat)) :
    matrixWOTTrace dims hd U
      (matrixInternalWOTClosureInclusion dims S hd U (matrixInternalWOTEquiv dims S hd U hU x)) =
      matrixUltratrace dims hd U x.val :=
  matrixWOTTrace_embedding dims hd U x.val

end ThomGame.Analysis
