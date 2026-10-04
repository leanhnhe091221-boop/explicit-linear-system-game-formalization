module

public import ThomGame.Analysis.MatrixFrameQuotientTrace
public import ThomGame.Analysis.MatrixInternalSequences

/-!
# Stabilization identifies each original internal algebra with its scalar extension

The same ambient star equivalence works simultaneously for every chosen
coordinate subalgebra. Compression of scalar extensions gives the
surjective inverse on their actual bounded representatives.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {ι : Type*} (dims large : ι → Nat)
    (F : (i : ι) → Matrix (Fin (large i)) (Fin (dims i)) ℂ)
    (hF : ∀ i, (F i)ᴴ * F i = 1) (hd : ∀ i, 0 < dims i) (hN : ∀ i, 0 < large i)
    (L : Filter ι) (hratio : Tendsto (fun i => (large i : ℝ) / dims i) L (𝓝 1))
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))

theorem matrixFrameQuotientHom_internal_mem (x : MatrixTracialQuotient dims L)
    (hx : x ∈ matrixInternalQuotient dims C L) :
    matrixFrameQuotientHom dims large F hF hd hN L hratio x ∈
      matrixInternalQuotient large (fun i => matrixFrameScalarAlgebra (C i) (F i) (hF i)) L := by
  obtain ⟨A, hA, rfl⟩ := (mem_matrixInternalQuotient dims C L x).mp hx
  exact ⟨matrixFrameSequenceLift dims large F hF A,
    fun i => matrixFrameScalarAlgebra_lift_mem (C i) (F i) (hF i) (A.val i) (hA i), rfl⟩

noncomputable def matrixFrameInternalHom :
    matrixInternalQuotient dims C L →⋆ₐ[ℂ]
      matrixInternalQuotient large (fun i => matrixFrameScalarAlgebra (C i) (F i) (hF i)) L :=
  ((matrixFrameQuotientHom dims large F hF hd hN L hratio).comp (matrixInternalQuotient dims C L).subtype).codRestrict _
    (fun x => matrixFrameQuotientHom_internal_mem dims large F hF hd hN L hratio C x.val x.property)

theorem matrixFrameInternalHom_bijective :
    Function.Bijective (matrixFrameInternalHom dims large F hF hd hN L hratio C) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact matrixFrameQuotientHom_injective dims large F hF hd hN L hratio (congrArg Subtype.val h)
  · intro y
    obtain ⟨A, hA, he⟩ := (mem_matrixInternalQuotient large _ L y.val).mp y.property
    let B := matrixFrameSequenceCompression dims large F hF A
    have hB : matrixQuotientMk dims L B ∈ matrixInternalQuotient dims C L :=
      ⟨B, fun i => matrixFrameScalarAlgebra_compression_mem (C i) (F i) (hF i) (A.val i) (hA i), rfl⟩
    refine ⟨⟨matrixQuotientMk dims L B, hB⟩, ?_⟩
    apply Subtype.ext
    exact (matrixFrameSequence_lift_compression_mk dims large F hF hN L hratio A).trans he

noncomputable def matrixFrameInternalEquiv :
    matrixInternalQuotient dims C L ≃⋆ₐ[ℂ]
      matrixInternalQuotient large (fun i => matrixFrameScalarAlgebra (C i) (F i) (hF i)) L :=
  StarAlgEquiv.ofBijective (matrixFrameInternalHom dims large F hF hd hN L hratio C)
    (matrixFrameInternalHom_bijective dims large F hF hd hN L hratio C)

@[simp] theorem matrixFrameInternalEquiv_val (x : matrixInternalQuotient dims C L) :
    (matrixFrameInternalEquiv dims large F hF hd hN L hratio C x).val =
      matrixFrameQuotientEquiv dims large F hF hd hN L hratio x.val := rfl

theorem matrixFrameQuotientHom_internal_map :
    (matrixInternalQuotient dims C L).map (matrixFrameQuotientHom dims large F hF hd hN L hratio) =
      matrixInternalQuotient large (fun i => matrixFrameScalarAlgebra (C i) (F i) (hF i)) L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact matrixFrameQuotientHom_internal_mem dims large F hF hd hN L hratio C x hx
  · intro hy
    obtain ⟨x, hx⟩ := (matrixFrameInternalHom_bijective dims large F hF hd hN L hratio C).2 ⟨y, hy⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

end ThomGame.Analysis
