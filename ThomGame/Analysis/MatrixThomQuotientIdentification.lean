module

public import ThomGame.Analysis.MatrixThomCorrectedStabilization

/-!
# One trace-preserving ambient identification for both corrected algebras

The source-frame equivalence followed by the inverse target-frame
equivalence identifies the original d-dimensional and corrected
m-dimensional matrix quotients. Both internal A and internal B are
transported by this same equivalence.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem starAlgEquiv_mem_map_iff {R T : Type*} [Semiring R] [Semiring T]
    [StarRing R] [StarRing T] [Algebra ℂ R] [Algebra ℂ T] [StarModule ℂ R] [StarModule ℂ T]
    (e : R ≃⋆ₐ[ℂ] T) (C : StarSubalgebra ℂ R) (x : R) :
    e x ∈ C.map e.toStarAlgHom ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact (e.injective he) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {ι : Type*} (dims : ι → Nat) [∀ i, NeZero (dims i)]
    {A B D : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i))} {ε : ι → ℝ}
    (S : (i : ι) → MatrixThomSpectralData (A i) (B i) (D i) (ε i))
    (L : Filter ι) (hε : Tendsto ε L (𝓝 0)) (hm : ∀ i, 0 < (S i).cut.rank)

noncomputable def matrixThomQuotientEquiv :
    MatrixTracialQuotient dims L ≃⋆ₐ[ℂ] MatrixTracialQuotient (fun i => (S i).cut.rank) L :=
  (matrixThomOriginalQuotientEquiv dims S L hε).trans
    (matrixThomCorrectedQuotientEquiv dims S L hε hm).symm

theorem matrixThomQuotientEquiv_stable (x : MatrixTracialQuotient dims L) :
    matrixThomCorrectedQuotientEquiv dims S L hε hm (matrixThomQuotientEquiv dims S L hε hm x) =
      matrixThomOriginalQuotientEquiv dims S L hε x := by
  simp only [matrixThomQuotientEquiv, StarAlgEquiv.trans_apply, StarAlgEquiv.apply_symm_apply]

theorem matrixThomQuotientEquiv_internal_iff
    (C : (i : ι) → StarSubalgebra ℂ (CMatrix (dims i)))
    (C' : (i : ι) → StarSubalgebra ℂ (CMatrix (S i).cut.rank))
    (hCC : matrixInternalQuotient (fun i => (S i).stableDim) (fun i => (S i).stableOriginalAlgebra (C i)) L =
      matrixInternalQuotient (fun i => (S i).stableDim) (fun i => (S i).stableCorrectedAlgebra (C' i)) L)
    (x : MatrixTracialQuotient dims L) :
    matrixThomQuotientEquiv dims S L hε hm x ∈ matrixInternalQuotient (fun i => (S i).cut.rank) C' L ↔
      x ∈ matrixInternalQuotient dims C L := by
  have hs := starAlgEquiv_mem_map_iff (matrixThomOriginalQuotientEquiv dims S L hε)
    (matrixInternalQuotient dims C L) x
  rw [matrixThomOriginalQuotientEquiv_internal_map, hCC] at hs
  have ht := starAlgEquiv_mem_map_iff (matrixThomCorrectedQuotientEquiv dims S L hε hm)
    (matrixInternalQuotient (fun i => (S i).cut.rank) C' L) (matrixThomQuotientEquiv dims S L hε hm x)
  rw [matrixThomCorrectedQuotientEquiv_internal_map, matrixThomQuotientEquiv_stable] at ht
  exact ht.symm.trans hs

theorem matrixThomQuotientEquiv_A_iff (hε0 : ∀ i, 0 ≤ ε i) (x : MatrixTracialQuotient dims L) :
    matrixThomQuotientEquiv dims S L hε hm x ∈
        matrixInternalQuotient (fun i => (S i).cut.rank) (fun i => (S i).correctedTargetAlgebra) L ↔
      x ∈ matrixInternalQuotient dims A L :=
  matrixThomQuotientEquiv_internal_iff dims S L hε hm A (fun i => (S i).correctedTargetAlgebra)
    (matrixThom_stable_A_internal_eq dims S hε hε0) x

theorem matrixThomQuotientEquiv_B_iff (hε0 : ∀ i, 0 ≤ ε i)
    (hBA : ∀ i, MatrixNearInclusion (B i) (A i) (ε i)) (x : MatrixTracialQuotient dims L) :
    matrixThomQuotientEquiv dims S L hε hm x ∈
        matrixInternalQuotient (fun i => (S i).cut.rank) (fun i => (S i).correctedSourceAlgebra) L ↔
      x ∈ matrixInternalQuotient dims B L :=
  matrixThomQuotientEquiv_internal_iff dims S L hε hm B (fun i => (S i).correctedSourceAlgebra)
    (matrixThom_stable_B_internal_eq dims S hε hε0 hBA) x

theorem matrixThomQuotientEquiv_trace (U : Ultrafilter ι)
    (hεU : Tendsto ε (U : Filter ι) (𝓝 0)) (x : MatrixTracialQuotient dims (U : Filter ι)) :
    matrixUltratrace (fun i => (S i).cut.rank) hm U
        (matrixThomQuotientEquiv dims S (U : Filter ι) hεU hm x) =
      matrixUltratrace dims (fun i => NeZero.pos (dims i)) U x := by
  have ht := matrixThomCorrectedQuotientEquiv_trace dims S hm U hεU
    (matrixThomQuotientEquiv dims S (U : Filter ι) hεU hm x)
  rw [matrixThomQuotientEquiv_stable] at ht
  exact ht.symm.trans (matrixThomOriginalQuotientEquiv_trace dims S U hεU x)

end ThomGame.Analysis
