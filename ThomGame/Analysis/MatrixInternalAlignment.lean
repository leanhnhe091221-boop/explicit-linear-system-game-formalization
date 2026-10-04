module

public import ThomGame.Analysis.MatrixThomGeneralQuotient
public import ThomGame.Analysis.MatrixInternalNearInclusion

/-!
# Simultaneous nested representatives for an actual internal inclusion

The original coordinate algebras need not be nested. The proved relative
Thom correction, with scalar common algebra, constructs nested algebras
in asymptotically equal positive dimensions and a single trace-preserving
ambient equivalence representing both original internal algebras.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

theorem exists_matrixInternal_nested_realization {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))) (L : Ultrafilter ι)
    (hDA : matrixInternalQuotient dims D (L : Filter ι) ≤ matrixInternalQuotient dims A (L : Filter ι)) :
    ∃ m : ι → Nat, ∃ hm : ∀ n, 0 < m n,
      ∃ A' D' : (n : ι) → StarSubalgebra ℂ (CMatrix (m n)),
      ∃ e : MatrixTracialQuotient dims (L : Filter ι) ≃⋆ₐ[ℂ] MatrixTracialQuotient m (L : Filter ι),
      (∀ n, D' n ≤ A' n) ∧
      Tendsto (fun n => (m n : ℝ) / dims n) (L : Filter ι) (𝓝 1) ∧
      (∀ x, e x ∈ matrixInternalQuotient m A' (L : Filter ι) ↔
        x ∈ matrixInternalQuotient dims A (L : Filter ι)) ∧
      (∀ x, e x ∈ matrixInternalQuotient m D' (L : Filter ι) ↔
        x ∈ matrixInternalQuotient dims D (L : Filter ι)) ∧
      ∀ x, matrixUltratrace m hm L (e x) =
        matrixUltratrace dims (fun n => NeZero.pos (dims n)) L x := by
  obtain ⟨ε, hε0, hε, hnear⟩ := exists_matrixNearInclusion_errors_of_internal_le dims D A
    (fun n => NeZero.pos (dims n)) (L : Filter ι) hDA
  obtain ⟨S⟩ := exists_matrixThomModifiedData dims A D (fun _ => ⊥) ε
    (fun _ => bot_le) (fun _ => bot_le) hε0 hnear
  refine ⟨fun n => (S n).cut.rank, matrixThomModified_cut_rank_pos dims S hε0,
    (fun n => (S n).correctedTargetAlgebra), (fun n => (S n).correctedSourceAlgebra),
    matrixThomGeneralQuotientEquiv dims S (L : Filter ι) hε hε0,
    (fun n => (S n).correctedSourceAlgebra_le_target),
    matrixThomModified_dimension_ratio_tendsto dims S (L : Filter ι) hε,
    matrixThomGeneralQuotientEquiv_A_iff dims S (L : Filter ι) hε hε0,
    matrixThomGeneralQuotientEquiv_B_iff dims S (L : Filter ι) hε hε0 hnear,
    matrixThomGeneralQuotientEquiv_trace dims S hε0 L hε⟩

end ThomGame.Analysis
