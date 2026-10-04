module

public import ThomGame.Analysis.MatrixInternalAlignment
public import ThomGame.Analysis.MatrixThomUnitaryTheorem4_2

/-!
# Normalization with independently presented internal algebras

The anchor supplies an internal inclusion, which is aligned by the
actual tracial correction. The entire tuple is transported by the same
ambient equivalence and has exactly commuting lifts. Thom Theorem 4.2
then gives equality, which is pulled back to the original quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem matrixThom_internal_normalization {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)]
    (A D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n))) (L : Ultrafilter ι) {h : Nat}
    (u : Fin h → unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (hincl : ∀ j, (matrixInternalQuotient dims A (L : Filter ι)).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims (L : Filter ι)) (u j)).symm.toStarAlgHom ≤
      matrixInternalQuotient dims A (L : Filter ι))
    (hanchor : matrixInternalQuotient dims A (L : Filter ι) ⊓
      StarSubalgebra.centralizer ℂ (Set.range (fun j => (u j).val)) =
        matrixInternalQuotient dims D (L : Filter ι)) :
    ∀ j, (matrixInternalQuotient dims A (L : Filter ι)).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims (L : Filter ι)) (u j)).symm.toStarAlgHom =
      matrixInternalQuotient dims A (L : Filter ι) := by
  have hDA : matrixInternalQuotient dims D (L : Filter ι) ≤ matrixInternalQuotient dims A (L : Filter ι) := by
    rw [← hanchor]
    exact inf_le_left
  obtain ⟨m, hm, C, E, e, hEC, _, hA, hD, _⟩ := exists_matrixInternal_nested_realization dims A D L hDA
  let : ∀ n, NeZero (m n) := fun n => ⟨ne_of_gt (hm n)⟩
  let v := fun j => starAlgHomUnitary e.toStarAlgHom (u j)
  have ha : matrixInternalQuotient m C (L : Filter ι) ⊓
      StarSubalgebra.centralizer ℂ (Set.range (fun j => (v j).val)) =
        matrixInternalQuotient m E (L : Filter ι) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change (e x ∈ matrixInternalQuotient m C (L : Filter ι) ∧
      e x ∈ StarSubalgebra.centralizer ℂ (Set.range (fun j => (v j).val))) ↔
        e x ∈ matrixInternalQuotient m E (L : Filter ι)
    rw [hA, hD, starAlgEquiv_unitaryCommutant_mem_iff e u x]
    exact SetLike.ext_iff.mp hanchor x
  have hi j : (matrixInternalQuotient m C (L : Filter ι)).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient m (L : Filter ι)) (v j)).symm.toStarAlgHom ≤
        matrixInternalQuotient m C (L : Filter ι) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective z
    change (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient m (L : Filter ι))
      (starAlgHomUnitary e.toStarAlgHom (u j))).symm (e x) ∈ _
    rw [← starAlgEquiv_unitaryPullback_apply]
    exact (hA _).mpr (hincl j ⟨x, (hA x).mp hz, rfl⟩)
  have he := matrixThom_theorem_4_2_of_unitaries m C E hEC (L : Filter ι) v hi ha
  intro j
  apply le_antisymm (hincl j)
  intro x hx
  have hx' : e x ∈ (matrixInternalQuotient m C (L : Filter ι)).map
      (Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient m (L : Filter ι)) (v j)).symm.toStarAlgHom := by
    rw [he j]
    exact (hA x).mpr hx
  obtain ⟨z, hz, hzx⟩ := hx'
  obtain ⟨y, rfl⟩ := e.surjective z
  refine ⟨y, (hA y).mp hz, ?_⟩
  apply e.injective
  change e ((Unitary.conjStarAlgAut ℂ (MatrixTracialQuotient dims (L : Filter ι)) (u j)).symm y) = e x
  rw [starAlgEquiv_unitaryPullback_apply]
  exact hzx

end ThomGame.Analysis
