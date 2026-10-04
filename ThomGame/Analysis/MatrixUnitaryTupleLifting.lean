module

public import ThomGame.Analysis.MatrixUnitaryLifting
public import ThomGame.Analysis.MatrixMarkovCommutant

/-! Exact coordinate unitary representatives for a tuple in the genuine tracial quotient. -/

@[expose] public section
namespace ThomGame.Analysis

open Filter

theorem exists_matrixTuple_unitary_lift {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i)
    (L : Filter ι) {h : Nat} (u : Fin h → unitary (MatrixTracialQuotient dims L)) :
    ∃ V : (i : ι) → Fin h → UnitaryMatrix (dims i),
      ∀ j, matrixTupleClass dims V L j = (u j).val := by
  choose V hV using fun j => exists_matrixQuotient_unitary_lift dims hd L (u j)
  exact ⟨fun i j => V j i, hV⟩

end ThomGame.Analysis
