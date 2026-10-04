module

public import ThomGame.Analysis.MatrixInternalUnitaryLifting
public import ThomGame.Analysis.MatrixFiniteInternalCommutants
public import ThomGame.Analysis.UnitaryFiniteEquivalence

/-!
# Internal and exactly commuting unitary lifts of finite-algebra unitaries

The constructed weakly closed finite operator algebra is identified with
the original matrix quotient. Its internal unitaries and commutant
unitaries therefore admit exact lifts in the prescribed coordinates.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

include hL

theorem exists_matrixFiniteInternal_unitary_lift (u : unitary (MatrixFiniteOperatorAlgebra dims hd L))
    (hu : u.val ∈ matrixInternalFiniteAlgebra dims S hd L) :
    ∃ U : UnitarySequence dims, (∀ n, (U n).val ∈ S n) ∧
      matrixFiniteEmbedding dims hd L (matrixQuotientMk dims (L : Filter Nat) (boundedUnitarySequence dims U)) = u.val := by
  let e := matrixFiniteEquiv dims hd L hL
  let x : unitary (MatrixTracialQuotient dims (L : Filter Nat)) :=
    ⟨e.symm u.val, Unitary.map_mem e.symm u.property⟩
  have hxe : matrixFiniteEmbedding dims hd L x.val = u.val := e.apply_symm_apply u.val
  have hx : x.val ∈ matrixInternalQuotient dims S (L : Filter Nat) := by
    apply (matrixFiniteEmbedding_mem_internal_iff dims S hd L x.val).mp
    rwa [hxe]
  obtain ⟨U, hUS, hU⟩ := exists_matrixInternal_unitary_lift dims S hd (L : Filter Nat) x hx
  exact ⟨U, hUS, (congrArg (matrixFiniteEmbedding dims hd L) hU).trans hxe⟩

theorem exists_matrixFiniteInternalCommutant_unitary_lift (u : unitary (MatrixFiniteOperatorAlgebra dims hd L))
    (hu : u.val ∈ StarSubalgebra.centralizer ℂ
      (matrixInternalFiniteAlgebra dims S hd L : Set (MatrixFiniteOperatorAlgebra dims hd L))) :
    ∃ U : UnitarySequence dims, (∀ n X, X ∈ S n → X * (U n).val = (U n).val * X) ∧
      matrixFiniteEmbedding dims hd L (matrixQuotientMk dims (L : Filter Nat) (boundedUnitarySequence dims U)) = u.val := by
  rw [matrixInternalFiniteAlgebra_commutant dims S hd L hL] at hu
  obtain ⟨U, hUS, hU⟩ := exists_matrixFiniteInternal_unitary_lift dims
    (fun n => StarSubalgebra.centralizer ℂ (S n : Set (CMatrix (dims n)))) hd L hL u hu
  exact ⟨U, fun n => (mem_matrixSubalgebraCommutant_iff (S n) (U n).val).mp (hUS n), hU⟩

end ThomGame.Analysis
