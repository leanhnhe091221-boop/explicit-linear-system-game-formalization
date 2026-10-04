module

public import ThomGame.Analysis.MatrixMarkovProjection
public import Mathlib.Algebra.Star.Subalgebra

/-!
# The relative commutant and its entire trace Hilbert space

The tuple classes are actual unitaries. Their common commutant is a
star subalgebra, whose trace closure is exactly the full fixed space
of the lazy Markov operator. Boundedness of the mean ergodic projection
supplies the reverse inclusion without assuming internality or a gap.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter

variable {ι : Type*} (dims : ι → Nat) {h : Nat}
  (U : (i : ι) → Fin h → UnitaryMatrix (dims i))

theorem matrixTupleClass_unitary (L : Filter ι) (j : Fin h) :
    matrixTupleClass dims U L j ∈ unitary (MatrixTracialQuotient dims L) := by
  constructor
  · rw [matrixTupleClass, matrixQuotientMk_star, ← map_mul,
      boundedUnitarySequence_star_mul, map_one]
  · rw [matrixTupleClass, matrixQuotientMk_star, ← map_mul,
      boundedUnitarySequence_mul_star, map_one]

def matrixRelativeCommutant (L : Filter ι) : StarSubalgebra ℂ (MatrixTracialQuotient dims L) :=
  StarSubalgebra.centralizer ℂ (Set.range (matrixTupleClass dims U L))

theorem mem_matrixRelativeCommutant_iff (L : Filter ι) (x : MatrixTracialQuotient dims L) :
    x ∈ matrixRelativeCommutant dims U L ↔ ∀ j, Commute (matrixTupleClass dims U L j) x := by
  rw [matrixRelativeCommutant, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro hx j
    exact (hx _ ⟨j, rfl⟩).1
  · intro hx g hg
    obtain ⟨j, rfl⟩ := hg
    refine ⟨(hx j).eq, ?_⟩
    have hu := matrixTupleClass_unitary dims U L j
    have he := (commute_unitary_iff_star_left_conjugate hu).mp (hx j)
    exact ((commute_unitary_iff_star_right_conjugate (Unitary.star_mem hu)).mpr
      (by simpa only [star_star] using he)).eq

variable (hd : ∀ i, 0 < dims i) (L : Ultrafilter ι)

noncomputable def matrixRelativeCommutantTraceSubspace : Submodule ℂ (MatrixTraceHilbert dims hd L) :=
  ((matrixRelativeCommutant dims U (L : Filter ι)).toSubalgebra.toSubmodule.map
    (matrixHilbertEmbedding dims hd L)).topologicalClosure

instance matrixRelativeCommutantTraceSubspace_isClosed :
    IsClosed (matrixRelativeCommutantTraceSubspace dims U hd L : Set (MatrixTraceHilbert dims hd L)) :=
  Submodule.isClosed_topologicalClosure _

theorem matrixHilbertEmbedding_mem_relativeCommutantTraceSubspace
    (x : MatrixTracialQuotient dims (L : Filter ι)) (hx : x ∈ matrixRelativeCommutant dims U (L : Filter ι)) :
    matrixHilbertEmbedding dims hd L x ∈ matrixRelativeCommutantTraceSubspace dims U hd L :=
  Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩

variable [NeZero h]

theorem matrixQuotientLazyMarkov_fixed_iff_mem (x : MatrixTracialQuotient dims (L : Filter ι)) :
    matrixQuotientLazyMarkov dims U hd (L : Filter ι) x = x ↔
      x ∈ matrixRelativeCommutant dims U (L : Filter ι) := by
  rw [matrixQuotientLazyMarkov_fixed_iff, mem_matrixRelativeCommutant_iff]

theorem matrixRelativeCommutantTraceSubspace_le_fixed :
    matrixRelativeCommutantTraceSubspace dims U hd L ≤
      ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L).eqLocus
        (1 : MatrixTraceHilbert dims hd L →L[ℂ] MatrixTraceHilbert dims hd L) := by
  apply Submodule.topologicalClosure_minimal
  · rintro ξ ⟨x, hx, rfl⟩
    change (matrixUniformLazyMarkov dims U hd).hilbertMap hd L (matrixHilbertEmbedding dims hd L x) = _
    rw [UniformMatrixMap.hilbertMap_embedding]
    change matrixHilbertEmbedding dims hd L (matrixQuotientLazyMarkov dims U hd (L : Filter ι) x) = _
    rw [(matrixQuotientLazyMarkov_fixed_iff_mem dims U hd L x).mpr hx]
    rfl
  · exact ContinuousLinearMap.isClosed_eqLocus _ _

section NatIndex

variable (dims : Nat → Nat) (U : (n : Nat) → Fin h → UnitaryMatrix (dims n))
  (hd : ∀ n, 0 < dims n) (L : Ultrafilter Nat) (hL : (L : Filter Nat) ≤ atTop)

include hL in
theorem matrixMarkovProjection_mem_relativeCommutantTraceSubspace (ξ : MatrixTraceHilbert dims hd L) :
    matrixMarkovProjection dims U hd L ξ ∈ matrixRelativeCommutantTraceSubspace dims U hd L := by
  refine (matrixHilbertEmbedding_dense dims hd L).induction_on ξ ?_ ?_
  · exact (matrixRelativeCommutantTraceSubspace_isClosed dims U hd L).preimage
      (matrixMarkovProjection dims U hd L).continuous
  · intro x
    obtain ⟨y, he, hy, _⟩ := exists_matrixMarkovProjection_element dims U hd L hL x
    rw [← he]
    exact matrixHilbertEmbedding_mem_relativeCommutantTraceSubspace dims U hd L y
      ((matrixQuotientLazyMarkov_fixed_iff_mem dims U hd L y).mp hy)

include hL in
theorem matrixRelativeCommutantTraceSubspace_eq_fixed :
    matrixRelativeCommutantTraceSubspace dims U hd L =
      ((matrixUniformLazyMarkov dims U hd).hilbertMap hd L).eqLocus
        (1 : MatrixTraceHilbert dims hd L →L[ℂ] MatrixTraceHilbert dims hd L) := by
  apply le_antisymm (matrixRelativeCommutantTraceSubspace_le_fixed dims U hd L)
  intro ξ hξ
  have he := (matrixMarkovProjection_eq_self_iff dims U hd L ξ).mpr hξ
  rw [← he]
  exact matrixMarkovProjection_mem_relativeCommutantTraceSubspace dims U hd L hL ξ

include hL in
theorem matrixMarkovProjection_eq_relativeCommutantProjection :
    matrixMarkovProjection dims U hd L = (matrixRelativeCommutantTraceSubspace dims U hd L).starProjection := by
  simp only [matrixRelativeCommutantTraceSubspace_eq_fixed dims U hd L hL]
  rfl

end NatIndex
end ThomGame.Analysis
