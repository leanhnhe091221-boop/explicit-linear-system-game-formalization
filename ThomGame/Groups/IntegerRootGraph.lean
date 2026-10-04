module

public import ThomGame.Groups.CompressorPresentation
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-! The actual six-vertex, four-regular graph used in the integer-root spectral criterion. -/

@[expose] public section
namespace ThomGame.IntegerRootGraph

open Compressor
open scoped BigOperators

def neighbor (r : Root) : Fin 4 → Root :=
  ![across r, right r, reverse (across r), reverse (right r)]

def reverseIndex : Fin 4 → Fin 4 := ![0, 2, 1, 3]

theorem reverse_reverse : ∀ r : Root, reverse (reverse r) = r := by decide +kernel

theorem reverse_ne : ∀ r : Root, reverse r ≠ r := by decide +kernel

theorem neighbor_reverse : ∀ (r : Root) (i : Fin 4), neighbor (neighbor r i) (reverseIndex i) = r := by
  decide +kernel

theorem reverseIndex_reverseIndex : ∀ i : Fin 4, reverseIndex (reverseIndex i) = i := by decide +kernel

theorem neighbor_injective : ∀ r : Root, Function.Injective (neighbor r) := by decide +kernel

def graph : SimpleGraph Root where
  Adj r s := r ≠ s ∧ reverse r ≠ s
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := fun r s =>
  inferInstanceAs (Decidable (r ≠ s ∧ reverse r ≠ s))

theorem adjacent_iff_neighbor : ∀ r s : Root, graph.Adj r s ↔ ∃ i : Fin 4, neighbor r i = s := by
  decide +kernel

theorem adjacent_iff_all_axes : ∀ r s : Root,
    graph.Adj r s ↔ ({source r, target r, source s, target s} : Finset Axis) = Finset.univ := by
  decide +kernel

def vertexEnumeration (r : Root) : Fin 6 → Root :=
  ![r, reverse r, across r, right r, reverse (across r), reverse (right r)]

theorem vertexEnumeration_bijective : ∀ r : Root, Function.Bijective (vertexEnumeration r) := by
  decide +kernel

def neighborEquiv (i : Fin 4) : Root ≃ Root where
  toFun r := neighbor r i
  invFun r := neighbor r (reverseIndex i)
  left_inv r := neighbor_reverse r i
  right_inv r := by simpa only [reverseIndex_reverseIndex] using neighbor_reverse r (reverseIndex i)

def oppositeEquiv : Root ≃ Root where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse
  right_inv := reverse_reverse

def edgeReverse : (Root × Fin 4) ≃ (Root × Fin 4) where
  toFun e := (neighbor e.1 e.2, reverseIndex e.2)
  invFun e := (neighbor e.1 e.2, reverseIndex e.2)
  left_inv e := by simp only [neighbor_reverse, reverseIndex_reverseIndex]
  right_inv e := by simp only [neighbor_reverse, reverseIndex_reverseIndex]

theorem vertex_card : Fintype.card Root = 6 := by decide +kernel

theorem directed_edge_card : Fintype.card (Root × Fin 4) = 24 := by decide +kernel

theorem sum_neighbors_complement {A : Type*} [AddCommGroup A] (f : Root → A) (r : Root) :
    f r + f (reverse r) + ∑ i : Fin 4, f (neighbor r i) = ∑ s : Root, f s := by
  have h := (vertexEnumeration_bijective r).sum_comp f
  simpa only [vertexEnumeration, neighbor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, add_assoc] using h

theorem sum_neighbors_reindex {A : Type*} [AddCommMonoid A] (f : Root → A) (i : Fin 4) :
    ∑ r : Root, f (neighbor r i) = ∑ r : Root, f r := (neighborEquiv i).sum_comp f

theorem sum_opposites_reindex {A : Type*} [AddCommMonoid A] (f : Root → A) :
    ∑ r : Root, f (reverse r) = ∑ r : Root, f r := oppositeEquiv.sum_comp f

end ThomGame.IntegerRootGraph
