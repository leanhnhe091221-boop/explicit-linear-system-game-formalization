module

public import ThomGame.Finite.Hypergraph
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Data.Fintype.Perm

/-!
# The slot permutation of an open embedding of trivalent systems

The three distinct columns determine an actual permutation of the port
positions at every included row. Every permutation of three positions
preserves a cyclic order after possibly reversing its orientation.
The orientation assertion is a finite theorem checked by the kernel.
-/

@[expose] public section
namespace ThomGame

def triangleTurn (flip : Bool) : Equiv.Perm (Fin 3) :=
  if flip then (finRotate 3).symm else finRotate 3

theorem exists_triangleFlip : ∀ p : Equiv.Perm (Fin 3), ∃ f : Bool,
    ∀ (b : Bool) (i : Fin 3), triangleTurn (b ^^ f) (p i) = p (triangleTurn b i) := by
  decide +kernel

noncomputable def triangleFlip (p : Equiv.Perm (Fin 3)) : Bool :=
  Classical.choose (exists_triangleFlip p)

theorem triangleFlip_turn (p : Equiv.Perm (Fin 3)) (b : Bool) (i : Fin 3) :
    triangleTurn (b ^^ triangleFlip p) (p i) = p (triangleTurn b i) :=
  Classical.choose_spec (exists_triangleFlip p) b i

namespace Hypergraph.OpenEmbedding

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  (ι : A.hypergraph.OpenEmbedding B.hypergraph)

theorem exists_column_slot (r : R) (i : Fin 3) :
    ∃ j : Fin 3, B.column (ι.vertex r) j = ι.edge (A.column r i) := by
  apply (B.mem_hypergraph_incidence _ _).mp
  rw [← ι.incidence]
  exact Multiset.mem_map.mpr ⟨A.column r i, (A.mem_hypergraph_incidence r _).mpr ⟨i, rfl⟩, rfl⟩

noncomputable def columnSlot (r : R) (i : Fin 3) : Fin 3 :=
  Classical.choose (ι.exists_column_slot r i)

theorem columnSlot_label (r : R) (i : Fin 3) :
    B.column (ι.vertex r) (ι.columnSlot r i) = ι.edge (A.column r i) :=
  Classical.choose_spec (ι.exists_column_slot r i)

theorem columnSlot_injective (r : R) : Function.Injective (ι.columnSlot r) := by
  intro i j he
  apply A.column_injective r
  apply ι.edge.injective
  exact (ι.columnSlot_label r i).symm.trans
    ((congrArg (B.column (ι.vertex r)) he).trans (ι.columnSlot_label r j))

noncomputable def slotEquiv (r : R) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (ι.columnSlot r)
    ⟨ι.columnSlot_injective r, Finite.surjective_of_injective (ι.columnSlot_injective r)⟩

theorem slotEquiv_label (r : R) (i : Fin 3) :
    B.column (ι.vertex r) (ι.slotEquiv r i) = ι.edge (A.column r i) := ι.columnSlot_label r i

theorem slotEquiv_turn (r : R) (b : Bool) (i : Fin 3) :
    triangleTurn (b ^^ triangleFlip (ι.slotEquiv r)) (ι.slotEquiv r i) =
      ι.slotEquiv r (triangleTurn b i) := triangleFlip_turn _ b i

end Hypergraph.OpenEmbedding
end ThomGame
