module

public import ThomGame.Pictures.EdgeDeletionEuler
public import ThomGame.Pictures.RestrictedConnectivity

/-!
# Paths after deleting a pairing-invariant set of edges

Deletion only refines connectivity. A component is unchanged when every
edge port in that component is either retained or was already fixed.
This is a path statement, without finiteness or Euler assumptions.
-/

@[expose] public section
namespace ThomGame.Pictures.RotationEuler

open Equiv RibbonConnectivity
open scoped Classical

variable {D : Type*} (f t : Perm D) (M : D → Prop) (hM : ∀ x, M (t x) ↔ M x)

theorem retainEdges_preserves (N : D → Prop) (hN : ∀ x, N (t x) ↔ N x) (x : D) :
    N (retainEdges t M hM x) ↔ N x := by
  rw [retainEdges_apply]
  split_ifs
  · exact hN x
  · rfl

theorem connected_retainEdges {x y : D} (h : Connected f (retainEdges t M hM) x y) :
    Connected f t x y := by
  apply h.lift id ⟨Connected.refl, Connected.symm, Connected.trans⟩ Connected.edge
  intro z
  change Connected f t z (retainEdges t M hM z)
  rw [retainEdges_apply]
  split_ifs
  · exact Connected.circuit z
  · exact Connected.refl z

theorem connected_retainEdges_iff_of_component (x y : D)
    (hkeep : ∀ z, Connected f t x z → M z ∨ t z = z) :
    Connected f (retainEdges t M hM) x y ↔ Connected f t x y := by
  constructor
  · exact connected_retainEdges f t M hM
  · intro h
    let N := fun z => Connected f t x z
    have hf (z : D) : N (f z) ↔ N z :=
      ⟨fun hz => hz.trans (Connected.edge z).symm, fun hz => hz.trans (Connected.edge z)⟩
    have ht (z : D) : N (t z) ↔ N z :=
      ⟨fun hz => hz.trans (Connected.circuit z).symm, fun hz => hz.trans (Connected.circuit z)⟩
    apply h.lift_restricted N hf ht (Connected.refl x) h Subtype.val
      ⟨Connected.refl, Connected.symm, Connected.trans⟩
    · intro z
      exact Connected.edge z.val
    · intro z
      change Connected f (retainEdges t M hM) z.val (t z.val)
      rcases hkeep z.val z.property with hz | hz
      · have he := Connected.circuit (p := f) (f := retainEdges t M hM) z.val
        rw [retainEdges_apply, ite_eq_left hz] at he
        exact he
      · rw [hz]
        exact Connected.refl _

end ThomGame.Pictures.RotationEuler
