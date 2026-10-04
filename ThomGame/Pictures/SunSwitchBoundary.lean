module

public import ThomGame.Pictures.SunSwitchEuler
public import ThomGame.Pictures.ReturnTransport
public import ThomGame.Pictures.BoundaryOrder

/-!
# The sun switch preserves the complete ordered boundary return

Boundary ports survive deletion of the spoke ports and are fixed by the
attachment exchange. Nested first return therefore transports the proved
retained face conjugacy to equality of the original boundary successor.
In particular the specified boundary noncrossing condition is preserved.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv MarkedReturn
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

theorem boundary_kept {x : G.Dart} (hx : G.IsBoundary x) : s.Kept x := by
  cases x with
  | top i => exact ⟨(by intro h; cases h), (by intro h; cases h)⟩
  | bottom i => exact ⟨(by intro h; cases h), (by intro h; cases h)⟩
  | hub h i => exact hx.elim
  | joint j side => exact hx.elim

theorem portSwap_boundary {x : G.Dart} (hx : G.IsBoundary x) : s.portSwap x = x := by
  cases x with
  | top i => exact swap_apply_of_ne_of_ne (by intro h; cases h) (by intro h; cases h)
  | bottom i => exact swap_apply_of_ne_of_ne (by intro h; cases h) (by intro h; cases h)
  | hub h i => exact hx.elim
  | joint j side => exact hx.elim

theorem portSwap_boundary_iff (x : G.Dart) : G.IsBoundary (s.portSwap x) ↔ G.IsBoundary x := by
  constructor
  · intro h
    have he := s.portSwap_boundary h
    rw [s.portSwap_involutive] at he
    exact he.symm ▸ h
  · intro h
    rwa [s.portSwap_boundary h]

theorem nested_boundary_fixed (x : {a : Subtype s.Kept // G.IsBoundary a.val}) :
    (s.keptSwap.subtypeEquiv (fun a => (s.portSwap_boundary_iff a.val).symm)) x = x := by
  apply Subtype.ext
  apply Subtype.ext
  exact s.portSwap_boundary x.property

theorem switch_boundary_return (hf : G.hubFlip s.left = G.hubFlip s.right)
    (x : Subtype G.IsBoundary) :
    perm s.switch.circuitStep G.IsBoundary x = perm G.circuitStep G.IsBoundary x := by
  let z : {a : Subtype s.Kept // G.IsBoundary a.val} := ⟨⟨x.val, s.boundary_kept x.property⟩, x.property⟩
  have h := perm_subtypeEquiv (perm G.circuitStep s.Kept) (perm s.switch.circuitStep s.Kept)
    s.keptSwap (s.return_congr hf) (fun a => G.IsBoundary a.val) (fun a => G.IsBoundary a.val)
    (fun a => (s.portSwap_boundary_iff a.val).symm) z
  rw [s.nested_boundary_fixed, s.nested_boundary_fixed] at h
  have h' := congrArg (nestedSubset s.Kept G.IsBoundary (fun _ => s.boundary_kept)) h
  exact (perm_nested_subset s.switch.circuitStep s.Kept G.IsBoundary
    (fun _ => s.boundary_kept) z).trans
      (h'.trans (perm_nested_subset G.circuitStep s.Kept G.IsBoundary
        (fun _ => s.boundary_kept) z).symm)

theorem switch_boundaryNext (hf : G.hubFlip s.left = G.hubFlip s.right) :
    s.switch.boundaryNext = G.boundaryNext := by
  ext i
  have he (x : G.Dart) : s.switch.IsBoundary x ↔ G.IsBoundary x := by cases x <;> rfl
  have hp := perm_eq_of_pred_iff s.switch.circuitStep s.switch.IsBoundary G.IsBoundary
    he (s.switch.boundaryPorts i)
  have ha : (⟨(s.switch.boundaryPorts i).val, (he _).mp (s.switch.boundaryPorts i).property⟩ :
      Subtype G.IsBoundary) = G.boundaryPorts i := by cases i <;> rfl
  rw [ha] at hp
  have h := (congrArg Subtype.val (s.switch.boundaryPorts_next i)).symm.trans
    (hp.trans ((congrArg Subtype.val (s.switch_boundary_return hf (G.boundaryPorts i))).trans
      (congrArg Subtype.val (G.boundaryPorts_next i))))
  have hd (j : BoundaryIndex u v) : (s.switch.boundaryPorts j).val = (G.boundaryPorts j).val := by
    cases j <;> rfl
  rw [hd] at h
  exact G.boundaryDart.injective h

theorem switch_boundaryNoncrossing (hf : G.hubFlip s.left = G.hubFlip s.right)
    (h : G.BoundaryNoncrossing) : s.switch.BoundaryNoncrossing := by
  change CircularPartition.OrderedNoncrossing (boundaryCyclic u v) (boundaryBetween u v) _
  rw [s.switch_boundaryNext hf]
  exact h

theorem switch_boundary_circuit_iff (hf : G.hubFlip s.left = G.hubFlip s.right)
    (i j : BoundaryIndex u v) :
    s.switch.circuitStep.SameCycle (G.boundaryDart i) (G.boundaryDart j) ↔
      G.circuitStep.SameCycle (G.boundaryDart i) (G.boundaryDart j) := by
  have hn := (s.switch.boundaryNext_sameCycle_iff i j).trans (s.switch.circuit_eq_iff _ _)
  have ho := (G.boundaryNext_sameCycle_iff i j).trans (G.circuit_eq_iff _ _)
  have hbd (k : BoundaryIndex u v) : s.switch.boundaryDart k = G.boundaryDart k := by cases k <;> rfl
  rw [s.switch_boundaryNext hf, hbd, hbd] at hn
  exact hn.symm.trans ho

theorem switch_boundarySeesComponents (hf : G.hubFlip s.left = G.hubFlip s.right)
    (h : G.BoundarySeesComponents) : s.switch.BoundarySeesComponents := by
  intro a c
  obtain ⟨i, rfl⟩ := s.switch.boundaryPorts.surjective a
  obtain ⟨j, rfl⟩ := s.switch.boundaryPorts.surjective c
  change RibbonConnectivity.Connected s.switch.pairing.perm s.switch.circuitStep
    (s.switch.boundaryDart i) (s.switch.boundaryDart j) ↔
      s.switch.circuitStep.SameCycle (s.switch.boundaryDart i) (s.switch.boundaryDart j)
  have hbd (k : BoundaryIndex u v) : s.switch.boundaryDart k = G.boundaryDart k := by cases k <;> rfl
  rw [hbd, hbd]
  exact (s.switch_circuit_connected _ _).trans
    ((h (G.boundaryPorts i) (G.boundaryPorts j)).trans (s.switch_boundary_circuit_iff hf i j).symm)

end ThomGame.Pictures.PortGraph.SunSpoke
