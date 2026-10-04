module

public import ThomGame.Pictures.SunSideSpokes

/-!
# Applying the actual sun switch twice restores the original graph

The second switch uses the same two hub identities. It reverses their
orientations again and conjugates the edge pairing by the same port
exchange. The resulting equality includes all original graph data.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SunSpoke

open Equiv
open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} (s : G.SunSpoke)

private theorem pairing_ext_twin {D S : Type*} {label : D → S}
    (p q : Pairing label) (h : p.twin = q.twin) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem switch_twice_flip (h : G.Hub) : s.switchedSpoke.switch.hubFlip h = G.hubFlip h := by
  change (if h = s.left ∨ h = s.right then
    !(if h = s.left ∨ h = s.right then !G.hubFlip h else G.hubFlip h)
    else if h = s.left ∨ h = s.right then !G.hubFlip h else G.hubFlip h) = G.hubFlip h
  by_cases hh : h = s.left ∨ h = s.right <;> simp only [hh, ite_true, ite_false, Bool.not_not]

theorem switch_twice_twin (x : G.Dart) : s.switchedSpoke.switch.pairing.twin x = G.pairing.twin x := by
  change s.portSwap (s.switch.pairing.twin (s.portSwap x)) = G.pairing.twin x
  rw [s.switch_twin_portSwap, s.portSwap_involutive]

theorem switch_twice_pairing : s.switchedSpoke.switch.pairing = G.pairing := by
  exact pairing_ext_twin _ _ (funext s.switch_twice_twin)

theorem switch_twice : s.switchedSpoke.switch = G := by
  change ({G with hubFlip := s.switchedSpoke.switch.hubFlip, pairing := s.switchedSpoke.switch.pairing} :
    PortGraph (sunPresentation n b) u v) = G
  rw [funext s.switch_twice_flip, s.switch_twice_pairing]

theorem switch_twice_onSide (hn : 3 ≤ n)
    (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
    (a : G.SunRimDart hn) (side : Bool) (x : G.Dart) :
    (s.switchedSpoke.switch.sunRimSimpleCircuit hn hu hv a).OnSide side x ↔
      (G.sunRimSimpleCircuit hn hu hv a).OnSide side x := by
  change (({G with hubFlip := s.switchedSpoke.switch.hubFlip, pairing := s.switchedSpoke.switch.pairing} :
    PortGraph (sunPresentation n b) u v).sunRimSimpleCircuit hn hu hv a).OnSide side x ↔ _
  rw [funext s.switch_twice_flip, s.switch_twice_pairing]

theorem switch_twice_sideSpokeCount (hn : 3 ≤ n)
    (hu : ∀ z ∈ u, ∃ j, z = Sum.inl j) (hv : ∀ z ∈ v, ∃ j, z = Sum.inl j)
    (a : G.SunRimDart hn) (side : Bool) :
    s.switchedSpoke.switch.sunSideSpokeCount hn hu hv a side = G.sunSideSpokeCount hn hu hv a side := by
  change ({G with hubFlip := s.switchedSpoke.switch.hubFlip, pairing := s.switchedSpoke.switch.pairing} :
    PortGraph (sunPresentation n b) u v).sunSideSpokeCount
      hn hu hv a side = G.sunSideSpokeCount hn hu hv a side
  rw [funext s.switch_twice_flip, s.switch_twice_pairing]

end ThomGame.Pictures.PortGraph.SunSpoke
