module

public import ThomGame.Pictures.SunBandExclusion

/-!
# A circuit restricted to one rim label is a three-label circuit

At a spoke end, the other circuit port must be one of the two rim
ports. If all rim occurrences have one label, the spoke is therefore
one of that rim's two incident spokes. Lemma 10.6 then excludes the
circuit in a minimal sun.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v}

namespace SimpleCircuit

variable [IsEmpty G.Joint] (C : G.SimpleCircuit)

theorem sunBand_of_single_rim_label (i : Fin n)
    (hs : ∀ (k : Fin C.length) (j : Fin n), Port.label G.jointLabel (C.dart k) = Sum.inr j → j = i) :
    ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)) := by
  have hp (k : Fin C.length) (side : Bool) (j : Fin n)
      (he : Port.label G.jointLabel (C.port (k, side)) = Sum.inr j) : j = i := by
    cases side
    · exact hs k j he
    · change Port.label G.jointLabel (G.pairing.twin (C.dart ((finRotate C.length).symm k))) = Sum.inr j at he
      rw [G.pairing.label_twin] at he
      exact hs _ j he
  intro k
  obtain ⟨h, p, q, ho, hi, hpq⟩ := C.exists_hub_ports k
  change SunBandLabel i (Port.label G.jointLabel (C.outgoing k))
  rw [ho]
  fin_cases p
  · fin_cases q
    · exact (hpq rfl).elim
    · have he := hp k true (G.hubLabel h) (congrArg (Port.label G.jointLabel) hi)
      exact Or.inr (Or.inl (congrArg Sum.inl he))
    · have he := hp k true (finRotate n (G.hubLabel h)) (congrArg (Port.label G.jointLabel) hi)
      have hh : G.hubLabel h = (finRotate n).symm i :=
        (Equiv.symm_apply_apply (finRotate n) (G.hubLabel h)).symm.trans (congrArg (finRotate n).symm he)
      exact Or.inr (Or.inr (congrArg Sum.inl hh))
  · exact Or.inl (congrArg Sum.inr (hp k false (G.hubLabel h) (congrArg (Port.label G.jointLabel) ho)))
  · exact Or.inl (congrArg Sum.inr
      (hp k false (finRotate n (G.hubLabel h)) (congrArg (Port.label G.jointLabel) ho)))

end SimpleCircuit

variable {w : List (Fin n ⊕ Fin n)} {B : PortGraph (sunPresentation n b) [] w}
  [IsEmpty B.Joint]

theorem NoSunBandCircuit.no_single_rim_label (h : B.NoSunBandCircuit) (C : B.SimpleCircuit) (i : Fin n) :
    ¬ ∀ (k : Fin C.length) (j : Fin n), Port.label B.jointLabel (C.dart k) = Sum.inr j → j = i :=
  fun hs => h C i (C.sunBand_of_single_rim_label i hs)

end ThomGame.Pictures.PortGraph
