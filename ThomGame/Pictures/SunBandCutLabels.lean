module

public import ThomGame.Pictures.SunBandErasureGraph

/-!
# Retaining and relabelling spokes while deleting the fixed rim edges

Retain every off-circuit dart and both ends of every circuit spoke.
The spoke matching allows its label to be changed to the common unused
rim label at its ends. Edge reversal preserves this actual retained set
and its new labels.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open scoped Classical

variable {n : Nat} {b : Fin n → ZMod 2} {u v : List (Fin n ⊕ Fin n)}
  {G : PortGraph (sunPresentation n b) u v} [IsEmpty G.Joint]
  (C : G.SimpleCircuit) (hn : 3 ≤ n) (i : Fin n)
  (hband : ∀ k : Fin C.length, SunBandLabel i (Port.label G.jointLabel (C.dart k)))

noncomputable def sunBandSpokePort (k : Fin C.length) : G.Dart := .hub (C.hubAt k) (0 : Fin 3)

theorem sunBandSpokePort_injective : Function.Injective C.sunBandSpokePort := by
  intro k l he
  exact C.hubAt_injective (G.sun_hub_eq_iff.mp he).1

def SunBandCutKeep (x : G.Dart) : Prop := ¬ C.Marked x ∨ x ∈ Set.range C.sunBandSpokePort

include hn hband in
theorem sunBandSpokePort_twin (k : Fin C.length) :
    G.pairing.twin (C.sunBandSpokePort k) = C.sunBandSpokePort (C.sunBandPartner hn i hband k) :=
  C.sunBandPartner_paired hn i hband k

include hn hband in
theorem sunBandCutKeep_twin (x : G.Dart) : C.SunBandCutKeep (G.pairing.twin x) ↔ C.SunBandCutKeep x := by
  have ht (y : G.Dart) (hy : C.SunBandCutKeep y) : C.SunBandCutKeep (G.pairing.twin y) := by
    rcases hy with hy | ⟨k, rfl⟩
    · exact Or.inl (C.sunBandErasure_kept_twin y hy)
    · exact Or.inr ⟨C.sunBandPartner hn i hband k, (C.sunBandSpokePort_twin hn i hband k).symm⟩
  exact ⟨fun hx => G.pairing.involutive x ▸ ht _ hx, ht x⟩

noncomputable def sunBandCutLabel (x : G.Dart) : Fin n ⊕ Fin n :=
  if hx : x ∈ Set.range C.sunBandSpokePort then
    Port.label G.jointLabel (C.sunBandExternalPort i (Classical.choose hx))
  else Port.label G.jointLabel x

theorem sunBandCutLabel_spoke (k : Fin C.length) :
    C.sunBandCutLabel i (C.sunBandSpokePort k) = Port.label G.jointLabel (C.sunBandExternalPort i k) := by
  have hk : C.sunBandSpokePort k ∈ Set.range C.sunBandSpokePort := ⟨k, rfl⟩
  unfold sunBandCutLabel
  rw [dite_eq_left hk]
  exact congrArg (fun l => Port.label G.jointLabel (C.sunBandExternalPort i l))
    (C.sunBandSpokePort_injective (Classical.choose_spec hk))

include hn hband in
theorem sunBandCutLabel_unmarked (x : G.Dart) (hx : ¬ C.Marked x) :
    C.sunBandCutLabel i x = Port.label G.jointLabel x := by
  apply dite_eq_right
  rintro ⟨k, rfl⟩
  exact hx (C.sunBand_spoke_marked hn i hband k)

include hn hband in
theorem sunBandCutLabel_twin (x : G.Dart) (hx : C.SunBandCutKeep x) :
    C.sunBandCutLabel i (G.pairing.twin x) = C.sunBandCutLabel i x := by
  rcases hx with hx | ⟨k, rfl⟩
  · rw [C.sunBandCutLabel_unmarked hn i hband x hx,
      C.sunBandCutLabel_unmarked hn i hband _ (C.sunBandErasure_kept_twin x hx), G.pairing.label_twin]
  · rw [C.sunBandSpokePort_twin hn i hband k, C.sunBandCutLabel_spoke, C.sunBandCutLabel_spoke]
    exact C.sunBandExternalPort_partner_label hn i hband k

noncomputable def sunBandCutPairing : Pairing (fun x : Subtype C.SunBandCutKeep => C.sunBandCutLabel i x.val) where
  twin x := ⟨G.pairing.twin x.val, (C.sunBandCutKeep_twin hn i hband x.val).mpr x.property⟩
  involutive x := Subtype.ext (G.pairing.involutive x.val)
  ne_self x hx := G.pairing.ne_self x.val (congrArg Subtype.val hx)
  label_twin x := C.sunBandCutLabel_twin hn i hband x.val x.property

end ThomGame.Pictures.PortGraph.SimpleCircuit
