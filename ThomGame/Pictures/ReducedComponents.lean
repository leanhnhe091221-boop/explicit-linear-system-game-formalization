module

public import ThomGame.Pictures.SmoothingEuler

/-!
# Exactly the components retained by complete smoothing

The retained dart components are those containing an original boundary
or relation port. Components containing only junctions account for the
recorded circles, one per discarded component.
-/

@[expose] public section
namespace ThomGame.Pictures

open RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

namespace PortGraph

def ComponentHasTerminal (G : PortGraph P u v) (c : G.DartComponent) : Prop :=
  ∃ a : G.Dart, G.Terminal a ∧ G.dartComponent a = c

end PortGraph

namespace Smoothing

variable {G H : PortGraph P u v} {circles : List S}

noncomputable def componentMap (d : Smoothing G H circles) : H.DartComponent → G.DartComponent :=
  Quotient.lift (fun a => G.dartComponent (d.portEmbedding a)) (fun a b hab =>
    (G.dartComponent_eq_iff _ _).mpr ((d.connected_iff a b).mp hab))

theorem componentMap_component (d : Smoothing G H circles) (a : H.Dart) :
    d.componentMap (H.dartComponent a) = G.dartComponent (d.portEmbedding a) := rfl

theorem componentMap_injective (d : Smoothing G H circles) : Function.Injective d.componentMap := by
  intro c e hce
  refine Quotient.inductionOn₂ c e (fun a b hab => ?_) hce
  exact (H.dartComponent_eq_iff a b).mpr ((d.connected_iff a b).mpr ((G.dartComponent_eq_iff _ _).mp hab))

theorem componentMap_range_iff (d : Smoothing G H circles) [IsEmpty H.Joint] (c : G.DartComponent) :
    (∃ e, d.componentMap e = c) ↔ G.ComponentHasTerminal c := by
  constructor
  · rintro ⟨e, rfl⟩
    refine Quotient.inductionOn e fun a => ?_
    exact ⟨d.portEmbedding a, (d.terminal_iff a).mpr (H.terminal_of_no_junctions a), rfl⟩
  · rintro ⟨a, ha, hc⟩
    obtain ⟨b, _, hb⟩ := d.terminal_surjective a ha
    refine ⟨H.dartComponent b, ?_⟩
    rw [d.componentMap_component, hb, hc]

noncomputable def retainedComponentEquiv (d : Smoothing G H circles) [IsEmpty H.Joint] :
    H.DartComponent ≃ {c : G.DartComponent // G.ComponentHasTerminal c} :=
  Equiv.ofBijective (fun c => ⟨d.componentMap c, (d.componentMap_range_iff _).mp ⟨c, rfl⟩⟩)
    ⟨fun _ _ he => d.componentMap_injective (congrArg Subtype.val he), fun c => by
      obtain ⟨e, he⟩ := (d.componentMap_range_iff c.val).mpr c.property
      exact ⟨e, Subtype.ext he⟩⟩

theorem discarded_component_card (d : Smoothing G H circles) [IsEmpty H.Joint] :
    Nat.card {c : G.DartComponent // ¬ G.ComponentHasTerminal c} = circles.length := by
  let : Fintype G.DartComponent := Fintype.ofFinite _
  have hr := Nat.card_congr d.retainedComponentEquiv
  have hc := d.dartComponent_card
  have hh := Fintype.card_subtype_compl G.ComponentHasTerminal
  simp only [← Nat.card_eq_fintype_card] at hh
  omega

end Smoothing
end ThomGame.Pictures
