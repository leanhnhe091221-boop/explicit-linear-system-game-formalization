module

public import ThomGame.Pictures.ConnectivitySmoothing
public import ThomGame.Pictures.GraphComponentCounts

/-!
# Exact component counts for one smoothing step

The map on dart components is injective. For an ordinary junction it is
surjective; for an isolated loop its image omits exactly the component
of the two removed ports. The resulting counts are then transferred to
actual vertex components when every hub has a port.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph

open Equiv RibbonConnectivity
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S} (G : PortGraph P u v)

abbrev DartComponent := Component G.pairing.perm G.circuitStep

def dartComponent (a : G.Dart) : G.DartComponent := component G.pairing.perm G.circuitStep a

theorem dartComponent_eq_iff (a b : G.Dart) :
    G.dartComponent a = G.dartComponent b ↔ Connected G.pairing.perm G.circuitStep a b :=
  component_eq_iff _ _ a b

noncomputable def smoothComponentMap (j : G.Joint) : (G.smooth j).DartComponent → G.DartComponent :=
  Quotient.lift (fun a => G.dartComponent (G.smoothPortEmbedding j a)) (fun _ _ h =>
    (G.dartComponent_eq_iff _ _).mpr (G.smooth_connected_expands j h))

theorem smoothComponentMap_component (j : G.Joint) (a : (G.smooth j).Dart) :
    G.smoothComponentMap j ((G.smooth j).dartComponent a) =
      G.dartComponent (G.smoothPortEmbedding j a) := rfl

theorem smoothComponentMap_injective (j : G.Joint) : Function.Injective (G.smoothComponentMap j) := by
  intro c d hcd
  refine Quotient.inductionOn₂ c d (fun a b he => ?_) hcd
  exact ((G.smooth j).dartComponent_eq_iff _ _).mpr
    ((G.smooth_connected_iff j a b).mpr ((G.dartComponent_eq_iff _ _).mp he))

theorem loop_connected_iff (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (x : G.Dart) :
    Connected G.pairing.perm G.circuitStep x (.joint j false) ↔
      x = .joint j false ∨ x = .joint j true := by
  have hp' : G.pairing.twin (.joint j true) = .joint j false := by rw [← hp, G.pairing.involutive]
  have ep : ∀ x : G.Dart,
      (G.pairing.perm x = .joint j false ∨ G.pairing.perm x = .joint j true) ↔
        x = .joint j false ∨ x = .joint j true := by
    intro x
    have ha : G.pairing.perm (.joint j true) = .joint j false := hp'
    have hb : G.pairing.perm (.joint j false) = .joint j true := hp
    calc
      _ ↔ x = .joint j true ∨ x = .joint j false := by
        simpa only [ha, hb] using or_congr
          (G.pairing.perm.injective.eq_iff (a := x) (b := .joint j true))
          (G.pairing.perm.injective.eq_iff (a := x) (b := .joint j false))
      _ ↔ _ := or_comm
  have ef : ∀ x : G.Dart,
      (G.circuitStep x = .joint j false ∨ G.circuitStep x = .joint j true) ↔
        x = .joint j false ∨ x = .joint j true := by
    intro x
    rw [← G.circuitStep_joint_left_of_loop j hp, ← G.circuitStep_joint_right_of_loop j hp,
      G.circuitStep.injective.eq_iff, G.circuitStep.injective.eq_iff,
      G.circuitStep_joint_left_of_loop j hp, G.circuitStep_joint_right_of_loop j hp]
  constructor
  · intro h
    have hi := h.lift (fun y => y = .joint j false ∨ y = .joint j true)
      ⟨Iff.refl, Iff.symm, Iff.trans⟩ (fun y => (ep y).symm) (fun y => (ef y).symm)
    exact hi.mpr (Or.inl rfl)
  · rintro (rfl | rfl)
    · exact Connected.refl _
    · exact (G.connected_of_same_vertex (a := .joint j false) (b := .joint j true) rfl).symm

theorem smoothComponentMap_avoids_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (c : (G.smooth j).DartComponent) :
    G.smoothComponentMap j c ≠ G.dartComponent (.joint j false) := by
  refine Quotient.inductionOn c fun a he => ?_
  have ha := (G.loop_connected_iff j hp _).mp ((G.dartComponent_eq_iff _ _).mp he)
  exact ha.elim (G.smoothPorts j a).property.1 (G.smoothPorts j a).property.2

theorem smoothComponentMap_range_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) (c : G.DartComponent) :
    (∃ d, G.smoothComponentMap j d = c) ↔ c ≠ G.dartComponent (.joint j false) := by
  constructor
  · rintro ⟨d, rfl⟩
    exact G.smoothComponentMap_avoids_loop j hp d
  · refine Quotient.inductionOn c (fun x hx => ?_)
    have hxa : x ≠ .joint j false := fun he => hx (congrArg G.dartComponent he)
    have hxb : x ≠ .joint j true := by
      intro he
      apply hx
      exact (G.dartComponent_eq_iff _ _).mpr ((G.loop_connected_iff j hp x).mpr (Or.inr he))
    refine ⟨(G.smooth j).dartComponent ((G.smoothPorts j).symm ⟨x, hxa, hxb⟩), ?_⟩
    rw [G.smoothComponentMap_component]
    exact congrArg G.dartComponent (congrArg Subtype.val ((G.smoothPorts j).apply_symm_apply _))

noncomputable def smoothComponentComplementEquiv (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    (G.smooth j).DartComponent ≃ {c : G.DartComponent // c ≠ G.dartComponent (.joint j false)} :=
  Equiv.ofBijective (fun c => ⟨G.smoothComponentMap j c, G.smoothComponentMap_avoids_loop j hp c⟩)
    ⟨fun _ _ he => G.smoothComponentMap_injective j (congrArg Subtype.val he), fun c => by
      obtain ⟨d, hd⟩ := (G.smoothComponentMap_range_of_loop j hp c.val).mpr c.property
      exact ⟨d, Subtype.ext hd⟩⟩

theorem smoothComponentMap_surjective_of_not_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) : Function.Surjective (G.smoothComponentMap j) := by
  intro c
  refine Quotient.inductionOn c fun x => ?_
  by_cases hxa : x = .joint j false
  · subst x
    let a : (G.smooth j).Dart := (G.smoothPorts j).symm
      ⟨G.pairing.twin (.joint j false), G.pairing.partner_left_away hp⟩
    refine ⟨(G.smooth j).dartComponent a, ?_⟩
    rw [G.smoothComponentMap_component]
    apply (G.dartComponent_eq_iff _ _).mpr
    change Connected _ _ (G.smoothPorts j ((G.smoothPorts j).symm _)).val _
    rw [Equiv.apply_symm_apply]
    exact (Connected.edge _).symm
  by_cases hxb : x = .joint j true
  · subst x
    let a : (G.smooth j).Dart := (G.smoothPorts j).symm
      ⟨G.pairing.twin (.joint j true), G.pairing.partner_right_away hp⟩
    refine ⟨(G.smooth j).dartComponent a, ?_⟩
    rw [G.smoothComponentMap_component]
    apply (G.dartComponent_eq_iff _ _).mpr
    change Connected _ _ (G.smoothPorts j ((G.smoothPorts j).symm _)).val _
    rw [Equiv.apply_symm_apply]
    exact (Connected.edge _).symm
  · refine ⟨(G.smooth j).dartComponent ((G.smoothPorts j).symm ⟨x, hxa, hxb⟩), ?_⟩
    rw [G.smoothComponentMap_component]
    exact congrArg G.dartComponent (congrArg Subtype.val ((G.smoothPorts j).apply_symm_apply _))

noncomputable def smoothComponentEquiv (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) ≠ .joint j true) : (G.smooth j).DartComponent ≃ G.DartComponent :=
  Equiv.ofBijective (G.smoothComponentMap j)
    ⟨G.smoothComponentMap_injective j, G.smoothComponentMap_surjective_of_not_loop j hp⟩

theorem smooth_dartComponent_card_of_loop (j : G.Joint)
    (hp : G.pairing.twin (.joint j false) = .joint j true) :
    Nat.card (G.smooth j).DartComponent + 1 = Nat.card G.DartComponent := by
  let : Fintype G.DartComponent := Fintype.ofFinite _
  have hc := FiniteReturn.card_remove_one (G.dartComponent (.joint j false))
  simp only [← Nat.card_eq_fintype_card] at hc
  rw [← Nat.card_congr (G.smoothComponentComplementEquiv j hp)] at hc
  exact hc

theorem smooth_dartComponent_card (j : G.Joint) :
    Nat.card (G.smooth j).DartComponent + (G.smoothCircles j).length = Nat.card G.DartComponent := by
  by_cases hp : G.pairing.twin (.joint j false) = .joint j true
  · rw [G.smoothCircles_of_loop j hp]
    exact G.smooth_dartComponent_card_of_loop j hp
  · rw [G.smoothCircles_of_not_loop j hp]
    simpa only [List.length_nil, Nat.add_zero] using Nat.card_congr (G.smoothComponentEquiv j hp)

theorem smooth_graphComponent_card (j : G.Joint)
    (hn : ∀ h : G.Hub, 0 < (P.word (G.hubLabel h)).length) :
    Nat.card (G.smooth j).GraphComponent + (G.smoothCircles j).length = Nat.card G.GraphComponent := by
  have hc := G.smooth_dartComponent_card j
  rw [Nat.card_congr (G.dartComponentEquiv hn),
    Nat.card_congr ((G.smooth j).dartComponentEquiv hn)] at hc
  exact hc

end ThomGame.Pictures.PortGraph
