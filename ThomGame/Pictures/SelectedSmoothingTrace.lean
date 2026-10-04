module

public import ThomGame.Pictures.SelectedSmoothingStep

/-!
# Finite traces removing precisely the selected junctions

The certificate is an ordinary Smoothing trace. A recursive predicate
requires each removed junction to be selected, and a terminal condition
requires every survivor to be unselected. Such traces preserve all old
terminal ports and their exact first return. If every selected wire
reaches a terminal, a trace exists and records no lost circles.
-/

@[expose] public section
namespace ThomGame.Pictures.Smoothing

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} {circles : List S}

noncomputable def jointEmbedding : {G H : PortGraph P u v} → {circles : List S} →
    Smoothing G H circles → H.Joint ↪ G.Joint
  | _, _, _, .refl _ => Function.Embedding.refl _
  | _, _, _, .step _ tail => tail.jointEmbedding.trans (Function.Embedding.subtype _)

theorem portEmbedding_joint (d : Smoothing G H circles) (j : H.Joint) (b : Bool) :
    d.portEmbedding (.joint j b) = .joint (d.jointEmbedding j) b := by
  induction d with
  | refl _ => rfl
  | @step G H circles k tail ih =>
    change G.smoothPortEmbedding k (tail.portEmbedding (.joint j b)) = _
    rw [ih]
    rfl

theorem jointLabel (d : Smoothing G H circles) (j : H.Joint) :
    H.jointLabel j = G.jointLabel (d.jointEmbedding j) := by
  induction d with
  | refl _ => rfl
  | step _ _ ih => exact ih j

theorem portRotation (d : Smoothing G H circles) (a : H.Dart) :
    d.portEmbedding (H.rotation a) = G.rotation (d.portEmbedding a) := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    change G.smoothPortEmbedding j (tail.portEmbedding (H.rotation a)) = _
    rw [ih]
    exact G.smooth_rotation j (tail.portEmbedding a)

def RemovesOnly : {G H : PortGraph P u v} → {circles : List S} →
    Smoothing G H circles → (G.Joint → Prop) → Prop
  | _, _, _, .refl _, _ => True
  | _, _, _, .step j tail, remove => remove j ∧ tail.RemovesOnly (fun k => remove k.val)

def ClearsSelected (d : Smoothing G H circles) (remove : G.Joint → Prop) : Prop :=
  ∀ j : H.Joint, ¬ remove (d.jointEmbedding j)

theorem selectedTerminal_iff (d : Smoothing G H circles) (remove : G.Joint → Prop) (a : H.Dart) :
    G.SelectedTerminal remove (d.portEmbedding a) ↔
      H.SelectedTerminal (fun j => remove (d.jointEmbedding j)) a := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    exact (G.smooth_selectedTerminal_iff remove j (tail.portEmbedding a)).trans
      (ih (fun k => remove k.val) a)

theorem selectedTerminal_surjective (d : Smoothing G H circles) (remove : G.Joint → Prop)
    (hd : d.RemovesOnly remove) (a : G.Dart) (ha : G.SelectedTerminal remove a) :
    ∃ b : H.Dart, H.SelectedTerminal (fun j => remove (d.jointEmbedding j)) b ∧ d.portEmbedding b = a := by
  induction d with
  | refl _ => exact ⟨a, ha, rfl⟩
  | @step G H circles j tail ih =>
    obtain ⟨b, hb, he⟩ := G.selectedTerminal_survives remove j hd.1 a ha
    obtain ⟨c, hc, hc'⟩ := ih (fun k => remove k.val) hd.2 b hb
    refine ⟨c, hc, ?_⟩
    change G.smoothPortEmbedding j (tail.portEmbedding c) = a
    rw [hc', he]

theorem selectedReturn_preserved (d : Smoothing G H circles) (remove : G.Joint → Prop)
    (hd : d.RemovesOnly remove)
    (a : {a : H.Dart // H.SelectedTerminal (fun j => remove (d.jointEmbedding j)) a}) :
    d.portEmbedding
      (MarkedReturn.perm (H.selectedStep (fun j => remove (d.jointEmbedding j)))
        (H.SelectedTerminal (fun j => remove (d.jointEmbedding j))) a).val =
      (MarkedReturn.perm (G.selectedStep remove) (G.SelectedTerminal remove)
        ⟨d.portEmbedding a.val, (d.selectedTerminal_iff remove a.val).mpr a.property⟩).val := by
  induction d with
  | refl _ => rfl
  | @step G H circles j tail ih =>
    change G.smoothPortEmbedding j (tail.portEmbedding
      (MarkedReturn.perm (H.selectedStep (fun k => remove (tail.jointEmbedding k).val))
        (H.SelectedTerminal (fun k => remove (tail.jointEmbedding k).val)) a).val) = _
    exact (congrArg (G.smoothPortEmbedding j) (ih (fun k => remove k.val) hd.2 a)).trans
      (G.smooth_selected_return remove j hd.1
        ⟨tail.portEmbedding a.val, (tail.selectedTerminal_iff (fun k => remove k.val) a.val).mpr a.property⟩)

theorem clears_selectedTerminal (d : Smoothing G H circles) (remove : G.Joint → Prop)
    (hc : d.ClearsSelected remove) (a : H.Dart) :
    H.SelectedTerminal (fun j => remove (d.jointEmbedding j)) a := by
  cases a with
  | top i => trivial
  | bottom i => trivial
  | hub h i => trivial
  | joint j b => exact hc j

noncomputable def selectedTerminalEquiv (d : Smoothing G H circles) (remove : G.Joint → Prop)
    (hd : d.RemovesOnly remove) (hc : d.ClearsSelected remove) :
    H.Dart ≃ {a : G.Dart // G.SelectedTerminal remove a} :=
  Equiv.ofBijective
    (fun a => ⟨d.portEmbedding a, (d.selectedTerminal_iff remove a).mpr (d.clears_selectedTerminal remove hc a)⟩)
    ⟨fun _ _ h => d.portEmbedding.injective (congrArg Subtype.val h), fun a => by
      obtain ⟨b, _, hb⟩ := d.selectedTerminal_surjective remove hd a.val a.property
      exact ⟨b, Subtype.ext hb⟩⟩

theorem selected_twin_return (d : Smoothing G H circles) (remove : G.Joint → Prop)
    (hd : d.RemovesOnly remove) (hc : d.ClearsSelected remove) (a : H.Dart) :
    d.portEmbedding (H.pairing.twin a) =
      (MarkedReturn.perm (G.selectedStep remove) (G.SelectedTerminal remove)
        (d.selectedTerminalEquiv remove hd hc a)).val := by
  have hstep : H.selectedStep (fun j => remove (d.jointEmbedding j)) a = H.pairing.twin a := by
    rw [H.selectedStep_apply]
    exact H.selectedTurn_eq_self _ _ (d.clears_selectedTerminal remove hc _)
  have hret := MarkedReturn.eq_perm_of_hit
    (H.selectedStep (fun j => remove (d.jointEmbedding j)))
    (H.SelectedTerminal (fun j => remove (d.jointEmbedding j)))
    ⟨a, d.clears_selectedTerminal remove hc a⟩
    (d.clears_selectedTerminal remove hc (H.pairing.twin a))
    (hstep ▸ MarkedReturn.Hit.direct (f := H.selectedStep (fun j => remove (d.jointEmbedding j)))
      (p := H.SelectedTerminal (fun j => remove (d.jointEmbedding j))) a)
  rw [hret]
  exact d.selectedReturn_preserved remove hd ⟨a, d.clears_selectedTerminal remove hc a⟩

/-- Every selected junction is removed, and no unrelated junction or circle is lost. -/
theorem exists_selected_without_circles (G : PortGraph P u v) (remove : G.Joint → Prop)
    (hAccess : G.SelectedAccessible remove) :
    ∃ (H : PortGraph P u v) (d : Smoothing G H []), d.RemovesOnly remove ∧ d.ClearsSelected remove := by
  generalize hn : Fintype.card G.Joint = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hex : ∃ j, remove j
    · obtain ⟨j, hj⟩ := hex
      have hlt : Fintype.card (G.smooth j).Joint < n := by
        rw [← hn]
        exact G.smooth_joint_card_lt j
      obtain ⟨H, d, hd, hc⟩ := ih _ hlt (G.smooth j) (fun k => remove k.val)
        (G.smooth_selectedAccessible remove hAccess j hj) rfl
      have he : G.smoothCircles j = [] := G.smoothCircles_of_not_loop j (G.selected_not_loop remove hAccess j hj)
      have result : ∃ (H : PortGraph P u v) (d : Smoothing G H (G.smoothCircles j ++ [])),
          d.RemovesOnly remove ∧ d.ClearsSelected remove :=
        ⟨H, d.step j, ⟨hj, hd⟩, hc⟩
      have he' : G.smoothCircles j ++ [] = [] := by rw [he]; rfl
      exact Eq.mp (congrArg (fun cs => ∃ (H : PortGraph P u v) (d : Smoothing G H cs),
        d.RemovesOnly remove ∧ d.ClearsSelected remove) he') result
    · exact ⟨G, .refl G, trivial, fun j hj => hex ⟨j, hj⟩⟩

end ThomGame.Pictures.Smoothing

namespace ThomGame.Pictures

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

/-- An ordinary circle-free smoothing trace which removes precisely the selected joints. -/
structure SelectedReduction (G : PortGraph P u v) (remove : G.Joint → Prop) where
  graph : PortGraph P u v
  trace : Smoothing G graph []
  removesOnly : trace.RemovesOnly remove
  clearsSelected : trace.ClearsSelected remove

noncomputable def PortGraph.reduceSelected (G : PortGraph P u v) (remove : G.Joint → Prop)
    (h : G.SelectedAccessible remove) : SelectedReduction G remove :=
  Classical.choice (by
    obtain ⟨H, d, hd, hc⟩ := Smoothing.exists_selected_without_circles G remove h
    exact ⟨⟨H, d, hd, hc⟩⟩)

end ThomGame.Pictures
