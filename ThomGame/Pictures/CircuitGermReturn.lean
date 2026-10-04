module

public import ThomGame.Pictures.CircuitGermGraph
public import ThomGame.Pictures.ReturnPaths

/-!
# Exact edge recovery after gluing a germ and its opposite region

Raw ports distinguish the two ports of every new seam junction. Crossing
an edge and then turning only at a seam gives a permutation. Its first
return to old ports is exactly the old edge pairing. This includes chords
whose two endpoints both receive seam junctions.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.SimpleCircuit

open Equiv MarkedReturn
open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {G : PortGraph P [] []} (C : G.SimpleCircuit)
  (hEuler : RotationEuler.count G.circuitStep G.pairing.perm =
    2 * Nat.card (RibbonConnectivity.Component G.circuitStep G.pairing.perm))

abbrev GluingRaw (s : Bool) := C.GermRaw s ⊕ Subtype (C.KeptDart (!s))

abbrev GluingOriginal (s : Bool) := Subtype (C.UncutDart s) ⊕ Subtype (C.KeptDart (!s))

noncomputable def frontierKept (s : Bool) (a : Subtype (C.Frontier (!s))) :
    Subtype (C.KeptDart (!s)) := ⟨a.val, ((C.frontier_iff hEuler (!s) a.val).mp a.property).2⟩

noncomputable def gluingRawPairing (s : Bool) :
    Pairing (Sum.elim (C.germRawLabel s) (fun a : Subtype (C.KeptDart (!s)) =>
      Port.label G.jointLabel a.val)) :=
  (C.germRawPairing s).sum (C.keptPairing (!s))

noncomputable def gluingOriginalPairing (s : Bool) :
    Pairing (Sum.elim (fun a : Subtype (C.UncutDart s) => Port.label G.jointLabel a.val)
      (fun a : Subtype (C.KeptDart (!s)) => Port.label G.jointLabel a.val)) :=
  (C.uncutPairing s).sum (C.keptPairing (!s))

/-- Turn at the new seam junctions, fixing every original port. -/
noncomputable def gluingSeamTurn (s : Bool) : C.GluingRaw s → C.GluingRaw s
  | .inl (.inl a) => .inl (.inl a)
  | .inl (.inr (a, false)) => .inl (.inr (a, false))
  | .inl (.inr (a, true)) => .inr (C.frontierKept hEuler s a)
  | .inr a => if ha : C.Frontier (!s) a.val then .inl (.inr (⟨a.val, ha⟩, true)) else .inr a

include hEuler in
theorem gluingSeamTurn_involutive (s : Bool) : Function.Involutive (C.gluingSeamTurn hEuler s) := by
  rintro (a | a)
  · rcases a with a | ⟨a, b⟩
    · rfl
    · cases b
      · rfl
      · simp [gluingSeamTurn, frontierKept, a.property]
  · by_cases ha : C.Frontier (!s) a.val
    · simp [gluingSeamTurn, ha, frontierKept]
    · simp [gluingSeamTurn, ha]

noncomputable def gluingSeamPerm (s : Bool) : Equiv.Perm (C.GluingRaw s) :=
  ⟨C.gluingSeamTurn hEuler s, C.gluingSeamTurn hEuler s,
    C.gluingSeamTurn_involutive hEuler s, C.gluingSeamTurn_involutive hEuler s⟩

noncomputable def gluingStep (s : Bool) : Equiv.Perm (C.GluingRaw s) :=
  C.gluingSeamPerm hEuler s * (C.gluingRawPairing s).perm

def GluingRetained (s : Bool) : C.GluingRaw s → Prop
  | .inl (.inl _) => True
  | .inl (.inr (_, b)) => b = false
  | .inr a => ¬ C.Frontier (!s) a.val

include hEuler in
theorem gluingRetained_iff_fixed (s : Bool) (a : C.GluingRaw s) :
    C.GluingRetained s a ↔ C.gluingSeamTurn hEuler s a = a := by
  rcases a with (a | ⟨a, b⟩) | a
  · simp [GluingRetained, gluingSeamTurn]
  · cases b <;> simp [GluingRetained, gluingSeamTurn]
  · by_cases ha : C.Frontier (!s) a.val <;> simp [GluingRetained, gluingSeamTurn, ha]

def gluingRawVal (s : Bool) : C.GluingRaw s → G.Dart
  | .inl (.inl a) => a.val
  | .inl (.inr (a, _)) => a.val
  | .inr a => a.val

noncomputable def gluingOriginalPort (s : Bool) : C.GluingOriginal s → C.GluingRaw s
  | .inl a => .inl (.inl a)
  | .inr a => if ha : C.Frontier (!s) a.val then .inl (.inr (⟨a.val, ha⟩, false)) else .inr a

theorem gluingOriginalPort_retained (s : Bool) (a : C.GluingOriginal s) :
    C.GluingRetained s (C.gluingOriginalPort s a) := by
  rcases a with a | a
  · trivial
  · by_cases ha : C.Frontier (!s) a.val <;> simp [gluingOriginalPort, GluingRetained, ha]

noncomputable def gluingRetainedEquiv (s : Bool) :
    C.GluingOriginal s ≃ Subtype (C.GluingRetained s) where
  toFun a := ⟨C.gluingOriginalPort s a, C.gluingOriginalPort_retained s a⟩
  invFun
    | ⟨.inl (.inl a), _⟩ => .inl a
    | ⟨.inl (.inr (a, _)), _⟩ => .inr (C.frontierKept hEuler s a)
    | ⟨.inr a, _⟩ => .inr a
  left_inv a := by
    rcases a with a | a
    · rfl
    · by_cases ha : C.Frontier (!s) a.val <;> simp [gluingOriginalPort, ha, frontierKept]
  right_inv a := by
    rcases a with ⟨(a | a), ha⟩
    · rcases a with a | ⟨a, b⟩
      · rfl
      · change b = false at ha
        subst b
        apply Subtype.ext
        simp [gluingOriginalPort, frontierKept, a.property]
    · apply Subtype.ext
      exact dite_eq_right ha

include hEuler in
theorem gluingStep_uncut (s : Bool) (a : Subtype (C.UncutDart s)) :
    C.gluingStep hEuler s (.inl (.inl a)) = .inl (.inl ((C.uncutPairing s).twin a)) := rfl

include hEuler in
theorem gluingStep_outward (s : Bool) (a : Subtype (C.Frontier (!s))) :
    C.gluingStep hEuler s (.inl (.inr (a, false))) = .inr (C.frontierKept hEuler s a) := rfl

include hEuler in
theorem gluingStep_boundary (s : Bool) (a : Subtype (C.Frontier (!s))) :
    C.gluingStep hEuler s (.inl (.inr (a, true))) = .inl (.inr (a, false)) := rfl

include hEuler in
theorem gluingStep_region (s : Bool) (a : Subtype (C.KeptDart (!s))) :
    C.gluingStep hEuler s (.inr a) =
      if ha : C.Frontier (!s) ((C.keptPairing (!s)).twin a).val then
        .inl (.inr (⟨((C.keptPairing (!s)).twin a).val, ha⟩, true))
      else .inr ((C.keptPairing (!s)).twin a) := rfl

include hEuler in
theorem gluing_region_hit (s : Bool) (a : Subtype (C.KeptDart (!s))) :
    Hit (C.gluingStep hEuler s) (C.GluingRetained s) (.inr a)
      (C.gluingOriginalPort s (.inr ((C.keptPairing (!s)).twin a))) := by
  by_cases ha : C.Frontier (!s) ((C.keptPairing (!s)).twin a).val
  · have hn : ¬ C.GluingRetained s (C.gluingStep hEuler s (.inr a)) := by
      rw [C.gluingStep_region, dite_eq_left ha]
      simp [GluingRetained]
    apply Hit.skip _ hn
    rw [C.gluingStep_region, dite_eq_left ha]
    simpa only [gluingOriginalPort, dite_eq_left ha, gluingStep_boundary] using
      (Hit.direct (f := C.gluingStep hEuler s) (p := C.GluingRetained s)
        (.inl (.inr (⟨((C.keptPairing (!s)).twin a).val, ha⟩, true))))
  · simpa only [gluingStep_region, dite_eq_right ha, gluingOriginalPort] using
      (Hit.direct (f := C.gluingStep hEuler s) (p := C.GluingRetained s) (.inr a))

include hEuler in
theorem gluing_original_hit (s : Bool) (a : C.GluingOriginal s) :
    Hit (C.gluingStep hEuler s) (C.GluingRetained s) (C.gluingOriginalPort s a)
      (C.gluingOriginalPort s ((C.gluingOriginalPairing s).twin a)) := by
  rcases a with a | a
  · exact Hit.direct _
  · change Hit _ _ (C.gluingOriginalPort s (.inr a))
      (C.gluingOriginalPort s (.inr ((C.keptPairing (!s)).twin a)))
    by_cases ha : C.Frontier (!s) a.val
    · rw [gluingOriginalPort, dite_eq_left ha]
      apply Hit.skip _
      · rw [C.gluingStep_outward]
        exact fun hh => hh ha
      · rw [C.gluingStep_outward]
        exact C.gluing_region_hit hEuler s a
    · rw [gluingOriginalPort, dite_eq_right ha]
      exact C.gluing_region_hit hEuler s a

include hEuler in
/-- The exact successor after bypassing every new seam junction. -/
theorem gluing_firstReturn (s : Bool) (a : C.GluingOriginal s) :
    MarkedReturn.perm (C.gluingStep hEuler s) (C.GluingRetained s)
      (C.gluingRetainedEquiv hEuler s a) =
        C.gluingRetainedEquiv hEuler s ((C.gluingOriginalPairing s).twin a) := by
  apply Subtype.ext
  exact (MarkedReturn.eq_perm_of_hit _ _ _ (C.gluingOriginalPort_retained s _)
    (C.gluing_original_hit hEuler s a)).symm

include hEuler in
theorem uncut_not_opposite_kept (s : Bool) {a : G.Dart}
    (hu : C.UncutDart s a) (hk : C.KeptDart (!s) a) : False := by
  rcases hu with hm | hu
  · exact hk.1 hm
  · exact (Bool.not_eq_self s).mp (C.onSide_unique hEuler hu.2 hk.2).symm

theorem gluingOriginal_partition (s : Bool) (a : G.Dart) :
    C.UncutDart s a ∨ C.KeptDart (!s) a ↔
      RibbonConnectivity.Connected G.circuitStep G.pairing.perm a C.cutBase := by
  constructor
  · rintro ((hm | hk) | hk)
    · exact (C.old_connected_base_iff a).mpr (C.cut_marked_reaches_seam hm)
    · exact (C.old_connected_base_iff_onSide a).mpr ⟨s, hk.2⟩
    · exact (C.old_connected_base_iff_onSide a).mpr ⟨!s, hk.2⟩
  · intro hc
    by_cases hm : C.Marked a
    · exact Or.inl (Or.inl hm)
    · obtain ⟨t, ht⟩ := (C.old_connected_base_iff_onSide a).mp hc
      cases s <;> cases t
      · exact Or.inl (Or.inr ⟨hm, ht⟩)
      · exact Or.inr ⟨hm, ht⟩
      · exact Or.inr ⟨hm, ht⟩
      · exact Or.inl (Or.inr ⟨hm, ht⟩)

def gluingOriginalVal (s : Bool) : C.GluingOriginal s → G.Dart :=
  Sum.elim Subtype.val Subtype.val

theorem gluingOriginalPort_val (s : Bool) (a : C.GluingOriginal s) :
    C.gluingRawVal s (C.gluingOriginalPort s a) = C.gluingOriginalVal s a := by
  rcases a with a | a
  · rfl
  · by_cases ha : C.Frontier (!s) a.val <;> simp [gluingOriginalPort, ha, gluingRawVal, gluingOriginalVal]

include hEuler in
theorem gluingRetainedEquiv_symm_val (s : Bool) (a : Subtype (C.GluingRetained s)) :
    C.gluingOriginalVal s ((C.gluingRetainedEquiv hEuler s).symm a) = C.gluingRawVal s a.val := by
  obtain ⟨b, rfl⟩ := (C.gluingRetainedEquiv hEuler s).surjective a
  rw [Equiv.symm_apply_apply]
  exact (C.gluingOriginalPort_val s b).symm

noncomputable def gluingComponentEquiv (s : Bool) :
    C.GluingOriginal s ≃ {a : G.Dart //
      RibbonConnectivity.Connected G.circuitStep G.pairing.perm a C.cutBase} where
  toFun
    | .inl a => ⟨a.val, (C.gluingOriginal_partition s a.val).mp (Or.inl a.property)⟩
    | .inr a => ⟨a.val, (C.gluingOriginal_partition s a.val).mp (Or.inr a.property)⟩
  invFun a := if hu : C.UncutDart s a.val then .inl ⟨a.val, hu⟩ else
    .inr ⟨a.val, ((C.gluingOriginal_partition s a.val).mpr a.property).resolve_left hu⟩
  left_inv a := by
    rcases a with a | a
    · simp [a.property]
    · have hu : ¬ C.UncutDart s a.val := fun hu => C.uncut_not_opposite_kept hEuler s hu a.property
      simp [hu]
  right_inv a := by by_cases hu : C.UncutDart s a.val <;> simp [hu]

include hEuler in
theorem gluingComponentEquiv_val (s : Bool) (a : C.GluingOriginal s) :
    (C.gluingComponentEquiv hEuler s a).val = C.gluingOriginalVal s a := by cases a <;> rfl

theorem gluingOriginal_twin_val (s : Bool) (a : C.GluingOriginal s) :
    C.gluingOriginalVal s ((C.gluingOriginalPairing s).twin a) =
      G.pairing.twin (C.gluingOriginalVal s a) := by cases a <;> rfl

end ThomGame.Pictures.PortGraph.SimpleCircuit
