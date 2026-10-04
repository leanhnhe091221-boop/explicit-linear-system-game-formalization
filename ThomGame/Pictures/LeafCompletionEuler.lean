module

public import ThomGame.Pictures.InvariantEuler

/-!
# Replacing fixed edge ports by genuine boundary leaves

Each fixed port of a partial involution receives a new leaf, paired to
that port. The old rotation is unchanged and the new leaves are fixed
vertices. First-return maps preserve the old edge and face orbits, while
vertices and darts gain the same number. Euler count and components are
therefore preserved exactly.
-/

@[expose] public section
namespace ThomGame.Pictures.LeafCompletion

open Equiv FiniteReturn RibbonConnectivity
open scoped Classical

variable {D : Type*} (r t : Perm D)

abbrev Fixed := {a : D // t a = a}
abbrev Dart := D ⊕ Fixed t

abbrev embedding : D ↪ Dart t := ⟨Sum.inl, Sum.inl_injective⟩

def project : Dart t → D := Sum.elim id Subtype.val

noncomputable def turn : Dart t → Dart t
  | .inl a => if ha : t a = a then .inr ⟨a, ha⟩ else .inl (t a)
  | .inr a => .inl a.val

theorem turn_involutive (ht : Function.Involutive t) : Function.Involutive (turn t) := by
  rintro (a | a)
  · by_cases ha : t a = a
    · simp only [turn, dite_eq_left ha]
    · have hb : t (t a) ≠ t a := fun he => ha ((ht a).symm.trans he).symm
      rw [turn, dite_eq_right ha, turn, dite_eq_right hb, ht a]
  · simp only [turn, dite_eq_left a.property]

noncomputable def pairing (ht : Function.Involutive t) : Perm (Dart t) :=
  ⟨turn t, turn t, turn_involutive t ht, turn_involutive t ht⟩

def rotation : Perm (Dart t) := Equiv.sumCongr r 1

noncomputable def face (ht : Function.Involutive t) : Perm (Dart t) := rotation r t * pairing t ht

variable (ht : Function.Involutive t)

theorem pairing_inl_fixed (a : Fixed t) : pairing t ht (.inl a.val) = .inr a := by
  change turn t (.inl a.val) = .inr a
  rw [turn, dite_eq_left a.property]

theorem pairing_inl_moving {a : D} (ha : t a ≠ a) : pairing t ht (.inl a) = .inl (t a) :=
  dite_eq_right ha

theorem pairing_inr (a : Fixed t) : pairing t ht (.inr a) = .inl a.val := rfl

theorem rotation_inl (a : D) : rotation r t (.inl a) = .inl (r a) := rfl
theorem rotation_inr (a : Fixed t) : rotation r t (.inr a) = .inr a := rfl

theorem edge_advances : Advances (pairing t ht) t (embedding t) := by
  intro a
  by_cases ha : t a = a
  · refine Or.inr ⟨?_, ?_⟩
    · change Sum.inl (t a) = pairing t ht (pairing t ht (.inl a))
      rw [pairing_inl_fixed t ht ⟨a, ha⟩, pairing_inr, ha]
    · intro b
      change Sum.inl b ≠ pairing t ht (.inl a)
      rw [pairing_inl_fixed t ht ⟨a, ha⟩]
      intro h
      cases h
  · exact Or.inl (pairing_inl_moving t ht ha).symm

theorem face_advances : Advances (face r t ht) (r * t) (embedding t) := by
  intro a
  by_cases ha : t a = a
  · have hs : face r t ht (.inl a) = .inr ⟨a, ha⟩ := by
      rw [face, Perm.mul_apply, pairing_inl_fixed t ht ⟨a, ha⟩, rotation_inr]
    refine Or.inr ⟨?_, ?_⟩
    · change Sum.inl ((r * t) a) = face r t ht (face r t ht (.inl a))
      rw [hs]
      change Sum.inl (r (t a)) = rotation r t (pairing t ht (.inr ⟨a, ha⟩))
      rw [pairing_inr, rotation_inl, ha]
    · intro b
      change Sum.inl b ≠ face r t ht (.inl a)
      rw [hs]
      intro h
      cases h
  · exact Or.inl (by
      change Sum.inl (r (t a)) = rotation r t (pairing t ht (.inl a))
      rw [pairing_inl_moving t ht ha, rotation_inl])

theorem embed_connected {a b : D} (h : Connected r t a b) :
    Connected (rotation r t) (pairing t ht) (.inl a) (.inl b) := by
  apply h.lift (fun x : D => (Sum.inl x : Dart t)) ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · intro a
    exact Connected.edge (p := rotation r t) (f := pairing t ht) (.inl a)
  · intro a
    by_cases ha : t a = a
    · rw [ha]
      exact Connected.refl _
    · rw [← pairing_inl_moving t ht ha]
      exact Connected.circuit _

theorem project_connected {a b : Dart t} (h : Connected (rotation r t) (pairing t ht) a b) :
    Connected r t (project t a) (project t b) := by
  apply h.lift (project t) ⟨Connected.refl, Connected.symm, Connected.trans⟩
  · rintro (a | a)
    · exact Connected.edge a
    · exact Connected.refl a.val
  · rintro (a | a)
    · by_cases ha : t a = a
      · rw [pairing_inl_fixed t ht ⟨a, ha⟩]
        exact Connected.refl a
      · rw [pairing_inl_moving t ht ha]
        exact Connected.circuit a
    · exact Connected.refl a.val

noncomputable def componentEquiv : Component (rotation r t) (pairing t ht) ≃ Component r t where
  toFun := Quotient.lift (fun a => component r t (project t a))
    (fun _ _ h => (component_eq_iff _ _ _ _).mpr (project_connected r t ht h))
  invFun := Quotient.lift (fun a => component (rotation r t) (pairing t ht) (.inl a))
    (fun _ _ h => (component_eq_iff _ _ _ _).mpr (embed_connected r t ht h))
  left_inv c := by
    refine Quotient.inductionOn c ?_
    rintro (a | a)
    · rfl
    · apply (component_eq_iff _ _ _ _).mpr
      have h := Connected.circuit (p := rotation r t) (f := pairing t ht) (.inl a.val)
      rw [pairing_inl_fixed t ht a] at h
      exact h
  right_inv c := Quotient.inductionOn c (fun _ => rfl)

variable [Finite D]

theorem edge_orbit_card : Nat.card (Orbit (pairing t ht)) = Nat.card (Orbit t) := by
  have hb : Function.Bijective (edge_advances t ht).orbitMap := by
    refine ⟨(edge_advances t ht).orbitMap_injective, ?_⟩
    apply (edge_advances t ht).orbitMap_surjective_iff.mpr
    rintro (a | a)
    · exact ⟨a, Perm.SameCycle.rfl⟩
    · refine ⟨a.val, 1, ?_⟩
      change (pairing t ht ^ (1 : Int)) (.inl a.val) = .inr a
      rw [zpow_one, pairing_inl_fixed t ht a]
  exact (Nat.card_congr (Equiv.ofBijective (edge_advances t ht).orbitMap hb)).symm

theorem face_orbit_card : Nat.card (Orbit (face r t ht)) = Nat.card (Orbit (r * t)) := by
  have hb : Function.Bijective (face_advances r t ht).orbitMap := by
    refine ⟨(face_advances r t ht).orbitMap_injective, ?_⟩
    apply (face_advances r t ht).orbitMap_surjective_iff.mpr
    rintro (a | a)
    · exact ⟨a, Perm.SameCycle.rfl⟩
    · refine ⟨a.val, 1, ?_⟩
      change (face r t ht ^ (1 : Int)) (.inl a.val) = .inr a
      simp only [zpow_one, face, Perm.mul_apply, pairing_inl_fixed t ht a, rotation_inr]
  exact (Nat.card_congr (Equiv.ofBijective (face_advances r t ht).orbitMap hb)).symm

theorem count_eq : RotationEuler.count (rotation r t) (pairing t ht) = RotationEuler.count r t := by
  have hr : Nat.card (Orbit (rotation r t)) = Nat.card (Orbit r) + Nat.card (Fixed t) := by
    rw [rotation, orbit_card_sum, Nat.card_congr (orbitOneEquiv (Fixed t))]
  have he := edge_orbit_card t ht
  have hf := face_orbit_card r t ht
  have hfo := Nat.card_congr (RotationEuler.productOrbitEquiv r t ht)
  have hfn := Nat.card_congr (RotationEuler.productOrbitEquiv (rotation r t) (pairing t ht)
    (turn_involutive t ht))
  change Nat.card (Orbit (pairing t ht * rotation r t)) = Nat.card (Orbit (face r t ht)) at hfn
  have hd : Nat.card (Dart t) = Nat.card D + Nat.card (Fixed t) := Nat.card_sum
  unfold RotationEuler.count
  omega

theorem saturated (hEuler : RotationEuler.count r t = 2 * Nat.card (Component r t)) :
    RotationEuler.count (rotation r t) (pairing t ht) =
      2 * Nat.card (Component (rotation r t) (pairing t ht)) := by
  rw [count_eq, Nat.card_congr (componentEquiv r t ht), hEuler]

end ThomGame.Pictures.LeafCompletion
