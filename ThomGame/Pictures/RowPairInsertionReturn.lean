module

public import ThomGame.Pictures.RowPairInsertionFaces
public import ThomGame.Pictures.TwoStepReturn

/-!
# Exact face returns through the six inserted ports

Every new face meets an old dart. On old darts, the genuine first return
is the original face permutation followed on its input by one swap. The
two swapped inputs depend on the orientation of the inserted vertex.
-/

@[expose] public section
namespace ThomGame.Pictures.PortGraph.RowPairInsertion

open Equiv MarkedReturn FiniteReturn
open scoped Classical

variable {R S : Type*} {A : SparseSystem R S} {u v : List S}
  {G : SolutionGroup.RowGraph A u v} (s : G.RowPairInsertion)

def Old (x : s.Dart) : Prop := x ∈ Set.range s.old

theorem old_mem (x : G.Dart) : s.Old (s.old x) := ⟨x, rfl⟩

theorem fresh_not_old (b : Bool) (i : Fin 3) : ¬ s.Old (s.fresh b i) := by
  rintro ⟨x, hx⟩
  exact s.old_ne_fresh x b i hx

noncomputable def oldEquiv : G.Dart ≃ Subtype s.Old :=
  Equiv.ofBijective (fun x => ⟨s.old x, s.old_mem x⟩)
    ⟨fun _ _ h => s.old_injective (congrArg Subtype.val h), by
      rintro ⟨x, y, hy⟩
      exact ⟨y, Subtype.ext hy⟩⟩

theorem twin_fresh_one (b : Bool) :
    s.pairing.twin (s.fresh b 1) = s.old (if b then G.pairing.twin s.first else s.first) := by
  cases b
  · rw [← s.twin_first, s.pairing.involutive]; rfl
  · rw [← s.twin_partner_first, s.pairing.involutive]; rfl

theorem twin_fresh_two (b : Bool) :
    s.pairing.twin (s.fresh b 2) = s.old (if b then G.pairing.twin s.second else s.second) := by
  cases b
  · rw [← s.twin_second, s.pairing.involutive]; rfl
  · rw [← s.twin_partner_second, s.pairing.involutive]; rfl

variable (o : Bool)

theorem step_first :
    (s.graph o).circuitStep (s.old s.first) = s.fresh false (if o then 0 else 2) := by
  rw [(s.graph o).circuitStep_apply, show (s.graph o).pairing.twin (s.old s.first) = _ from s.twin_first,
    s.rotation_fresh]
  cases o <;> rfl

theorem step_second :
    (s.graph o).circuitStep (s.old s.second) = s.fresh false (if o then 1 else 0) := by
  rw [(s.graph o).circuitStep_apply, show (s.graph o).pairing.twin (s.old s.second) = _ from s.twin_second,
    s.rotation_fresh]
  cases o <;> rfl

theorem step_partner_first :
    (s.graph o).circuitStep (s.old (G.pairing.twin s.first)) = s.fresh true (if o then 2 else 0) := by
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.old (G.pairing.twin s.first)) = _ from s.twin_partner_first,
    s.rotation_fresh]
  cases o <;> rfl

theorem step_partner_second :
    (s.graph o).circuitStep (s.old (G.pairing.twin s.second)) = s.fresh true (if o then 0 else 1) := by
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.old (G.pairing.twin s.second)) = _ from s.twin_partner_second,
    s.rotation_fresh]
  cases o <;> rfl

theorem step_fresh_zero (b : Bool) :
    (s.graph o).circuitStep (s.fresh b 0) =
      s.fresh (!b) (if b then (if o then 2 else 1) else (if o then 1 else 2)) := by
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.fresh b 0) = _ from s.twin_spoke b, s.rotation_fresh]
  cases o <;> cases b <;> rfl

theorem step_fresh_one (b : Bool) :
    (s.graph o).circuitStep (s.fresh b 1) =
      s.old (G.rotation (if b then G.pairing.twin s.first else s.first)) := by
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.fresh b 1) = _ from s.twin_fresh_one b, s.rotation_old]

theorem step_fresh_two (b : Bool) :
    (s.graph o).circuitStep (s.fresh b 2) =
      s.old (G.rotation (if b then G.pairing.twin s.second else s.second)) := by
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.fresh b 2) = _ from s.twin_fresh_two b, s.rotation_old]

theorem hit_direct {x y : s.Dart} (h : (s.graph o).circuitStep x = y) :
    Hit (s.graph o).circuitStep s.Old x y := h ▸ Hit.direct x

theorem hit_skip_fresh {x y : s.Dart} (b : Bool) (i : Fin 3)
    (h : (s.graph o).circuitStep x = s.fresh b i)
    (ht : Hit (s.graph o).circuitStep s.Old (s.fresh b i) y) :
    Hit (s.graph o).circuitStep s.Old x y := by
  apply Hit.skip x
  · rw [h]
    exact s.fresh_not_old b i
  · rwa [h]

def zeroExit (b : Bool) : G.Dart :=
  if b then (if o then s.second else s.first)
  else G.pairing.twin (if o then s.first else s.second)

theorem hit_fresh_zero (b : Bool) :
    Hit (s.graph o).circuitStep s.Old (s.fresh b 0) (s.old (G.rotation (s.zeroExit o b))) := by
  cases o <;> cases b
  · exact s.hit_skip_fresh false true 2 (s.step_fresh_zero false false)
      (s.hit_direct false (s.step_fresh_two false true))
  · exact s.hit_skip_fresh false false 1 (s.step_fresh_zero false true)
      (s.hit_direct false (s.step_fresh_one false false))
  · exact s.hit_skip_fresh true true 1 (s.step_fresh_zero true false)
      (s.hit_direct true (s.step_fresh_one true true))
  · exact s.hit_skip_fresh true false 2 (s.step_fresh_zero true true)
      (s.hit_direct true (s.step_fresh_two true false))

abbrev cutLeft : G.Dart := if o then s.second else s.first
abbrev cutRight : G.Dart := G.pairing.twin (if o then s.first else s.second)

theorem cut_distinct : s.cutLeft o ≠ s.cutRight o := by
  cases o
  · exact s.first_ne_twin_second
  · intro h
    have hh := congrArg G.pairing.twin h
    rw [G.pairing.involutive] at hh
    exact s.first_ne_twin_second hh.symm

noncomputable def returnPerm : Perm G.Dart := G.circuitStep * swap (s.cutLeft o) (s.cutRight o)

theorem return_hit (x : G.Dart) :
    Hit (s.graph o).circuitStep s.Old (s.old x) (s.old (s.returnPerm o x)) := by
  have h12 := s.first_ne_second
  have ht1t2 := G.pairing.involutive.injective.ne h12
  by_cases h1 : x = s.first
  · subst x
    cases o
    · have he : s.returnPerm false s.first = G.rotation s.second := by
        change G.circuitStep (swap s.first (G.pairing.twin s.second) s.first) = _
        rw [swap_apply_left, G.circuitStep_apply, G.pairing.involutive]
      rw [he]
      exact s.hit_skip_fresh false false 2 (s.step_first false)
        (s.hit_direct false (s.step_fresh_two false false))
    · have he : s.returnPerm true s.first = G.rotation (G.pairing.twin s.first) := by
        change G.circuitStep (swap s.second (G.pairing.twin s.first) s.first) = _
        rw [swap_apply_of_ne_of_ne h12 (G.pairing.ne_self _).symm]
        rfl
      rw [he]
      exact s.hit_skip_fresh true false 0 (s.step_first true) (s.hit_fresh_zero true false)
  by_cases h2 : x = s.second
  · subst x
    cases o
    · have he : s.returnPerm false s.second = G.rotation (G.pairing.twin s.second) := by
        change G.circuitStep (swap s.first (G.pairing.twin s.second) s.second) = _
        rw [swap_apply_of_ne_of_ne h12.symm (G.pairing.ne_self _).symm]
        rfl
      rw [he]
      exact s.hit_skip_fresh false false 0 (s.step_second false) (s.hit_fresh_zero false false)
    · have he : s.returnPerm true s.second = G.rotation s.first := by
        change G.circuitStep (swap s.second (G.pairing.twin s.first) s.second) = _
        rw [swap_apply_left, G.circuitStep_apply, G.pairing.involutive]
      rw [he]
      exact s.hit_skip_fresh true false 1 (s.step_second true)
        (s.hit_direct true (s.step_fresh_one true false))
  by_cases ht1 : x = G.pairing.twin s.first
  · subst x
    cases o
    · have he : s.returnPerm false (G.pairing.twin s.first) = G.rotation s.first := by
        change G.circuitStep (swap s.first (G.pairing.twin s.second) (G.pairing.twin s.first)) = _
        rw [swap_apply_of_ne_of_ne (G.pairing.ne_self _) ht1t2]
        exact congrArg G.rotation (G.pairing.involutive _)
      rw [he]
      exact s.hit_skip_fresh false true 0 (s.step_partner_first false) (s.hit_fresh_zero false true)
    · have he : s.returnPerm true (G.pairing.twin s.first) = G.rotation (G.pairing.twin s.second) := by
        simp [returnPerm, cutLeft, cutRight, G.circuitStep_apply]
      rw [he]
      exact s.hit_skip_fresh true true 2 (s.step_partner_first true)
        (s.hit_direct true (s.step_fresh_two true true))
  by_cases ht2 : x = G.pairing.twin s.second
  · subst x
    cases o
    · have he : s.returnPerm false (G.pairing.twin s.second) = G.rotation (G.pairing.twin s.first) := by
        simp [returnPerm, cutLeft, cutRight, G.circuitStep_apply]
      rw [he]
      exact s.hit_skip_fresh false true 1 (s.step_partner_second false)
        (s.hit_direct false (s.step_fresh_one false true))
    · have he : s.returnPerm true (G.pairing.twin s.second) = G.rotation s.second := by
        change G.circuitStep (swap s.second (G.pairing.twin s.first) (G.pairing.twin s.second)) = _
        rw [swap_apply_of_ne_of_ne (G.pairing.ne_self _) ht1t2.symm]
        exact congrArg G.rotation (G.pairing.involutive _)
      rw [he]
      exact s.hit_skip_fresh true true 0 (s.step_partner_second true) (s.hit_fresh_zero true true)
  have hs : swap (s.cutLeft o) (s.cutRight o) x = x := by
    cases o
    · exact swap_apply_of_ne_of_ne h1 ht2
    · exact swap_apply_of_ne_of_ne h2 ht1
  have he : s.returnPerm o x = G.circuitStep x := by rw [returnPerm, Perm.mul_apply, hs]
  rw [he]
  apply s.hit_direct o
  rw [(s.graph o).circuitStep_apply,
    show (s.graph o).pairing.twin (s.old x) = _ from s.twin_old_away x h1 h2 ht1 ht2,
    s.rotation_old]
  rfl

theorem return_congr (x : G.Dart) :
    perm (s.graph o).circuitStep s.Old (s.oldEquiv x) = s.oldEquiv (s.returnPerm o x) :=
  Subtype.ext (eq_perm_of_hit (s.graph o).circuitStep s.Old (s.oldEquiv x)
    (s.old_mem _) (s.return_hit o x)).symm

theorem hit_sameCycle {x y : s.Dart} (h : Hit (s.graph o).circuitStep s.Old x y) :
    (s.graph o).circuitStep.SameCycle x y := by
  induction h with
  | direct _ => exact Perm.SameCycle.rfl.apply_right
  | skip _ _ _ ih => exact Perm.SameCycle.rfl.apply_right.trans ih

theorem all_faces_hit_old : ∀ x : (s.graph o).Dart,
    ∃ y : Subtype s.Old, (s.graph o).circuitStep.SameCycle x y.val := by
  intro x
  obtain ⟨x, rfl⟩ := s.ports.surjective x
  rcases x with x | ⟨b, i⟩
  · exact ⟨s.oldEquiv x, Perm.SameCycle.rfl⟩
  · change ∃ y : Subtype s.Old, (s.graph o).circuitStep.SameCycle (s.fresh b i) y.val
    fin_cases i
    · refine ⟨s.oldEquiv (G.rotation (s.zeroExit o b)), ?_⟩
      exact s.hit_sameCycle o (s.hit_fresh_zero o b)
    · refine ⟨s.oldEquiv (G.rotation (if b then G.pairing.twin s.first else s.first)),
        ⟨1, ?_⟩⟩
      exact s.step_fresh_one o b
    · refine ⟨s.oldEquiv (G.rotation (if b then G.pairing.twin s.second else s.second)),
        ⟨1, ?_⟩⟩
      exact s.step_fresh_two o b

noncomputable def faceOrbitEquiv : Orbit (s.returnPerm o) ≃ Orbit (s.graph o).circuitStep :=
  (orbitEquiv (s.returnPerm o) (perm (s.graph o).circuitStep s.Old) s.oldEquiv
    (s.return_congr o)).trans (orbitEquivOfHits (s.graph o).circuitStep s.Old (s.all_faces_hit_old o))

theorem returnPerm_eq_splice : s.returnPerm o =
    CycleSurgery.splice G.circuitStep (G.circuitStep (s.cutLeft o)) (G.circuitStep (s.cutRight o)) := by
  rw [returnPerm, mul_swap_eq_swap_mul]
  rfl

theorem face_count_of_same_face
    (hf : G.circuitStep.SameCycle (s.cutLeft o) (s.cutRight o)) :
    Nat.card (Orbit (s.graph o).circuitStep) = Nat.card (Orbit G.circuitStep) + 1 := by
  rw [← Nat.card_congr (s.faceOrbitEquiv o), s.returnPerm_eq_splice]
  exact CycleSurgery.orbit_card_split G.circuitStep
    (G.circuitStep.injective.ne (s.cut_distinct o)) hf.apply_left.apply_right

end ThomGame.Pictures.PortGraph.RowPairInsertion
