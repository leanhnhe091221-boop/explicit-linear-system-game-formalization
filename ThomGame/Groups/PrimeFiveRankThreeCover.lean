module

public import ThomGame.Groups.CompressorPresentation
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma

/-!
# The explicit rank-three, prime-five cover presentation

This is the presentation (E0)--(E4) of Ershov--Jaikin, Theorem 6.9,
specialized to the prime field F₅, with `d` formal variable labels.
The constant coefficient is `none`; it is independent of group inversion.
The rank-three (E5) relations are tautologies because the intermediate
root index is unique. There is no (E6) relation over this base field.
This file constructs the actual finitely presented group. It does not
assert the property (T) theorem for that group.
-/

@[expose] public section
namespace ThomGame.PrimeFiveRankThreeCover

open Compressor

abbrev Coefficient (d : Nat) := Option (Fin d)
abbrev Generator (d : Nat) := Root × Coefficient d

def comm {G : Type*} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

set_option synthInstance.maxSize 256 in
inductive Relation (d : Nat)
  | e0 (r : Root) (m : Coefficient d)
  | e1 (r s : Root) (m n : Coefficient d)
  | e2 (r : Root) (m : Coefficient d)
  | e3 (r : Root) (m : Coefficient d)
  | e4 (r s : Root) (m n l : Coefficient d)
  deriving DecidableEq, Fintype

def relator (d : Nat) : Relation d → FreeGroup (Generator d)
  | .e0 r m => FreeGroup.of (r, m) ^ 5
  | .e1 r s m n =>
      if separated r s then comm (FreeGroup.of (r, m)) (FreeGroup.of (s, n)) else 1
  | .e2 r m =>
      comm (FreeGroup.of (r, m)) (FreeGroup.of (right r, none)) * (FreeGroup.of (across r, m))⁻¹
  | .e3 r m =>
      comm (FreeGroup.of (r, none)) (FreeGroup.of (right r, m)) * (FreeGroup.of (across r, m))⁻¹
  | .e4 r s m n l =>
      if separated (across r) s then
        comm (comm (FreeGroup.of (r, m)) (FreeGroup.of (right r, n))) (FreeGroup.of (s, l))
      else 1

def relators (d : Nat) : Set (FreeGroup (Generator d)) := Set.range (relator d)

def Cover (d : Nat) := PresentedGroup (relators d)
  deriving Group

def of (d : Nat) (r : Root) (m : Coefficient d) : Cover d := PresentedGroup.of (r, m)

theorem relators_finite (d : Nat) : (relators d).Finite := Set.finite_range _

instance (d : Nat) : Group.IsFinitelyPresented (Cover d) := by
  let : Finite (relators d) := (relators_finite d).to_subtype
  exact inferInstanceAs (Group.IsFinitelyPresented (PresentedGroup (relators d)))

theorem generator_card (d : Nat) : Fintype.card (Generator d) = 6 * (d + 1) := by
  simp only [Generator, Fintype.card_prod, Coefficient, Fintype.card_option,
    Fintype.card_fin, Compressor.root_card]

theorem intermediate_unique : ∀ i k j j' : Axis,
    i ≠ k → j ≠ i → j ≠ k → j' ≠ i → j' ≠ k → j = j' := by decide +kernel

theorem third_eq_of_ne (r : Root) (k : Axis) (hki : k ≠ source r) (hkj : k ≠ target r) :
    third r = k :=
  intermediate_unique (source r) (target r) (third r) k r.property
    (third_ne_source r) (third_ne_target r) hki hkj

theorem path_indices (i j k : Axis) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    right ⟨(i, j), hij⟩ = ⟨(j, k), hkj.symm⟩ ∧
      across ⟨(i, j), hij⟩ = ⟨(i, k), hki.symm⟩ := by
  have h := third_eq_of_ne ⟨(i, j), hij⟩ k hki hkj
  constructor <;> apply Subtype.ext <;> simp only [right, across, source, target, h]

/-- Precisely the omitted (E5) equation, for any root-indexed family in any group. -/
theorem e5_tautology {d : Nat} {G : Type*} [Group G] (x : Axis → Axis → Coefficient d → G)
    (i k j j' : Axis) (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k)
    (hj'i : j' ≠ i) (hj'k : j' ≠ k) (m n : Coefficient d) :
    comm (x i j m) (x j k n) = comm (x i j' m) (x j' k n) := by
  rw [intermediate_unique i k j j' hik hji hjk hj'i hj'k]

structure Model (d : Nat) (G : Type*) [Group G] where
  x : Root → Coefficient d → G
  e0 : ∀ r m, x r m ^ 5 = 1
  e1 : ∀ r s m n, separated r s → comm (x r m) (x s n) = 1
  e2 : ∀ r m, comm (x r m) (x (right r) none) = x (across r) m
  e3 : ∀ r m, comm (x r none) (x (right r) m) = x (across r) m
  e4 : ∀ r s m n l, separated (across r) s →
    comm (comm (x r m) (x (right r) n)) (x s l) = 1

namespace Model

variable {d : Nat} {G : Type*} [Group G] (M : Model d G)

theorem eval_relator (r : Relation d) :
    FreeGroup.lift (fun g : Generator d => M.x g.1 g.2) (relator d r) = 1 := by
  cases r with
  | e0 r m => simpa [relator] using M.e0 r m
  | e1 r s m n =>
      by_cases hrs : separated r s
      · simpa [relator, hrs, comm] using M.e1 r s m n hrs
      · simp [relator, hrs]
  | e2 r m =>
      simpa [relator, comm, ← mul_inv_eq_one] using M.e2 r m
  | e3 r m =>
      simpa [relator, comm, ← mul_inv_eq_one] using M.e3 r m
  | e4 r s m n l =>
      by_cases hrs : separated (across r) s
      · simpa [relator, hrs, comm] using M.e4 r s m n l hrs
      · simp [relator, hrs]

def toHom : Cover d →* G := PresentedGroup.toGroup
    (f := fun g : Generator d => M.x g.1 g.2) (fun _ hr => by
  obtain ⟨r, rfl⟩ := hr
  exact M.eval_relator r)

@[simp] theorem toHom_of (r : Root) (m : Coefficient d) : M.toHom (of d r m) = M.x r m :=
  PresentedGroup.toGroup.of _

theorem range_toHom : M.toHom.range = Subgroup.closure (Set.range fun g : Generator d => M.x g.1 g.2) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact PresentedGroup.generated_by (relators d)
      ((Subgroup.closure (Set.range fun a : Generator d => M.x a.1 a.2)).comap M.toHom)
      (fun a => by
        change M.toHom (of d a.1 a.2) ∈ Subgroup.closure (Set.range fun b : Generator d => M.x b.1 b.2)
        rw [M.toHom_of]
        exact Subgroup.subset_closure ⟨a, rfl⟩) g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨of d a.1 a.2, M.toHom_of _ _⟩

end Model

theorem of_e0 (d : Nat) (r : Root) (m : Coefficient d) : of d r m ^ 5 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relators d) ⟨Relation.e0 r m, rfl⟩
  exact (map_pow (PresentedGroup.mk (relators d)) (FreeGroup.of (r, m)) 5).symm.trans h

theorem of_e1 (d : Nat) (r s : Root) (m n : Coefficient d) (hrs : separated r s) :
    comm (of d r m) (of d s n) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relators d) ⟨Relation.e1 r s m n, rfl⟩
  change comm (PresentedGroup.of (rels := relators d) (r, m)) (PresentedGroup.of (s, n)) = 1
  simpa only [relator, hrs, ↓reduceIte, comm, map_mul, map_inv, PresentedGroup.of] using h

theorem of_e2 (d : Nat) (r : Root) (m : Coefficient d) :
    comm (of d r m) (of d (right r) none) = of d (across r) m := by
  have h := PresentedGroup.one_of_mem (rels := relators d) ⟨Relation.e2 r m, rfl⟩
  change comm (PresentedGroup.of (rels := relators d) (r, m)) (PresentedGroup.of (right r, none)) =
    PresentedGroup.of (across r, m)
  apply mul_inv_eq_one.mp
  simpa only [relator, comm, map_mul, map_inv, PresentedGroup.of] using h

theorem of_e3 (d : Nat) (r : Root) (m : Coefficient d) :
    comm (of d r none) (of d (right r) m) = of d (across r) m := by
  have h := PresentedGroup.one_of_mem (rels := relators d) ⟨Relation.e3 r m, rfl⟩
  change comm (PresentedGroup.of (rels := relators d) (r, none)) (PresentedGroup.of (right r, m)) =
    PresentedGroup.of (across r, m)
  apply mul_inv_eq_one.mp
  simpa only [relator, comm, map_mul, map_inv, PresentedGroup.of] using h

theorem of_e4 (d : Nat) (r s : Root) (m n l : Coefficient d) (hrs : separated (across r) s) :
    comm (comm (of d r m) (of d (right r) n)) (of d s l) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := relators d) ⟨Relation.e4 r s m n l, rfl⟩
  change comm (comm (PresentedGroup.of (rels := relators d) (r, m)) (PresentedGroup.of (right r, n)))
    (PresentedGroup.of (s, l)) = 1
  simpa only [relator, hrs, ↓reduceIte, comm, map_mul, map_inv, PresentedGroup.of] using h

def canonicalModel (d : Nat) : Model d (Cover d) where
  x := of d
  e0 := of_e0 d
  e1 := of_e1 d
  e2 := of_e2 d
  e3 := of_e3 d
  e4 := of_e4 d

end ThomGame.PrimeFiveRankThreeCover
