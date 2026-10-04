module

public import ThomGame.Groups.PrimeFiveCoverPairGenerators
public import ThomGame.Groups.PrimeFiveCoverCyclicGeneration
public import ThomGame.Groups.CentralCommutatorExponent

/-!
# Finite p-group and class-two structure of the cyclic root pairs

These are unconditional properties of the actual cover and every model
of its relations. No orthogonality bound or property (T) is claimed here.
-/

@[expose] public section
namespace ThomGame.PrimeFiveRankThreeCover

open Compressor
open scoped commutatorElement

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace Model

variable {d : Nat} {G : Type*} [Group G] (M : Model d G)

theorem rootSubgroup_isPGroup (r : Root) : IsPGroup 5 (M.rootSubgroup r) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro x
  exact ⟨1, by simpa only [pow_one] using M.rootSubgroup_pow r x⟩

theorem pairSubgroup_isPGroup (r : Root) : IsPGroup 5 (M.pairSubgroup r) := by
  refine isPGroup_of_central_commutator_generators (M.pairOf_generates r) ?_ 5 ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    exact M.pairOf_triple r a b c
  · rintro _ ⟨a, rfl⟩
    exact M.pairOf_pow r a

theorem pairSubgroup_nilpotent (r : Root) : Group.IsNilpotent (M.pairSubgroup r) :=
  nilpotent_of_commutator_le_center (M.pairSubgroup_commutator_le_center r)

theorem pairSubgroup_nilpotencyClass_le_two (r : Root) : Group.nilpotencyClass (M.pairSubgroup r) ≤ 2 :=
  nilpotencyClass_le_two_of_commutator_le_center (M.pairSubgroup_commutator_le_center r)

theorem pairSubgroup_card (r : Root) : ∃ n : Nat, Nat.card (M.pairSubgroup r) = 5 ^ n :=
  (IsPGroup.iff_card).mp (M.pairSubgroup_isPGroup r)

theorem rootSubgroup_proper_index (r : Root) (H : Subgroup (M.rootSubgroup r)) (hH : H ≠ ⊤) :
    5 ≤ H.index := prime_le_index_of_proper (M.rootSubgroup_isPGroup r) H hH

theorem pairSubgroup_proper_index (r : Root) (H : Subgroup (M.pairSubgroup r)) (hH : H ≠ ⊤) :
    5 ≤ H.index := prime_le_index_of_proper (M.pairSubgroup_isPGroup r) H hH

end Model

abbrev pairSubgroup (d : Nat) (r : Root) : Subgroup (Cover d) := (canonicalModel d).pairSubgroup r

theorem cyclic_pairSubgroup (d : Nat) (c : Axis) :
    pairSubgroup d (cyclicRoot c) = rootSubgroup d (cyclicRoot c) ⊔ rootSubgroup d (cyclicRoot (finRotate 3 c)) := by
  rw [pairSubgroup, (canonicalModel d).pairSubgroup_eq_sup, right_cyclicRoot]

theorem pairSubgroup_finite (d : Nat) (r : Root) : Finite (pairSubgroup d r) :=
  (canonicalModel d).pairSubgroup_finite r

theorem pairSubgroup_isPGroup (d : Nat) (r : Root) : IsPGroup 5 (pairSubgroup d r) :=
  (canonicalModel d).pairSubgroup_isPGroup r

theorem pairSubgroup_nilpotencyClass_le_two (d : Nat) (r : Root) : Group.nilpotencyClass (pairSubgroup d r) ≤ 2 :=
  (canonicalModel d).pairSubgroup_nilpotencyClass_le_two r

end ThomGame.PrimeFiveRankThreeCover
