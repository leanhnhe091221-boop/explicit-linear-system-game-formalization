module

public import ThomGame.Groups.PrimeFiveCoverRootSubgroups
public import ThomGame.Groups.CentralCommutatorGenerators

/-!
# The actual generators of each adjacent root pair

Relations (E1) and (E4) imply that every commutator of two pair
generators commutes with every pair generator. The subgroup and its
generating family are explicit, so this condition can be passed to the
general central-commutator theorem without any presentation assumption.
-/

@[expose] public section
namespace ThomGame.PrimeFiveRankThreeCover.Model

open Compressor
open scoped commutatorElement

variable {d : Nat} {G : Type*} [Group G] (M : Model d G)

def pairGenerator (r : Root) (a : Bool × Coefficient d) : G :=
  if a.1 then M.x r a.2 else M.x (right r) a.2

def pairSubgroup (r : Root) : Subgroup G := Subgroup.closure (Set.range (M.pairGenerator r))

def pairOf (r : Root) (a : Bool × Coefficient d) : M.pairSubgroup r :=
  ⟨M.pairGenerator r a, Subgroup.subset_closure ⟨a, rfl⟩⟩

theorem pairGenerator_range (r : Root) :
    Set.range (M.pairGenerator r) = Set.range (M.x r) ∪ Set.range (M.x (right r)) := by
  ext x
  constructor
  · rintro ⟨⟨a, m⟩, rfl⟩
    cases a
    · exact Or.inr ⟨m, rfl⟩
    · exact Or.inl ⟨m, rfl⟩
  · rintro (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact ⟨(true, m), rfl⟩
    · exact ⟨(false, m), rfl⟩

theorem pairSubgroup_eq_sup (r : Root) :
    M.pairSubgroup r = M.rootSubgroup r ⊔ M.rootSubgroup (right r) := by
  rw [pairSubgroup, M.pairGenerator_range, Subgroup.closure_union]
  rfl

theorem pairOf_generates (r : Root) : Subgroup.closure (Set.range (M.pairOf r)) = ⊤ := by
  apply Subgroup.map_injective (M.pairSubgroup r).subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem cross_commutes_left (r : Root) (m n l : Coefficient d) :
    Commute ⁅M.x r m, M.x (right r) n⁆ (M.x r l) :=
  commutatorElement_eq_one_iff_commute.mp
    (M.e4 r r m n l ⟨r.property, (third_ne_source r).symm⟩)

theorem cross_commutes_right (r : Root) (m n l : Coefficient d) :
    Commute ⁅M.x r m, M.x (right r) n⁆ (M.x (right r) l) :=
  commutatorElement_eq_one_iff_commute.mp
    (M.e4 r (right r) m n l ⟨(third_ne_source r).symm, (third_ne_target r).symm⟩)

theorem pairGenerator_triple (r : Root) (a b c : Bool × Coefficient d) :
    Commute ⁅M.pairGenerator r a, M.pairGenerator r b⁆ (M.pairGenerator r c) := by
  rcases a with ⟨a, m⟩
  rcases b with ⟨b, n⟩
  rcases c with ⟨c, l⟩
  cases a <;> cases b
  · change Commute ⁅M.x (right r) m, M.x (right r) n⁆ _
    rw [(M.root_generators_commute (right r) m n).commutator_eq]
    exact Commute.one_left _
  · change Commute ⁅M.x (right r) m, M.x r n⁆ _
    rw [← commutatorElement_inv]
    cases c
    · exact (M.cross_commutes_right r n m l).inv_left
    · exact (M.cross_commutes_left r n m l).inv_left
  · change Commute ⁅M.x r m, M.x (right r) n⁆ _
    cases c
    · exact M.cross_commutes_right r m n l
    · exact M.cross_commutes_left r m n l
  · change Commute ⁅M.x r m, M.x r n⁆ _
    rw [(M.root_generators_commute r m n).commutator_eq]
    exact Commute.one_left _

theorem pairOf_triple (r : Root) (a b c : Bool × Coefficient d) :
    Commute ⁅M.pairOf r a, M.pairOf r b⁆ (M.pairOf r c) := by
  apply Subtype.ext
  exact M.pairGenerator_triple r a b c

theorem pairOf_pow (r : Root) (a : Bool × Coefficient d) : M.pairOf r a ^ 5 = 1 := by
  apply Subtype.ext
  rcases a with ⟨a, m⟩
  cases a
  · exact M.e0 (right r) m
  · exact M.e0 r m

theorem pairSubgroup_commutator_le_center (r : Root) :
    _root_.commutator (M.pairSubgroup r) ≤ Subgroup.center (M.pairSubgroup r) := by
  apply commutator_le_center_of_generators (M.pairOf_generates r)
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
  exact M.pairOf_triple r a b c

theorem pairSubgroup_finite (r : Root) : Finite (M.pairSubgroup r) := by
  refine finite_of_central_commutator_generators (Set.finite_range (M.pairOf r))
    (M.pairOf_generates r) ?_ 5 (by decide) ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    exact M.pairOf_triple r a b c
  · rintro _ ⟨a, rfl⟩
    exact M.pairOf_pow r a

instance (r : Root) : Finite (M.pairSubgroup r) := M.pairSubgroup_finite r

end ThomGame.PrimeFiveRankThreeCover.Model
