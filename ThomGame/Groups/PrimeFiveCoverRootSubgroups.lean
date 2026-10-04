module

public import ThomGame.Groups.PrimeFiveRankThreeCover
public import ThomGame.Groups.FiniteCommutingClosure
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Finite abelian root subgroups of the actual prime-five cover

The results also apply to every model of the cover relations, including
noninjective images. Finiteness follows from the explicit commuting
generators of exponent five; it is not assumed as part of a model.
-/

@[expose] public section
namespace ThomGame.PrimeFiveRankThreeCover

open Compressor
open scoped IsMulCommutative

namespace Model

variable {d : Nat} {G : Type*} [Group G] (M : Model d G)

def rootSubgroup (r : Root) : Subgroup G := Subgroup.closure (Set.range (M.x r))

theorem x_mem_rootSubgroup (r : Root) (m : Coefficient d) : M.x r m ∈ M.rootSubgroup r :=
  Subgroup.subset_closure ⟨m, rfl⟩

theorem root_generators_commute (r : Root) (m n : Coefficient d) : Commute (M.x r m) (M.x r n) :=
  commutatorElement_eq_one_iff_commute.mp (M.e1 r r m n ⟨r.property, r.property⟩)

theorem root_range_commute (r : Root) : (Set.range (M.x r)).Pairwise Commute := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _
  exact M.root_generators_commute r m n

instance (r : Root) : IsMulCommutative (M.rootSubgroup r) :=
  Subgroup.isMulCommutative_closure (M.root_range_commute r)

theorem rootSubgroup_pow (r : Root) (x : M.rootSubgroup r) : x ^ 5 = 1 := by
  apply Subtype.ext
  exact commutingClosure_pow (M.root_range_commute r) 5
    (fun _ ⟨m, hm⟩ => hm ▸ M.e0 r m) x.val x.property

theorem rootSubgroup_finite (r : Root) : Finite (M.rootSubgroup r) :=
  commutingClosure_finite (Set.finite_range _) (M.root_range_commute r) 5 (by decide)
    (fun _ ⟨m, hm⟩ => hm ▸ M.e0 r m)

instance (r : Root) : Finite (M.rootSubgroup r) := M.rootSubgroup_finite r

end Model

abbrev rootSubgroup (d : Nat) (r : Root) : Subgroup (Cover d) := (canonicalModel d).rootSubgroup r

theorem of_mem_rootSubgroup (d : Nat) (r : Root) (m : Coefficient d) : of d r m ∈ rootSubgroup d r :=
  (canonicalModel d).x_mem_rootSubgroup r m

theorem rootSubgroup_pow (d : Nat) (r : Root) (x : rootSubgroup d r) : x ^ 5 = 1 :=
  (canonicalModel d).rootSubgroup_pow r x

theorem rootSubgroup_finite (d : Nat) (r : Root) : Finite (rootSubgroup d r) :=
  (canonicalModel d).rootSubgroup_finite r

end ThomGame.PrimeFiveRankThreeCover
