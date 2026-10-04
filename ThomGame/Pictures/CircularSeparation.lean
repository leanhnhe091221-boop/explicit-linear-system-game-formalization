module

public import ThomGame.Pictures.CircularPartition

/-!
# Separation of distinct boundary orbits by circular intervals

The explicit noninterlacing condition is equivalent to saying that an
orbit distinct from the endpoints' orbit cannot leave the circular
interval between two of those endpoints. This concerns points on the
ordered boundary, not a geometric Jordan curve in a constructed disk.
-/

@[expose] public section
namespace ThomGame.Pictures.CircularPartition

variable {A : Type*} [CircularOrder A]

theorem strict_order_dichotomy {a b c : A} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    sbtw a b c ∨ sbtw a c b := by
  by_cases h : sbtw a b c
  · exact Or.inl h
  · have hcba : btw c b a := btw_iff_not_sbtw.mpr h
    refine Or.inr (hcba.cyclic_right.sbtw_of_not_btw ?_)
    intro hbca
    rcases hcba.cyclic_right.antisymm hbca with he | he | he
    · exact hca he.symm
    · exact hbc he.symm
    · exact hab he.symm

namespace NonInterlacing

variable {f : Equiv.Perm A} (h : NonInterlacing (sbtw : A → A → A → Prop) f)

include h

/-- Every point of a distinct orbit lies on the same side of an endpoint
pair whenever one of its points does. -/
theorem arc_invariant {a b x y : A} (hab : f.SameCycle a b) (hax : ¬ f.SameCycle a x)
    (hxy : f.SameCycle x y) (haxb : sbtw a x b) : sbtw a y b := by
  have hay : ¬ f.SameCycle a y := fun hay => hax (hay.trans hxy.symm)
  have hab' : a ≠ b := by
    intro he
    subst b
    exact sbtw_irrefl_left_right haxb
  have hya : y ≠ a := by
    intro he
    subst y
    exact hay Equiv.Perm.SameCycle.rfl
  have hyb : y ≠ b := by
    intro he
    subst y
    exact hay hab
  rcases strict_order_dichotomy hya.symm hyb hab'.symm with ha | ha
  · exact ha
  · exact (hax (h a x b y haxb ha hab hxy)).elim

theorem arc_membership_iff {a b x y : A} (hab : f.SameCycle a b) (hax : ¬ f.SameCycle a x)
    (hxy : f.SameCycle x y) : sbtw a x b ↔ sbtw a y b := by
  constructor
  · exact h.arc_invariant hab hax hxy
  · exact h.arc_invariant hab (fun hay => hax (hay.trans hxy.symm)) hxy.symm

end NonInterlacing

theorem noninterlacing_iff_arc_invariant (f : Equiv.Perm A) :
    NonInterlacing (sbtw : A → A → A → Prop) f ↔
      ∀ a b x y, f.SameCycle a b → ¬ f.SameCycle a x → f.SameCycle x y →
        sbtw a x b → sbtw a y b := by
  constructor
  · intro h a b x y hab hax hxy hx
    exact h.arc_invariant hab hax hxy hx
  · intro h a b c d habc hacd hac hbd
    by_contra hab
    have hadc := h a c b d hac hab hbd habc
    exact hadc.not_sbtw hacd.cyclic_left

end ThomGame.Pictures.CircularPartition
