module

public import ThomGame.Finite.SparseSystem
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.FinRange

/-! Row slot permutations, and the unique increasing ordering of each support. -/

@[expose] public section
namespace ThomGame.SparseSystem

variable {R C : Type*}

/-- The second system differs only in the order of the three slots in each row. -/
structure RowPermutation (S T : SparseSystem R C) where
  slots : R → Equiv.Perm (Fin 3)
  column_eq : ∀ r i, T.column r i = S.column r (slots r i)
  rhs_eq : T.rhs = S.rhs

namespace RowPermutation

variable {S T : SparseSystem R C} (p : RowPermutation S T)

def symm : RowPermutation T S where
  slots r := (p.slots r).symm
  column_eq r i := by rw [p.column_eq, Equiv.apply_symm_apply]
  rhs_eq := p.rhs_eq.symm

include p

theorem columns_perm (r : R) :
    [T.column r 0, T.column r 1, T.column r 2].Perm
      [S.column r 0, S.column r 1, S.column r 2] := by
  have h := (p.slots r).ofFn_comp_perm (S.column r)
  simpa [List.ofFn_succ, Function.comp_def, ← p.column_eq] using h

theorem matrix_eq [DecidableEq C] : T.matrix = S.matrix := by
  funext r c
  simp only [SparseSystem.matrix, p.column_eq]
  exact Equiv.sum_comp (p.slots r) (fun i => if S.column r i = c then (1 : ZMod 2) else 0)

theorem satisfies_iff (x : C → ZMod 2) : T.Satisfies x ↔ S.Satisfies x := by
  have he (r : R) : (∑ i, x (T.column r i)) = ∑ i, x (S.column r i) := by
    simp only [p.column_eq]
    exact Equiv.sum_comp (p.slots r) (fun i => x (S.column r i))
  simp only [Satisfies, he, p.rhs_eq]

end RowPermutation

variable [LinearOrder C] (S : SparseSystem R C)

def rowSupport (r : R) : Finset C := Finset.univ.image (S.column r)

theorem mem_rowSupport (r : R) (c : C) : c ∈ S.rowSupport r ↔ ∃ i, S.column r i = c := by
  simp [rowSupport]

theorem rowSupport_card (r : R) : (S.rowSupport r).card = 3 := by
  rw [rowSupport, Finset.card_image_of_injective _ (S.column_injective r)]
  simp

noncomputable def supportEquiv (r : R) : Fin 3 ≃ S.rowSupport r :=
  Equiv.ofBijective (fun i => ⟨S.column r i, (S.mem_rowSupport r _).mpr ⟨i, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact S.column_injective r (congrArg Subtype.val h)
    · rintro ⟨c, hc⟩
      obtain ⟨i, hi⟩ := (S.mem_rowSupport r c).mp hc
      exact ⟨i, Subtype.ext hi⟩)

/-- This is the increasing enumeration of the actual support, with the same rhs. -/
def ordered : SparseSystem R C where
  column r := (S.rowSupport r).orderEmbOfFin (S.rowSupport_card r)
  column_injective r := ((S.rowSupport r).orderEmbOfFin (S.rowSupport_card r)).injective
  rhs := S.rhs

noncomputable def orderedPermutation : RowPermutation S S.ordered where
  slots r := ((S.rowSupport r).orderIsoOfFin (S.rowSupport_card r)).toEquiv.trans
    (S.supportEquiv r).symm
  column_eq r i := by
    change ((S.rowSupport r).orderIsoOfFin (S.rowSupport_card r) i).val =
      ((S.supportEquiv r) ((S.supportEquiv r).symm
        ((S.rowSupport r).orderIsoOfFin (S.rowSupport_card r) i))).val
    rw [Equiv.apply_symm_apply]
  rhs_eq := rfl

theorem ordered_strictMono (r : R) : StrictMono (S.ordered.column r) :=
  ((S.rowSupport r).orderEmbOfFin (S.rowSupport_card r)).strictMono

theorem ordered_matrix : S.ordered.matrix = S.matrix := S.orderedPermutation.matrix_eq

theorem ordered_rhs : S.ordered.rhs = S.rhs := rfl

theorem ordered_column_mem (r : R) (i : Fin 3) : S.ordered.column r i ∈ S.rowSupport r :=
  Finset.orderEmbOfFin_mem _ _ _

/-- An increasing triple with precisely these matrix columns is forced to be this one. -/
theorem ordered_column_unique (r : R) (v : Fin 3 → C)
    (hv : StrictMono v) (hs : ∀ i, S.matrix r (v i) = 1) : v = S.ordered.column r := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact (S.mem_rowSupport r _).mpr ((S.matrix_eq_one_iff r _).mp (hs i))
  · exact hv

end ThomGame.SparseSystem
