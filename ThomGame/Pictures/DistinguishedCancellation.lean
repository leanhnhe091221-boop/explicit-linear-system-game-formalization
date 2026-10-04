module

public import ThomGame.Pictures.DistinguishedRelation

/-! # Puncturing the boundary block after deleting two ordinary relations -/

@[expose] public section
namespace ThomGame.Pictures.Diagram

open scoped Classical

variable {R S : Type*} {P : InvolutionPresentation R S} {w : List S} {p : ZMod 2}

theorem exists_punctured_after_cancel (d : Diagram (P.adjoinRelation w p) [] [])
    (m : Multiset R) (r : R)
    (h : (d.labels : Multiset (Option R)) + [some r, some r] = {none} + m.map some) :
    ∃ e : Diagram P w [], (e.labels : Multiset R) + [r, r] = m := by
  classical
  have hn : d.labels.count none = 1 := by
    obtain ⟨rs, hrs⟩ := Quotient.exists_rep m
    rw [← hrs] at h
    have hp : (d.labels ++ [some r, some r]).Perm (none :: rs.map some) :=
      Multiset.coe_eq_coe.mp h
    have hc := hp.count_eq none
    have hc0 : (rs.map some).count (none : Option R) = 0 := List.count_eq_zero.mpr (by simp)
    simpa [hc0] using hc
  obtain ⟨e, he⟩ := d.exists_punctured_diagram hn
  refine ⟨e, ?_⟩
  rw [Multiset.coe_eq_coe.mpr he]
  have hm : (m.map some).filterMap id = m := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep m
    simp
  have hf := congrArg (Multiset.filterMap id) h
  simpa [hm] using hf

end ThomGame.Pictures.Diagram
