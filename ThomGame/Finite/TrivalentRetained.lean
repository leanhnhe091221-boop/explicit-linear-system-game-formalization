module

public import ThomGame.Finite.TrivalentEmbedding

/-!
# Retained trivalent rows have a bijection of all three slots

A generalized map can identify labels globally. At a retained trivalent
row, however, all three incidences survive and are mapped bijectively to
the three distinct target incidences. No global injectivity is assumed.
-/

@[expose] public section
namespace ThomGame

namespace Hypergraph.GeneralizedHom

variable {R S T U : Type*} {A : SparseSystem R S} {B : SparseSystem T U}
  (φ : A.hypergraph.GeneralizedHom B.hypergraph) {r : R} {s : T}

theorem retained_incident_image (hr : φ.vertex r = some s) {e : S}
    (he : e ∈ A.hypergraph.incidence r) : ∃ f, φ.edge e = some f := by
  let l := [A.column r 0, A.column r 1, A.column r 2]
  have hl : (l.filterMap φ.edge).length = l.length := by
    have hc := congrArg Multiset.card (φ.retained r s hr)
    simpa only [l, SparseSystem.hypergraph, Multiset.filterMap_coe, Multiset.coe_card,
      List.length_cons, List.length_nil] using hc
  cases hx : φ.edge e with
  | some f => exact ⟨f, rfl⟩
  | none =>
    have hm : e ∈ l := he
    have hlt := List.length_filterMap_lt_length_iff_exists.mpr ⟨e, hm, hx⟩
    exact (Nat.ne_of_lt hlt hl).elim

theorem retained_map_incidence (hr : φ.vertex r = some s) (fallback : U) :
    (A.hypergraph.incidence r).map (fun e => (φ.edge e).getD fallback) = B.hypergraph.incidence s := by
  let l := [A.column r 0, A.column r 1, A.column r 2]
  have hl : l.filterMap φ.edge = l.map (fun e => (φ.edge e).getD fallback) := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro e he
    obtain ⟨f, hf⟩ := φ.retained_incident_image hr (show e ∈ A.hypergraph.incidence r from he)
    simp only [hf, Option.getD_some]
  have h := φ.retained r s hr
  change (l.filterMap φ.edge : Multiset U) = _ at h
  rw [hl] at h
  exact h

end Hypergraph.GeneralizedHom

namespace SparseSystem

variable {R S T U : Type*} (A : SparseSystem R S) (B : SparseSystem T U)
  (f : S → U) (r : R) (s : T)
  (h : (A.hypergraph.incidence r).map f = B.hypergraph.incidence s)

include h in
theorem exists_mapped_column_slot (i : Fin 3) : ∃ j : Fin 3, B.column s j = f (A.column r i) := by
  apply (B.mem_hypergraph_incidence _ _).mp
  rw [← h]
  exact Multiset.mem_map.mpr ⟨A.column r i, (A.mem_hypergraph_incidence r _).mpr ⟨i, rfl⟩, rfl⟩

noncomputable def mappedColumnSlot (i : Fin 3) : Fin 3 :=
  Classical.choose (A.exists_mapped_column_slot B f r s h i)

theorem mappedColumnSlot_label (i : Fin 3) :
    B.column s (A.mappedColumnSlot B f r s h i) = f (A.column r i) :=
  Classical.choose_spec (A.exists_mapped_column_slot B f r s h i)

theorem mappedColumnSlot_surjective : Function.Surjective (A.mappedColumnSlot B f r s h) := by
  intro j
  have hj : B.column s j ∈ (A.hypergraph.incidence r).map f := by
    rw [h]
    exact (B.mem_hypergraph_incidence s _).mpr ⟨j, rfl⟩
  obtain ⟨e, he, hf⟩ := Multiset.mem_map.mp hj
  obtain ⟨i, rfl⟩ := (A.mem_hypergraph_incidence r e).mp he
  exact ⟨i, B.column_injective s ((A.mappedColumnSlot_label B f r s h i).trans hf)⟩

noncomputable def mappedSlotEquiv : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (A.mappedColumnSlot B f r s h)
    ⟨(Finite.injective_iff_surjective).mpr (A.mappedColumnSlot_surjective B f r s h),
      A.mappedColumnSlot_surjective B f r s h⟩

theorem mappedSlotEquiv_label (i : Fin 3) :
    B.column s (A.mappedSlotEquiv B f r s h i) = f (A.column r i) :=
  A.mappedColumnSlot_label B f r s h i

theorem mappedSlotEquiv_turn (b : Bool) (i : Fin 3) :
    triangleTurn (b ^^ triangleFlip (A.mappedSlotEquiv B f r s h)) (A.mappedSlotEquiv B f r s h i) =
      A.mappedSlotEquiv B f r s h (triangleTurn b i) := triangleFlip_turn _ b i

end SparseSystem
end ThomGame
