module

public import ThomGame.Finite.Hypergraph
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Incidence multisets and the natural-number matrix conditions

The local multiset equations for a generalized morphism imply exactly
the incidence sums in Slofstra Definition 8.4, including the even sum at
deleted vertices. Sparse-system incidence counts reduce modulo two to
the existing binary matrix, with no replacement of its entries.
-/

@[expose] public section
namespace ThomGame.Hypergraph

open scoped BigOperators

variable {E F V W : Type*}

theorem sum_count_weight [Fintype E] [DecidableEq E] (s : Multiset E) (w : E → Nat) :
    (∑ e, s.count e * w e) = (s.map w).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp [Multiset.count_cons, add_mul, ite_mul, Finset.sum_add_distrib, ih, Nat.add_comm]

theorem count_filterMap_sum [Fintype E] [DecidableEq E] [DecidableEq F]
    (s : Multiset E) (edge : E → Option F) (f : F) :
    (s.filterMap edge).count f = ∑ e, if edge e = some f then s.count e else 0 := by
  have hm : (s.filterMap edge).count f = (s.map (fun e => if edge e = some f then 1 else 0)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      cases he : edge a with
      | none =>
        rw [Multiset.filterMap_cons_none _ _ he, Multiset.map_cons, Multiset.sum_cons, ih]
        simp [he]
      | some b =>
        rw [Multiset.filterMap_cons_some _ _ _ he, Multiset.count_cons,
          Multiset.map_cons, Multiset.sum_cons, ih]
        simp [he, eq_comm, Nat.add_comm]
  rw [hm, ← sum_count_weight]
  simp only [mul_ite, mul_one, mul_zero]

theorem card_filterMap_sum [Fintype E] [DecidableEq E]
    (s : Multiset E) (edge : E → Option F) :
    (s.filterMap edge).card = ∑ e, if (edge e).isSome then s.count e else 0 := by
  have hm : (s.filterMap edge).card = (s.map (fun e => if (edge e).isSome then 1 else 0)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      cases he : edge a with
      | none =>
        rw [Multiset.filterMap_cons_none _ _ he, Multiset.map_cons, Multiset.sum_cons, ih]
        simp [he]
      | some b =>
        rw [Multiset.filterMap_cons_some _ _ _ he, Multiset.card_cons,
          Multiset.map_cons, Multiset.sum_cons, ih]
        simp [he, Nat.add_comm]
  rw [hm, ← sum_count_weight]
  simp only [mul_ite, mul_one, mul_zero]

theorem GeneralizedHom.retained_matrix [Fintype E] [DecidableEq E] [DecidableEq F]
    {H : Hypergraph V E} {K : Hypergraph W F} (φ : GeneralizedHom H K)
    {v : V} {w : W} (hv : φ.vertex v = some w) (f : F) :
    (∑ e, if φ.edge e = some f then H.multiplicity v e else 0) = K.multiplicity w f := by
  unfold multiplicity
  rw [← count_filterMap_sum (H.incidence v) φ.edge f, φ.retained v w hv]

theorem GeneralizedHom.deleted_matrix_even [Fintype E] [DecidableEq E]
    {H : Hypergraph V E} {K : Hypergraph W F} (φ : GeneralizedHom H K)
    {v : V} (hv : φ.vertex v = none) :
    Even (∑ e, if (φ.edge e).isSome then H.multiplicity v e else 0) := by
  unfold multiplicity
  rw [← card_filterMap_sum (H.incidence v) φ.edge]
  exact (φ.deleted v hv).1

theorem GeneralizedHom.deleted_edge_images {H : Hypergraph V E} {K : Hypergraph W F}
    (φ : GeneralizedHom H K) {v : V} (hv : φ.vertex v = none)
    {a b : E} {f g : F} (ha : a ∈ H.incidence v) (hb : b ∈ H.incidence v)
    (hf : φ.edge a = some f) (hg : φ.edge b = some g) : f = g :=
  (φ.deleted v hv).2 f ((Multiset.mem_filterMap _ _).mpr ⟨a, ha, hf⟩)
    g ((Multiset.mem_filterMap _ _).mpr ⟨b, hb, hg⟩)

end ThomGame.Hypergraph

namespace ThomGame.SparseSystem

theorem hypergraph_incidence_nodup {R C : Type*} (S : SparseSystem R C) (r : R) :
    (S.hypergraph.incidence r).Nodup := by
  simp [hypergraph, (S.column_injective r).eq_iff]

theorem hypergraph_multiplicity_eq_ite {R C : Type*} [DecidableEq C]
    (S : SparseSystem R C) (r : R) (c : C) :
    S.hypergraph.multiplicity r c = if c ∈ S.hypergraph.incidence r then 1 else 0 :=
  Multiset.count_eq_of_nodup (S.hypergraph_incidence_nodup r)

theorem hypergraph_matrix {R C : Type*} [DecidableEq C] (S : SparseSystem R C) (r : R) (c : C) :
    (S.hypergraph.multiplicity r c : ZMod 2) = S.matrix r c := by
  unfold matrix
  change ((S.column r 0 ::ₘ S.column r 1 ::ₘ S.column r 2 ::ₘ (0 : Multiset C)).count c : ZMod 2) = _
  simp only [Multiset.count_cons, Multiset.count_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [eq_comm, add_comm, add_left_comm]
  exact add_left_comm _ _ _

end ThomGame.SparseSystem
