module

public import ThomGame.Analysis.MonotoneOperatorConvergence
public import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Directed suprema in weak operator closed subalgebras

A nonempty directed increasing positive family with an order upper bound
has a supremum in the given weakly closed subalgebra. It converges to
that supremum strongly and in the weak operator topology.
Translating a cofinal tail by one of its elements then gives suprema
for every nonempty directed set with an order upper bound.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

theorem exists_directed_sup_of_positive_sup {G : Type*}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (hpositive : ∀ t : Set G, t.Nonempty → DirectedOn (· ≤ ·) t →
      (∀ b ∈ t, 0 ≤ b) → BddAbove t → ∃ T : G, IsLUB t T)
    (s : Set G) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hb : BddAbove s) : ∃ T : G, IsLUB s T := by
  obtain ⟨a₀, ha₀⟩ := hs
  let t : Set G := {b | ∃ a ∈ s, a₀ ≤ a ∧ a - a₀ = b}
  have ht : t.Nonempty := ⟨a₀ - a₀, a₀, ha₀, le_rfl, rfl⟩
  have htd : DirectedOn (· ≤ ·) t := by
    rintro b ⟨a, ha, h₀a, rfl⟩ c ⟨d, hd', _, rfl⟩
    obtain ⟨e, he, hae, hde⟩ := hd a ha d hd'
    exact ⟨e - a₀, ⟨e, he, h₀a.trans hae, rfl⟩, sub_le_sub_right hae a₀, sub_le_sub_right hde a₀⟩
  have htp : ∀ b ∈ t, 0 ≤ b := by
    rintro b ⟨a, _, h₀a, rfl⟩
    exact sub_nonneg.mpr h₀a
  obtain ⟨B, hB⟩ := hb
  have htb : BddAbove t := by
    refine ⟨B - a₀, ?_⟩
    rintro b ⟨a, ha, _, rfl⟩
    exact sub_le_sub_right (hB ha) a₀
  obtain ⟨T, hT⟩ := hpositive t ht htd htp htb
  refine ⟨T + a₀, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, hc, hac, h₀c⟩ := hd a ha a₀ ha₀
    have hct : c - a₀ ≤ T := hT.1 ⟨c, hc, h₀c, rfl⟩
    exact hac.trans (sub_le_iff_le_add.mp hct)
  · intro C hC
    apply le_sub_iff_add_le.mp
    apply hT.2
    rintro b ⟨a, ha, _, rfl⟩
    exact sub_le_sub_right (hC ha) a₀

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : StarSubalgebra ℂ (H →L[ℂ] H))
  (hclosed : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ A})
variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

include hclosed

theorem exists_positive_sup_in_wot_closed_subalgebra (f : κ → A)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i) (hbound : BddAbove (Set.range f)) :
    ∃ T : A, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      (∀ x, Tendsto (fun i => (f i).val x) atTop (𝓝 (T.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val)) := by
  obtain ⟨B, hB⟩ := hbound
  have hnorm : ∀ i, ‖(f i).val‖ ≤ ‖B.val‖ := fun i =>
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (hB (Set.mem_range_self i)) (hpos i)
  obtain ⟨T, hTpos, _, hTsup, hs, hw⟩ := exists_monotone_positive_operator_limit
    (fun i => (f i).val) (fun _ _ hij => hmono hij) hpos ‖B.val‖ (norm_nonneg _) hnorm
  have hTmem : T ∈ A := hclosed.mem_of_tendsto hw (Eventually.of_forall fun i => (f i).property)
  refine ⟨⟨T, hTmem⟩, hTpos, ?_, hs, hw⟩
  constructor
  · rintro _ ⟨i, rfl⟩
    exact hTsup.1 (Set.mem_range_self i)
  · intro C hC
    apply hTsup.2
    rintro _ ⟨i, rfl⟩
    exact hC (Set.mem_range_self i)

theorem positive_family_tendsto_sup_in_wot_closed_subalgebra (f : κ → A)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i) (T : A) (hT : IsLUB (Set.range f) T) :
    (∀ x, Tendsto (fun i => (f i).val x) atTop (𝓝 (T.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val)) := by
  obtain ⟨B, _, hB, hs, hw⟩ := exists_positive_sup_in_wot_closed_subalgebra A hclosed f hmono hpos ⟨T, hT.1⟩
  have he : B = T := hB.unique hT
  exact he ▸ ⟨hs, hw⟩

theorem exists_directed_positive_sup_in_wot_closed_subalgebra
    (s : Set A) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hp : ∀ a ∈ s, 0 ≤ a) (hb : BddAbove s) : ∃ T : A, IsLUB s T := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hd a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  obtain ⟨T, _, hT, _, _⟩ := exists_positive_sup_in_wot_closed_subalgebra A hclosed
    (fun a : s => a.val) (fun _ _ h => h) (fun a => hp a.val a.property) (hr.symm ▸ hb)
  exact ⟨T, hr ▸ hT⟩

theorem exists_directed_sup_in_wot_closed_subalgebra
    (s : Set A) (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    (hb : BddAbove s) : ∃ T : A, IsLUB s T :=
  exists_directed_sup_of_positive_sup
    (exists_directed_positive_sup_in_wot_closed_subalgebra A hclosed) s hs hd hb

end ThomGame.Analysis
