module

public import ThomGame.Analysis.MatrixNormalTrace
public import ThomGame.Analysis.MatrixInternalFiniteAlgebra

/-!
# Directed completeness and normal traces of internal subalgebras

The ambient positive supremum remains internal by weak closedness.
Thus the internal inclusion preserves positive directed suprema, and
the restricted faithful trace is normal for the actual inherited order.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology ComplexOrder

variable (dims : Nat → Nat) (S : (n : Nat) → StarSubalgebra ℂ (CMatrix (dims n)))
  (hd : ∀ n, 0 < dims n) (U : Ultrafilter Nat)

theorem matrixInternalFiniteTrace_monotone : Monotone (matrixInternalFiniteTrace dims S hd U) :=
  fun _ _ h => matrixFiniteTrace_monotone dims hd U h

variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

theorem exists_matrixInternalFinite_positive_sup (hU : (U : Filter Nat) ≤ atTop)
    (f : κ → matrixInternalFiniteAlgebra dims S hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i) (hbound : BddAbove (Set.range f)) :
    ∃ T : matrixInternalFiniteAlgebra dims S hd U, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      IsLUB (Set.range (fun i => (f i).val)) T.val ∧
      (∀ x, Tendsto (fun i => (f i).val.val x) atTop (𝓝 (T.val.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val.val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val.val)) := by
  obtain ⟨B, hB⟩ := hbound
  have hb : BddAbove (Set.range (fun i => (f i).val)) := by
    refine ⟨B.val, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hB (Set.mem_range_self i)
  obtain ⟨T, hp, hsup, hs, hw⟩ := exists_matrixFinite_positive_sup dims hd U
    (fun i => (f i).val) (fun _ _ h => hmono h) hpos hb
  have hwmem : ContinuousLinearMapWOT.ofCLM T.val ∈ matrixInternalWOTAlgebra dims S hd U :=
    (matrixInternalWOTAlgebra_isClosed dims S hd U hU).mem_of_tendsto hw
      (Eventually.of_forall fun i => (mem_matrixInternalFiniteAlgebra dims S hd U (f i).val).mp (f i).property)
  have hT : T ∈ matrixInternalFiniteAlgebra dims S hd U :=
    (mem_matrixInternalFiniteAlgebra dims S hd U T).mpr hwmem
  refine ⟨⟨T, hT⟩, hp, ?_, hsup, hs, hw⟩
  constructor
  · rintro _ ⟨i, rfl⟩
    exact hsup.1 (Set.mem_range_self i)
  · intro C hC
    apply hsup.2
    rintro _ ⟨i, rfl⟩
    exact hC (Set.mem_range_self i)

theorem matrixInternalFinite_positive_tendsto_sup (hU : (U : Filter Nat) ≤ atTop)
    (f : κ → matrixInternalFiniteAlgebra dims S hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : matrixInternalFiniteAlgebra dims S hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => (f i).val)) T.val ∧
      (∀ x, Tendsto (fun i => (f i).val.val x) atTop (𝓝 (T.val.val x))) ∧
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).val.val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T.val.val)) := by
  obtain ⟨B, _, hB, hfull, hs, hw⟩ := exists_matrixInternalFinite_positive_sup dims S hd U hU f hmono hpos ⟨T, hT.1⟩
  exact hB.unique hT ▸ ⟨hfull, hs, hw⟩

theorem matrixInternalFiniteTrace_preserves_positive_sup (hU : (U : Filter Nat) ≤ atTop)
    (f : κ → matrixInternalFiniteAlgebra dims S hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : matrixInternalFiniteAlgebra dims S hd U) (hT : IsLUB (Set.range f) T) :
    IsLUB (Set.range (fun i => matrixInternalFiniteTrace dims S hd U (f i)))
      (matrixInternalFiniteTrace dims S hd U T) := by
  apply matrixFiniteTrace_preserves_positive_sup dims hd U (fun i => (f i).val)
    (fun _ _ h => hmono h) hpos T.val
  exact (matrixInternalFinite_positive_tendsto_sup dims S hd U hU f hmono hpos T hT).1

theorem matrixInternalFiniteTrace_re_sup_eq_ciSup (hU : (U : Filter Nat) ≤ atTop)
    (f : κ → matrixInternalFiniteAlgebra dims S hd U)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (T : matrixInternalFiniteAlgebra dims S hd U) (hT : IsLUB (Set.range f) T) :
    (matrixInternalFiniteTrace dims S hd U T).re = ⨆ i, (matrixInternalFiniteTrace dims S hd U (f i)).re :=
  matrixFiniteRealTrace_sup_eq_ciSup dims hd U (fun i => (f i).val) (fun _ _ h => hmono h) hpos T.val
    (matrixInternalFinite_positive_tendsto_sup dims S hd U hU f hmono hpos T hT).1

theorem exists_matrixInternalFinite_directed_positive_sup (hU : (U : Filter Nat) ≤ atTop)
    (s : Set (matrixInternalFiniteAlgebra dims S hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a) (hbound : BddAbove s) :
    ∃ T : matrixInternalFiniteAlgebra dims S hd U, IsLUB s T := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  obtain ⟨T, _, hT, _, _, _⟩ := exists_matrixInternalFinite_positive_sup dims S hd U hU
    (fun a : s => a.val) (fun _ _ h => h) (fun a => hpos a.val a.property) (hr.symm ▸ hbound)
  exact ⟨T, hr ▸ hT⟩

theorem exists_matrixInternalFinite_directed_sup (hU : (U : Filter Nat) ≤ atTop)
    (s : Set (matrixInternalFiniteAlgebra dims S hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hbound : BddAbove s) :
    ∃ T : matrixInternalFiniteAlgebra dims S hd U, IsLUB s T :=
  exists_directed_sup_of_positive_sup
    (exists_matrixInternalFinite_directed_positive_sup dims S hd U hU) s hs hdir hbound

theorem matrixInternalFiniteTrace_normal (hU : (U : Filter Nat) ≤ atTop)
    (s : Set (matrixInternalFiniteAlgebra dims S hd U))
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a)
    (T : matrixInternalFiniteAlgebra dims S hd U) (hT : IsLUB s T) :
    IsLUB (matrixInternalFiniteTrace dims S hd U '' s) (matrixInternalFiniteTrace dims S hd U T) := by
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.property b.val b.property
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  have hr : Set.range (fun a : s => a.val) = s := Subtype.range_coe
  have ht := matrixInternalFiniteTrace_preserves_positive_sup dims S hd U hU (fun a : s => a.val)
    (fun _ _ h => h) (fun a => hpos a.val a.property) T (hr.symm ▸ hT)
  have he : Set.range (fun a : s => matrixInternalFiniteTrace dims S hd U a.val) =
      matrixInternalFiniteTrace dims S hd U '' s := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  exact he ▸ ht

end ThomGame.Analysis
