module

public import ThomGame.Analysis.UnitarySequenceQuotient

/-!
# Dimension-varying countersequences and exact quotient representations

Failure of the uniform approximation statement produces actual matrix
assignments with tolerance 1/(n+1) and a fixed positive lower bound for
the selected word. Along any nontrivial filter finer than atTop, this
sequence yields an exact presented-group representation that detects
the word in the unitary sequence quotient.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {S : Type*} (rels : Set (FreeGroup S)) (v : FreeGroup S)

structure ApproximationCountersequence where
  separation : ℝ
  separation_pos : 0 < separation
  dims : Nat → Nat
  dims_pos : ∀ n, 0 < dims n
  assignment : (n : Nat) → MatrixAssignment S (dims n)
  approximate : ∀ n : Nat, IsApproxRepresentation rels (1 / ((n : ℝ) + 1)) (assignment n)
  separated : ∀ n, separation ≤ unitaryLength (assignment n v)

theorem exists_approximationCountersequence (h : ¬ ApproximatelyTrivial rels v) :
    Nonempty (ApproximationCountersequence rels v) := by
  classical
  unfold ApproximatelyTrivial at h
  push Not at h
  obtain ⟨η, hη, hh⟩ := h
  have hc (n : Nat) : ∃ d : Nat, 0 < d ∧ ∃ f : MatrixAssignment S d,
      IsApproxRepresentation rels (1 / ((n : ℝ) + 1)) f ∧ η ≤ unitaryLength (f v) :=
    hh _ (by positivity)
  choose dims hdim f hf hfar using hc
  exact ⟨⟨η, hη, dims, hdim, f, hf, hfar⟩⟩

namespace ApproximationCountersequence

variable {rels v} (C : ApproximationCountersequence rels v)

theorem relation_tendsto (r : FreeGroup S) (hr : r ∈ rels) :
    Tendsto (fun n => unitaryLength (C.assignment n r)) atTop (𝓝 0) :=
  squeeze_zero (fun _n => unitaryLength_nonneg _) (fun n => C.approximate n r hr)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem detects_in_quotient (L : Filter Nat) [L.NeBot] (hL : L ≤ atTop) :
    ∃ φ : PresentedGroup rels →* UnitarySequenceQuotient C.dims L,
      φ (PresentedGroup.mk rels v) ≠ 1 := by
  have hr (r : FreeGroup S) (h : r ∈ rels) :
      Tendsto (fun n => unitaryLength (C.assignment n r)) L (𝓝 0) :=
    (C.relation_tendsto r h).mono_left hL
  refine ⟨sequenceRepresentation C.dims L rels C.assignment hr, ?_⟩
  rw [sequenceRepresentation_mk]
  exact unitarySequenceMk_ne_one_of_lower_bound C.dims L _ C.separation_pos
    (Eventually.of_forall C.separated)

end ApproximationCountersequence

theorem approximatelyTrivial_of_quotient_killed (L : Filter Nat) [L.NeBot] (hL : L ≤ atTop)
    (hk : ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
      ∀ φ : PresentedGroup rels →* UnitarySequenceQuotient dims L,
        φ (PresentedGroup.mk rels v) = 1) : ApproximatelyTrivial rels v := by
  by_contra h
  obtain ⟨C⟩ := exists_approximationCountersequence rels v h
  obtain ⟨φ, hφ⟩ := C.detects_in_quotient L hL
  exact hφ (hk C.dims C.dims_pos φ)

theorem approximatelyTrivial_tendsto {ι : Type*} (dims : ι → Nat) (hd : ∀ i, 0 < dims i)
    (L : Filter ι) (hfinite : rels.Finite) (h : ApproximatelyTrivial rels v)
    (f : (i : ι) → MatrixAssignment S (dims i))
    (hr : ∀ r ∈ rels, Tendsto (fun i => unitaryLength (f i r)) L (𝓝 0)) :
    Tendsto (fun i => unitaryLength (f i v)) L (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (unitaryLength_nonneg _)
  · intro η hη
    obtain ⟨δ, hδ, hbound⟩ := h η hη
    have he : ∀ᶠ i in L, IsApproxRepresentation rels δ (f i) :=
      hfinite.eventually_all.mpr (fun r hh =>
        ((hr r hh).eventually (gt_mem_nhds hδ)).mono (fun i hi => hi.le))
    exact he.mono fun i hi => hbound (dims i) (hd i) (f i) hi

end ThomGame.Analysis
