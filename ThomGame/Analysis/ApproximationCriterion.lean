module

public import ThomGame.Analysis.ApproximationLimits
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# The approximation criterion for the concrete unitary sequence quotient

Every homomorphism into this quotient admits unitary sequence lifts of
its generators by its construction. For finitely many relators, uniform
approximate triviality therefore implies triviality in every such exact
quotient representation. The converse follows from the dimension-varying
countersequence. No tracial von Neumann algebra identification is assumed.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {S ι : Type*} (rels : Set (FreeGroup S)) (dims : ι → Nat) (L : Filter ι)

theorem quotientRepresentation_lift (φ : PresentedGroup rels →* UnitarySequenceQuotient dims L) :
    ∃ f : (i : ι) → MatrixAssignment S (dims i),
      quotientAssignment dims L f = φ.comp (PresentedGroup.mk rels) := by
  classical
  have hs (s : S) : ∃ U : UnitarySequence dims,
      unitarySequenceMk dims L U = φ (PresentedGroup.of s) :=
    QuotientGroup.mk_surjective _
  choose U hU using hs
  let f (i : ι) : MatrixAssignment S (dims i) := FreeGroup.lift (fun s => U s i)
  refine ⟨f, ?_⟩
  apply FreeGroup.ext_hom
  intro s
  change unitarySequenceMk dims L (fun i => f i (FreeGroup.of s)) = φ (PresentedGroup.of s)
  simpa only [f, FreeGroup.lift_apply_of] using hU s

theorem approximatelyTrivial_quotient_killed (v : FreeGroup S) (hfinite : rels.Finite)
    (hd : ∀ i, 0 < dims i) (h : ApproximatelyTrivial rels v)
    (φ : PresentedGroup rels →* UnitarySequenceQuotient dims L) :
    φ (PresentedGroup.mk rels v) = 1 := by
  obtain ⟨f, hf⟩ := quotientRepresentation_lift rels dims L φ
  have hr (r : FreeGroup S) (hr : r ∈ rels) :
      Tendsto (fun i => unitaryLength (f i r)) L (𝓝 0) := by
    apply (unitarySequenceMk_eq_one_iff dims L _).mp
    change quotientAssignment dims L f r = 1
    rw [hf, MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
  have ht := approximatelyTrivial_tendsto rels v dims hd L hfinite h f hr
  rw [← MonoidHom.comp_apply φ (PresentedGroup.mk rels), ← hf]
  exact (unitarySequenceMk_eq_one_iff dims L _).mpr ht

theorem approximatelyTrivial_iff_quotient_killed (v : FreeGroup S) (hfinite : rels.Finite)
    (L : Filter Nat) [L.NeBot] (hL : L ≤ atTop) :
    ApproximatelyTrivial rels v ↔
      ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
        ∀ φ : PresentedGroup rels →* UnitarySequenceQuotient dims L,
          φ (PresentedGroup.mk rels v) = 1 := by
  constructor
  · intro h dims hd φ
    exact approximatelyTrivial_quotient_killed rels dims L v hfinite hd h φ
  · exact approximatelyTrivial_of_quotient_killed rels v L hL

theorem approximatelyTrivial_iff_hyperfilter_killed (v : FreeGroup S) (hfinite : rels.Finite) :
    ApproximatelyTrivial rels v ↔
      ∀ (dims : Nat → Nat), (∀ n, 0 < dims n) →
        ∀ φ : PresentedGroup rels →* UnitarySequenceQuotient dims (hyperfilter Nat),
          φ (PresentedGroup.mk rels v) = 1 :=
  approximatelyTrivial_iff_quotient_killed rels v hfinite _ Nat.hyperfilter_le_atTop

end ThomGame.Analysis
