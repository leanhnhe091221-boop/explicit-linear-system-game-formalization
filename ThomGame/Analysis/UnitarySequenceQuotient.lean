module

public import ThomGame.Analysis.ApproxRepresentation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Actual unitary matrix sequences modulo vanishing normalized 2-error

For a dimension sequence and a filter, the sequences whose distance to
the identity tends to zero form a normal subgroup. The quotient and its
universal map are actual group constructions. This is the unitary metric
quotient; a tracial matrix algebra and its unitary-lifting theorem are
separate constructions, not assumed by this definition.
-/

@[expose] public section
namespace ThomGame.Analysis

open Filter
open scoped Topology

variable {ι : Type*} (dims : ι → Nat) (L : Filter ι)

abbrev UnitarySequence := (i : ι) → UnitaryMatrix (dims i)

def nullUnitarySubgroup : Subgroup (UnitarySequence dims) where
  carrier U := Tendsto (fun i => unitaryLength (U i)) L (𝓝 0)
  one_mem' := by
    change Tendsto (fun i => unitaryLength (1 : UnitaryMatrix (dims i))) L (𝓝 0)
    simpa only [unitaryLength_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) L (𝓝 0))
  mul_mem' := by
    intro U V hU hV
    change Tendsto (fun i => unitaryLength (U i)) L (𝓝 0) at hU
    change Tendsto (fun i => unitaryLength (V i)) L (𝓝 0) at hV
    have hsum := hU.add hV
    simp only [zero_add] at hsum
    exact squeeze_zero (fun i => unitaryLength_nonneg (U i * V i))
      (fun i => unitaryLength_mul_le (U i) (V i)) hsum
  inv_mem' := by
    intro U hU
    change Tendsto (fun i => unitaryLength (U i)) L (𝓝 0) at hU
    change Tendsto (fun i => unitaryLength ((U i)⁻¹)) L (𝓝 0)
    simpa only [unitaryLength_inv] using hU

instance nullUnitarySubgroup_normal : (nullUnitarySubgroup dims L).Normal where
  conj_mem U hU V := by
    change Tendsto (fun i => unitaryLength (U i)) L (𝓝 0) at hU
    change Tendsto (fun i => unitaryLength (V i * U i * (V i)⁻¹)) L (𝓝 0)
    simpa only [unitaryLength_conj] using hU

abbrev UnitarySequenceQuotient := UnitarySequence dims ⧸ nullUnitarySubgroup dims L

def unitarySequenceMk : UnitarySequence dims →* UnitarySequenceQuotient dims L :=
  QuotientGroup.mk' _

theorem unitarySequenceMk_eq_one_iff (U : UnitarySequence dims) :
    unitarySequenceMk dims L U = 1 ↔ Tendsto (fun i => unitaryLength (U i)) L (𝓝 0) :=
  QuotientGroup.eq_one_iff _

theorem unitarySequenceMk_eq_iff (U V : UnitarySequence dims) :
    unitarySequenceMk dims L U = unitarySequenceMk dims L V ↔
      Tendsto (fun i => unitaryDist (U i) (V i)) L (𝓝 0) := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, unitarySequenceMk_eq_one_iff]
  simp only [Pi.mul_apply, Pi.inv_apply, ← unitaryDist_eq_length]

theorem unitarySequenceMk_ne_one_of_lower_bound [L.NeBot]
    (U : UnitarySequence dims) {η : ℝ} (hη : 0 < η)
    (hU : ∀ᶠ i in L, η ≤ unitaryLength (U i)) : unitarySequenceMk dims L U ≠ 1 := by
  intro he
  have ht := (unitarySequenceMk_eq_one_iff dims L U).mp he
  have hsmall := ht.eventually (gt_mem_nhds hη)
  obtain ⟨i, hi, hj⟩ := (hU.and hsmall).exists
  exact (not_lt_of_ge hi) hj

variable {S : Type*}

def sequenceAssignment (f : (i : ι) → MatrixAssignment S (dims i)) :
    FreeGroup S →* UnitarySequence dims where
  toFun w i := f i w
  map_one' := funext fun i => (f i).map_one
  map_mul' u v := funext fun i => (f i).map_mul u v

def quotientAssignment (f : (i : ι) → MatrixAssignment S (dims i)) :
    FreeGroup S →* UnitarySequenceQuotient dims L :=
  (unitarySequenceMk dims L).comp (sequenceAssignment dims f)

theorem quotientAssignment_relation (rels : Set (FreeGroup S))
    (f : (i : ι) → MatrixAssignment S (dims i))
    (hr : ∀ r ∈ rels, Tendsto (fun i => unitaryLength (f i r)) L (𝓝 0))
    (r : FreeGroup S) (h : r ∈ rels) : quotientAssignment dims L f r = 1 :=
  (unitarySequenceMk_eq_one_iff dims L _).mpr (hr r h)

noncomputable def sequenceRepresentation (rels : Set (FreeGroup S))
    (f : (i : ι) → MatrixAssignment S (dims i))
    (hr : ∀ r ∈ rels, Tendsto (fun i => unitaryLength (f i r)) L (𝓝 0)) :
    PresentedGroup rels →* UnitarySequenceQuotient dims L :=
  QuotientGroup.lift (Subgroup.normalClosure rels) (quotientAssignment dims L f)
    (fun _r h => MonoidHom.mem_ker.mp ((Subgroup.normalClosure_le_normal
      (fun r h => MonoidHom.mem_ker.mpr (quotientAssignment_relation dims L rels f hr r h))) h))

theorem sequenceRepresentation_mk (rels : Set (FreeGroup S))
    (f : (i : ι) → MatrixAssignment S (dims i))
    (hr : ∀ r ∈ rels, Tendsto (fun i => unitaryLength (f i r)) L (𝓝 0))
    (w : FreeGroup S) :
    sequenceRepresentation dims L rels f hr (PresentedGroup.mk rels w) =
      unitarySequenceMk dims L (fun i => f i w) := rfl

end ThomGame.Analysis
