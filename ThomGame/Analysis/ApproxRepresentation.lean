module

public import ThomGame.Analysis.UnitaryHilbertSchmidt
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Free-group approximate representations with the paper's quantifiers

An assignment is a homomorphism from the free group into actual complex
unitary matrices. Relations have bounded normalized Hilbert--Schmidt
error, rather than being imposed before the assignment is defined.
The dimension-uniform property quantifies over all positive dimensions
after choosing a single positive tolerance.
-/

@[expose] public section
namespace ThomGame.Analysis

open scoped NNReal

abbrev MatrixAssignment (S : Type*) (d : Nat) := FreeGroup S →* UnitaryMatrix d

def IsApproxRepresentation {S : Type*} {d : Nat} (rels : Set (FreeGroup S))
    (δ : ℝ) (f : MatrixAssignment S d) : Prop :=
  ∀ r ∈ rels, unitaryLength (f r) ≤ δ

noncomputable def relationDefect {S : Type*} {d : Nat} (rels : Finset (FreeGroup S))
    (f : MatrixAssignment S d) : ℝ≥0 :=
  rels.sup (fun r => ⟨unitaryLength (f r), unitaryLength_nonneg _⟩)

def ApproximatelyTrivial {S : Type*} (rels : Set (FreeGroup S)) (v : FreeGroup S) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ (d : Nat), 0 < d → ∀ f : MatrixAssignment S d,
      IsApproxRepresentation rels δ f → unitaryLength (f v) < η

variable {S : Type*} {d : Nat}

theorem assignment_eq_lift (f : MatrixAssignment S d) :
    FreeGroup.lift (fun s => f (FreeGroup.of s)) = f := by
  apply FreeGroup.ext_hom
  intro s
  exact FreeGroup.lift_apply_of

theorem isApprox_mono {rels : Set (FreeGroup S)} {δ ε : ℝ} {f : MatrixAssignment S d}
    (h : IsApproxRepresentation rels δ f) (hle : δ ≤ ε) : IsApproxRepresentation rels ε f :=
  fun r hr => (h r hr).trans hle

theorem relationDefect_le_iff (rels : Finset (FreeGroup S)) (f : MatrixAssignment S d) (δ : ℝ) :
    (relationDefect rels f : ℝ) ≤ δ ↔ 0 ≤ δ ∧ IsApproxRepresentation (rels : Set (FreeGroup S)) δ f := by
  constructor
  · intro h
    refine ⟨(relationDefect rels f).coe_nonneg.trans h, ?_⟩
    intro r hr
    have hm : (⟨unitaryLength (f r), unitaryLength_nonneg _⟩ : ℝ≥0) ≤ relationDefect rels f := by
      exact Finset.le_sup (f := fun w => (⟨unitaryLength (f w), unitaryLength_nonneg _⟩ : ℝ≥0)) hr
    exact (show unitaryLength (f r) ≤ (relationDefect rels f : ℝ) from hm).trans h
  · rintro ⟨hδ, h⟩
    have hh : relationDefect rels f ≤ (⟨δ, hδ⟩ : ℝ≥0) :=
      Finset.sup_le (fun r hr => h r hr)
    exact hh

theorem isApprox_zero_iff [NeZero d] (rels : Set (FreeGroup S)) (f : MatrixAssignment S d) :
    IsApproxRepresentation rels 0 f ↔ ∀ r ∈ rels, f r = 1 := by
  constructor
  · intro h r hr
    exact (unitaryLength_eq_zero_iff _).mp (le_antisymm (h r hr) (unitaryLength_nonneg _))
  · intro h r hr
    simp [h r hr]

theorem assignment_descends_iff [NeZero d] (rels : Set (FreeGroup S)) (f : MatrixAssignment S d) :
    (∃ φ : PresentedGroup rels →* UnitaryMatrix d, φ.comp (PresentedGroup.mk rels) = f) ↔
      IsApproxRepresentation rels 0 f := by
  rw [isApprox_zero_iff]
  constructor
  · rintro ⟨φ, hφ⟩ r hr
    rw [← hφ, MonoidHom.comp_apply, PresentedGroup.one_of_mem hr, map_one]
  · intro h
    let φ := PresentedGroup.toGroup (rels := rels) (f := fun s => f (FreeGroup.of s))
      (by simpa only [assignment_eq_lift] using h)
    refine ⟨φ, ?_⟩
    apply FreeGroup.ext_hom
    intro s
    change φ (PresentedGroup.of s) = f (FreeGroup.of s)
    simp only [φ, PresentedGroup.toGroup.of]

theorem approximatelyTrivial_no_neg_one (rels : Set (FreeGroup S)) (v : FreeGroup S)
    (h : ApproximatelyTrivial rels v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d : Nat), 0 < d → ∀ f : MatrixAssignment S d,
      IsApproxRepresentation rels δ f → f v ≠ -1 := by
  obtain ⟨δ, hδ, hbound⟩ := h 1 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro d hd f hf heq
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hh := hbound d hd f hf
  rw [heq, unitaryLength_neg_one] at hh
  norm_num at hh

end ThomGame.Analysis
