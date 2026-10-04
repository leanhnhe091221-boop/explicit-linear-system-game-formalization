module

public import ThomGame.Groups.CompressorElementaryRelations
public import ThomGame.Groups.CompressorNormal

/-!
# The actual finite covers surject onto N and H

The six formal variable labels map bijectively to the positive and
negative coefficient labels. The three-variable cover maps to the
positive labels. The image calculations prove surjectivity onto the
specified subgroups of Q; no injectivity or finite presentation of H
is inferred from these surjections.
-/

@[expose] public noncomputable section
namespace ThomGame.Compressor

def coverToQ {d : Nat} (σ : PrimeFiveRankThreeCover.Coefficient d → Coeff) (hσ : σ none = none) :
    PrimeFiveRankThreeCover.Cover d →* GroupQ := (coverModel σ hσ).toHom

@[simp] theorem coverToQ_of {d : Nat}
    (σ : PrimeFiveRankThreeCover.Coefficient d → Coeff) (hσ : σ none = none)
    (r : Root) (m : PrimeFiveRankThreeCover.Coefficient d) :
    coverToQ σ hσ (PrimeFiveRankThreeCover.of d r m) = ofGenerator (.inl (r, σ m)) :=
  (coverModel σ hσ).toHom_of r m

theorem coverToQ_range {d : Nat}
    (σ : PrimeFiveRankThreeCover.Coefficient d → Coeff) (hσ : σ none = none) :
    (coverToQ σ hσ).range =
      Subgroup.closure (Set.range fun g : PrimeFiveRankThreeCover.Generator d => ofGenerator (.inl (g.1, σ g.2))) :=
  (coverModel σ hσ).range_toHom

def fullVariableEquiv : Fin 6 ≃ Axis × Bool :=
  (Fintype.equivFinOfCardEq (show Fintype.card (Axis × Bool) = 6 by decide)).symm

def fullCoverCoefficient : PrimeFiveRankThreeCover.Coefficient 6 → Coeff := Option.map fullVariableEquiv

def positiveCoverCoefficient : PrimeFiveRankThreeCover.Coefficient 3 → Coeff := Option.map (fun c => (c, true))

theorem fullCoverCoefficient_none : fullCoverCoefficient none = none := rfl

theorem positiveCoverCoefficient_none : positiveCoverCoefficient none = none := rfl

theorem fullCoverCoefficient_surjective : Function.Surjective fullCoverCoefficient := by
  intro m
  cases m with
  | none => exact ⟨none, rfl⟩
  | some p => exact ⟨some (fullVariableEquiv.symm p), congrArg some (fullVariableEquiv.apply_symm_apply p)⟩

def fullCoverToQ : PrimeFiveRankThreeCover.Cover 6 →* GroupQ :=
  coverToQ fullCoverCoefficient fullCoverCoefficient_none

def positiveCoverToQ : PrimeFiveRankThreeCover.Cover 3 →* GroupQ :=
  coverToQ positiveCoverCoefficient positiveCoverCoefficient_none

theorem fullCoverToQ_range : fullCoverToQ.range = elementarySubgroup := by
  rw [fullCoverToQ, coverToQ_range fullCoverCoefficient fullCoverCoefficient_none]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨⟨r, m⟩, rfl⟩
    exact ⟨.inl (r, fullCoverCoefficient m), rfl, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    cases g with
    | inl p =>
        obtain ⟨m, hm⟩ := fullCoverCoefficient_surjective p.2
        exact ⟨(p.1, m), by simp only [hm]⟩
    | inr s => simp [elementary] at hg

theorem positiveCoverToQ_range : positiveCoverToQ.range = positiveSubgroup := by
  rw [positiveCoverToQ, coverToQ_range positiveCoverCoefficient positiveCoverCoefficient_none]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨⟨r, m⟩, rfl⟩
    refine ⟨.inl (r, positiveCoverCoefficient m), ?_, rfl⟩
    cases m <;> rfl
  · rintro ⟨g, hg, rfl⟩
    cases g with
    | inr s => simp [positive] at hg
    | inl p =>
        rcases p with ⟨r, m⟩
        cases m with
        | none => exact ⟨(r, none), rfl⟩
        | some p =>
            rcases p with ⟨c, b⟩
            cases b with
            | false => simp [positive] at hg
            | true => exact ⟨(r, some c), rfl⟩

def coverToElementary : PrimeFiveRankThreeCover.Cover 6 →* elementarySubgroup :=
  fullCoverToQ.codRestrict elementarySubgroup (fun x => by
    rw [← fullCoverToQ_range]
    exact ⟨x, rfl⟩)

def coverToPositive : PrimeFiveRankThreeCover.Cover 3 →* positiveSubgroup :=
  positiveCoverToQ.codRestrict positiveSubgroup (fun x => by
    rw [← positiveCoverToQ_range]
    exact ⟨x, rfl⟩)

theorem coverToElementary_surjective : Function.Surjective coverToElementary := by
  intro x
  have hx : x.val ∈ fullCoverToQ.range := by rw [fullCoverToQ_range]; exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

theorem coverToPositive_surjective : Function.Surjective coverToPositive := by
  intro x
  have hx : x.val ∈ positiveCoverToQ.range := by rw [positiveCoverToQ_range]; exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

theorem coverToElementary_of (r : Root) (m : PrimeFiveRankThreeCover.Coefficient 6) :
    (coverToElementary (PrimeFiveRankThreeCover.of 6 r m)).val = ofGenerator (.inl (r, fullCoverCoefficient m)) :=
  coverToQ_of _ _ r m

theorem coverToPositive_of (r : Root) (m : PrimeFiveRankThreeCover.Coefficient 3) :
    (coverToPositive (PrimeFiveRankThreeCover.of 3 r m)).val = ofGenerator (.inl (r, positiveCoverCoefficient m)) :=
  coverToQ_of _ _ r m

end ThomGame.Compressor
