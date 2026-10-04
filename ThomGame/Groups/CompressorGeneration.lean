module

public import ThomGame.Groups.CompressorCompression

/-!
# H and the positive shears generate Q

The recovery relations express every negative label using H and the shears.
Since both H and all six positive shears compress H, the compression monoid
generates Q as a group. These are concrete consequences of the presentation;
no property (T) assertion is made here.
-/

@[expose] public section
namespace ThomGame.Compressor

def withShears : Subgroup GroupQ :=
  Subgroup.closure ((positiveSubgroup : Set GroupQ) ∪ Set.range shearElement)

theorem positive_le_withShears : positiveSubgroup ≤ withShears :=
  fun _ h => Subgroup.subset_closure (Or.inl h)

theorem shear_mem_withShears (s : Root) : shearElement s ∈ withShears :=
  Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem recoveryWord_letters_shear : ∀ c a, a ∈ recoveryWord c →
    ∃ s : Root, a.1 = Sum.inr s := by decide +kernel

theorem recoveryWord_mem_withShears (c : Axis) : Word.eval ofGenerator (recoveryWord c) ∈ withShears := by
  apply Word.eval_mem
  intro a ha
  obtain ⟨s, hs⟩ := recoveryWord_letters_shear c a ha
  rw [hs]
  exact shear_mem_withShears s

theorem recovery_relator_mem (c : Axis) (r : Root) :
    Word.equation (conjugate (recoveryWord c) (X r (some (c, true))))
      (X r (some (c, false))) ∈ rawRelators := by
  have h : Word.equation (conjugate (recoveryWord c) (X r (some (c, true))))
      (X r (some (c, false))) ∈ negativeRecovery := by
    unfold negativeRecovery
    exact List.mem_flatMap.mpr ⟨c, List.mem_finRange c,
      List.mem_map.mpr ⟨r, mem_roots r, rfl⟩⟩
  exact List.mem_append_right _ h

theorem negative_recovery (c : Axis) (r : Root) :
    Word.eval ofGenerator (recoveryWord c) * ofGenerator (.inl (r, some (c, true))) *
      (Word.eval ofGenerator (recoveryWord c))⁻¹ = ofGenerator (.inl (r, some (c, false))) := by
  have h := eval_rawRelator _ (recovery_relator_mem c r)
  rw [Word.eval_equation_eq_one_iff] at h
  simpa [conjugate, X, mul_assoc] using h

theorem generator_mem_withShears (g : Generator) : ofGenerator g ∈ withShears := by
  cases g with
  | inr s => exact shear_mem_withShears s
  | inl p =>
    rcases p with ⟨r, m⟩
    cases m with
    | none => exact positive_le_withShears (ofGenerator_mem_positiveSubgroup _ rfl)
    | some p =>
      rcases p with ⟨c, b⟩
      cases b with
      | true => exact positive_le_withShears (ofGenerator_mem_positiveSubgroup _ rfl)
      | false =>
        rw [← negative_recovery]
        exact withShears.mul_mem
          (withShears.mul_mem (recoveryWord_mem_withShears c)
            (positive_le_withShears (ofGenerator_mem_positiveSubgroup _ rfl)))
          (withShears.inv_mem (recoveryWord_mem_withShears c))

theorem withShears_eq_top : withShears = ⊤ := by
  apply top_unique
  intro x _
  exact generated_by withShears generator_mem_withShears x

/-- All elements whose positive conjugation sends H into H. -/
def compressionMonoid : Submonoid GroupQ where
  carrier := {g | ∀ x ∈ positiveSubgroup, g * x * g⁻¹ ∈ positiveSubgroup}
  one_mem' := by intro x hx; simpa using hx
  mul_mem' := by
    intro a b ha hb x hx
    have h := ha (b * x * b⁻¹) (hb x hx)
    simpa [mul_inv_rev, mul_assoc] using h

theorem positive_mem_compressionMonoid (g : GroupQ) (hg : g ∈ positiveSubgroup) :
    g ∈ compressionMonoid := by
  intro x hx
  exact positiveSubgroup.mul_mem (positiveSubgroup.mul_mem hg hx) (positiveSubgroup.inv_mem hg)

theorem shear_mem_compressionMonoid (s : Root) : shearElement s ∈ compressionMonoid :=
  shear_compresses s

/-- The paper's infranormality criterion, with the compression monoid defined
by actual subgroup containment under conjugation. -/
theorem compression_generates : Subgroup.closure (compressionMonoid : Set GroupQ) = ⊤ := by
  have h : withShears ≤ Subgroup.closure (compressionMonoid : Set GroupQ) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    apply Subgroup.subset_closure
    rcases hg with hg | ⟨s, rfl⟩
    · exact positive_mem_compressionMonoid g hg
    · exact shear_mem_compressionMonoid s
  rw [withShears_eq_top] at h
  exact top_unique h

end ThomGame.Compressor
