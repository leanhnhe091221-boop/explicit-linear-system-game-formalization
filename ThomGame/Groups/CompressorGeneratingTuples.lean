module

public import ThomGame.Groups.CompressorGroup

/-!
# Finite generating tuples for the actual Q and H

These tuples enumerate the existing typed generators. Their ranges,
and hence the generated subgroups, are proved exactly. The enumeration
is used only for spectral gaps; it does not change presentation order.
-/

@[expose] public section
namespace ThomGame.Compressor

noncomputable def generatorTuple : Fin 48 → GroupQ :=
  fun j => ofGenerator ((Fintype.equivFinOfCardEq generator_card).symm j)

noncomputable def positiveGeneratorTuple : Fin 24 → GroupQ :=
  fun j => ofGenerator ((Fintype.equivFinOfCardEq positive_generator_count).symm j).val

theorem generatorTuple_range : Set.range generatorTuple = Set.range ofGenerator := by
  let e := (Fintype.equivFinOfCardEq generator_card).symm
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨e j, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨e.symm g, congrArg ofGenerator (e.apply_symm_apply g)⟩

theorem positiveGeneratorTuple_range :
    Set.range positiveGeneratorTuple = ofGenerator '' {g | positive g = true} := by
  let e := (Fintype.equivFinOfCardEq positive_generator_count).symm
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(e j).val, (e j).property, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨e.symm ⟨g, hg⟩, ?_⟩
    exact congrArg (fun a : {g : Generator // positive g = true} => ofGenerator a.val)
      (e.apply_symm_apply ⟨g, hg⟩)

theorem generatorTuple_generates : Subgroup.closure (Set.range generatorTuple) = ⊤ := by
  rw [generatorTuple_range]
  apply top_unique
  intro x _
  exact generated_by (Subgroup.closure (Set.range ofGenerator))
    (fun g => Subgroup.subset_closure ⟨g, rfl⟩) x

theorem positiveGeneratorTuple_generates :
    Subgroup.closure (Set.range positiveGeneratorTuple) = positiveSubgroup := by
  rw [positiveGeneratorTuple_range]
  rfl

end ThomGame.Compressor
