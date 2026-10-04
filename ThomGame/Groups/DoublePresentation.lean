module

public import ThomGame.Groups.CompressorGroup
public import ThomGame.Groups.LambdaPresentation

/-!
# The 72-generator presentation of the double

The positive labels in the two copies of Q have the same generator number.
Negative labels and shears have separate numbers. The numbering is the
restriction of the actual Λ numbering to its first 72 generators.
-/

@[expose] public section
namespace ThomGame.Double

abbrev Generator := Fin 72

def copyGenerator (b : Bool) (g : Compressor.Generator) : Generator :=
  ⟨Lambda.copyNumber b g - 1, by have := Lambda.copyNumber_range b g; omega⟩

def copyWord (b : Bool) (w : Word Compressor.Generator) : Word Generator :=
  w.map fun a => (copyGenerator b a.1, a.2)

def generatorList : List Compressor.Generator :=
  Compressor.roots.flatMap (fun r => Compressor.coefficients.map (fun m => .inl (r, m))) ++
    Compressor.roots.map Sum.inr

def candidates : List (Bool × Compressor.Generator) :=
  [false, true].flatMap fun b => generatorList.map fun g => (b, g)

/-- Pick a preimage under the two-copy numbering. Its correctness is checked
below for every one of the 72 target labels. -/
def decode (g : Generator) : Bool × Compressor.Generator :=
  (candidates.find? (fun p => decide (copyGenerator p.1 p.2 = g))).getD
    (false, .inr Compressor.root12)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem copy_decode : ∀ g : Generator, copyGenerator (decode g).1 (decode g).2 = g := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem decode_copy : ∀ b g,
    (decode (copyGenerator b g)).2 = g ∧
      ((decode (copyGenerator b g)).1 = b ∨ Compressor.positive g = true) := by
  decide +kernel

theorem copy_positive_eq : ∀ g, Compressor.positive g = true →
    copyGenerator false g = copyGenerator true g := by decide +kernel

def rawRelators : List (Word Generator) :=
  Compressor.rawRelators.map (copyWord false) ++ Compressor.rawRelators.map (copyWord true)

def relators : Set (FreeGroup Generator) := FreeGroup.mk '' {w | w ∈ rawRelators}

abbrev GroupD := PresentedGroup relators

def ofGenerator (g : Generator) : GroupD := PresentedGroup.of g

theorem eval_rawRelator (r : Word Generator) (hr : r ∈ rawRelators) :
    Word.eval ofGenerator r = 1 := by
  rw [show ofGenerator = PresentedGroup.of (rels := relators) from rfl, Word.eval_presented]
  exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩

theorem copyWord_mem (b : Bool) (r : Word Compressor.Generator) (hr : r ∈ Compressor.rawRelators) :
    copyWord b r ∈ rawRelators := by
  cases b with
  | false => exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  | true => exact List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

def copyHom (b : Bool) : Compressor.GroupQ →* GroupD :=
  PresentedGroup.toGroup (f := fun g => ofGenerator (copyGenerator b g))
    (rels := Compressor.relators) (by
      rintro _ ⟨r, hr, rfl⟩
      change Word.eval (fun g => ofGenerator (copyGenerator b g)) r = 1
      rw [← Word.eval_map_generators]
      exact eval_rawRelator _ (copyWord_mem b r hr))

theorem copyHom_of (b : Bool) (g : Compressor.Generator) :
    copyHom b (Compressor.ofGenerator g) = ofGenerator (copyGenerator b g) :=
  PresentedGroup.toGroup.of _

theorem copyHom_positive (x : Compressor.positiveSubgroup) : copyHom false x = copyHom true x := by
  apply Compressor.hom_agree_on_positive
  intro g hg
  rw [copyHom_of, copyHom_of, copy_positive_eq g hg]

theorem generator_count : Fintype.card Generator = 72 := Fintype.card_fin _

theorem raw_relator_count : rawRelators.length = 15458 := by
  simp only [rawRelators, List.length_append, List.length_map, Compressor.raw_relator_count]

end ThomGame.Double
