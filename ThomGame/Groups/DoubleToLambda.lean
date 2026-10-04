module

public import ThomGame.Groups.DoubleAmalgam
public import ThomGame.Groups.LambdaRelations

/-!
# The double inside the raw Λ presentation

The canonical map on the first 72 labels respects all double relations.
The special h, t₁, t₂ and obstruction words map to the exact Λ words.
Injectivity into Λ will require the HNN construction; it is not claimed here.
-/

@[expose] public section
namespace ThomGame.Double

def lambdaGenerator (g : Generator) : Lambda.Generator := g.castLE (by decide)

theorem lambdaGenerator_copy (b : Bool) (g : Compressor.Generator) :
    lambdaGenerator (copyGenerator b g) = Lambda.copyGenerator b g := rfl

theorem lambda_copyRelator_mem (b : Bool) (r : Word Compressor.Generator)
    (hr : r ∈ Compressor.rawRelators) : Lambda.copyWord b r ∈ Lambda.rawRelators := by
  have hm : Lambda.copyWord b r ∈ Compressor.rawRelators.map (Lambda.copyWord b) :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  cases b <;> simp only [Lambda.rawRelators, List.mem_append] <;> tauto

theorem lambdaAssignment_copyRelator (b : Bool) (r : Word Compressor.Generator)
    (hr : r ∈ Compressor.rawRelators) :
    Word.eval (fun g => Lambda.ofGenerator (lambdaGenerator g)) (copyWord b r) = 1 := by
  have h := Lambda.eval_rawRelator (Lambda.copyWord b r) (lambda_copyRelator_mem b r hr)
  rw [Lambda.copyWord, Word.eval_map_generators] at h
  rw [copyWord, Word.eval_map_generators]
  exact h

def toLambda : GroupD →* Lambda.GroupLambda :=
  PresentedGroup.toGroup (f := fun g => Lambda.ofGenerator (lambdaGenerator g)) (rels := relators) (by
    rintro _ ⟨r, hr, rfl⟩
    change Word.eval (fun g => Lambda.ofGenerator (lambdaGenerator g)) r = 1
    simp only [rawRelators, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · exact lambdaAssignment_copyRelator false w hw
    · exact lambdaAssignment_copyRelator true w hw)

theorem toLambda_of (g : Generator) :
    toLambda (ofGenerator g) = Lambda.ofGenerator (lambdaGenerator g) := PresentedGroup.toGroup.of _

def hElement : GroupD := ofGenerator 2
def t₁Element : GroupD := ofGenerator 42
def t₂Element : GroupD := ofGenerator 66

def obstructionWord : Word Generator :=
  Word.commutator (Word.generator 2) (Word.generator 66 ++ Word.inverse (Word.generator 42))

def obstructionElement : GroupD := Word.eval ofGenerator obstructionWord

theorem obstruction_formula :
    obstructionElement = hElement * (t₂Element * t₁Element⁻¹) * hElement⁻¹ *
      (t₂Element * t₁Element⁻¹)⁻¹ := by
  simp [obstructionElement, obstructionWord, hElement, t₁Element, t₂Element]

theorem copy_h (b : Bool) :
    copyHom b (Compressor.ofGenerator (.inl (Compressor.root12, some (1, true)))) = hElement := by
  rw [copyHom_of]
  rfl

theorem copy_t₁ :
    copyHom false (Compressor.ofGenerator (.inr Compressor.root12)) = t₁Element := by
  rw [copyHom_of]
  rfl

theorem copy_t₂ :
    copyHom true (Compressor.ofGenerator (.inr Compressor.root12)) = t₂Element := by
  rw [copyHom_of]
  rfl

theorem toLambda_h : toLambda hElement = Word.eval Lambda.ofGenerator Lambda.h := by
  rw [hElement, toLambda_of]
  exact (Word.eval_generator Lambda.ofGenerator 2).symm

theorem toLambda_t₁ : toLambda t₁Element = Word.eval Lambda.ofGenerator Lambda.t₁ := by
  rw [t₁Element, toLambda_of]
  exact (Word.eval_generator Lambda.ofGenerator 42).symm

theorem toLambda_t₂ : toLambda t₂Element = Word.eval Lambda.ofGenerator Lambda.t₂ := by
  rw [t₂Element, toLambda_of]
  exact (Word.eval_generator Lambda.ofGenerator 66).symm

theorem toLambda_obstruction : toLambda obstructionElement = Lambda.obstructionElement := by
  rw [obstruction_formula]
  simp only [map_mul, map_inv, toLambda_h, toLambda_t₁, toLambda_t₂]
  simp [Lambda.obstructionElement, Lambda.w]

end ThomGame.Double
