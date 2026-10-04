module

public import ThomGame.Groups.DoublePresentation
public import Mathlib.GroupTheory.PushoutI

/-!
# The actual finite double presentation is Q *_H Q

Both maps out of H are its subgroup inclusion into Q. The two universal
maps constructed here are inverse and fix every named copy generator.
Consequently both copies of Q embed in the 72-generator presentation.
-/

@[expose] public section
namespace ThomGame.Double

def amalgamMaps : (b : Bool) → Compressor.positiveSubgroup →* Compressor.GroupQ :=
  fun _ => Compressor.positiveSubgroup.subtype

abbrev Amalgam := Monoid.PushoutI amalgamMaps

def inclusion (b : Bool) : Compressor.GroupQ →* Amalgam :=
  Monoid.PushoutI.of (φ := amalgamMaps) b

theorem inclusion_injective (b : Bool) : Function.Injective (inclusion b) :=
  Monoid.PushoutI.of_injective (φ := amalgamMaps) (fun _ => Subtype.val_injective) b

theorem inclusion_positive (b : Bool) (g : Compressor.Generator) (hg : Compressor.positive g = true) :
    inclusion b (Compressor.ofGenerator g) = inclusion false (Compressor.ofGenerator g) := by
  let x : Compressor.positiveSubgroup :=
    ⟨Compressor.ofGenerator g, Compressor.ofGenerator_mem_positiveSubgroup g hg⟩
  exact (Monoid.PushoutI.of_apply_eq_base amalgamMaps b x).trans
    (Monoid.PushoutI.of_apply_eq_base amalgamMaps false x).symm

def amalgamToPresentation : Amalgam →* GroupD :=
  Monoid.PushoutI.lift (φ := amalgamMaps) copyHom
    ((copyHom false).comp Compressor.positiveSubgroup.subtype) (by
    intro b
    cases b with
    | false => rfl
    | true =>
      apply MonoidHom.ext
      intro x
      exact (copyHom_positive x).symm)

theorem amalgamToPresentation_inclusion (b : Bool) (x : Compressor.GroupQ) :
    amalgamToPresentation (inclusion b x) = copyHom b x :=
  Monoid.PushoutI.lift_of (φ := amalgamMaps) (i := b) _ _ _ x

def amalgamAssignment (g : Generator) : Amalgam :=
  inclusion (decode g).1 (Compressor.ofGenerator (decode g).2)

theorem amalgamAssignment_copy (b : Bool) (g : Compressor.Generator) :
    amalgamAssignment (copyGenerator b g) = inclusion b (Compressor.ofGenerator g) := by
  obtain ⟨hletter, hcopy⟩ := decode_copy b g
  unfold amalgamAssignment
  rw [hletter]
  rcases hcopy with hb | hg
  · rw [hb]
  · exact (inclusion_positive _ g hg).trans (inclusion_positive b g hg).symm

theorem amalgamAssignment_copyRelator (b : Bool) (r : Word Compressor.Generator)
    (hr : r ∈ Compressor.rawRelators) : Word.eval amalgamAssignment (copyWord b r) = 1 := by
  rw [copyWord, Word.eval_map_generators]
  have hf : (fun g => amalgamAssignment (copyGenerator b g)) =
      fun g => inclusion b (Compressor.ofGenerator g) := funext (amalgamAssignment_copy b)
  rw [hf, ← Word.map_eval, Compressor.eval_rawRelator r hr, map_one]

theorem amalgamAssignment_relator (r : Word Generator) (hr : r ∈ rawRelators) :
    Word.eval amalgamAssignment r = 1 := by
  simp only [rawRelators, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact amalgamAssignment_copyRelator false w hw
  · exact amalgamAssignment_copyRelator true w hw

def presentationToAmalgam : GroupD →* Amalgam :=
  PresentedGroup.toGroup (f := amalgamAssignment) (rels := relators) (by
    rintro _ ⟨r, hr, rfl⟩
    exact amalgamAssignment_relator r hr)

theorem presentationToAmalgam_of (g : Generator) :
    presentationToAmalgam (ofGenerator g) = amalgamAssignment g := PresentedGroup.toGroup.of _

theorem presentationToAmalgam_copy (b : Bool) :
    presentationToAmalgam.comp (copyHom b) = inclusion b := by
  apply PresentedGroup.ext
  intro g
  change presentationToAmalgam (copyHom b (Compressor.ofGenerator g)) = _
  rw [copyHom_of, presentationToAmalgam_of, amalgamAssignment_copy]
  rfl

theorem presentationToAmalgam_copy_apply (b : Bool) (x : Compressor.GroupQ) :
    presentationToAmalgam (copyHom b x) = inclusion b x :=
  DFunLike.congr_fun (presentationToAmalgam_copy b) x

theorem amalgamToPresentation_comp_presentationToAmalgam :
    amalgamToPresentation.comp presentationToAmalgam = MonoidHom.id GroupD := by
  apply PresentedGroup.ext
  intro g
  change amalgamToPresentation (presentationToAmalgam (ofGenerator g)) = ofGenerator g
  rw [presentationToAmalgam_of, amalgamAssignment, amalgamToPresentation_inclusion,
    copyHom_of, copy_decode]

theorem presentationToAmalgam_comp_amalgamToPresentation :
    presentationToAmalgam.comp amalgamToPresentation = MonoidHom.id Amalgam := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro b
  apply MonoidHom.ext
  intro x
  change presentationToAmalgam (amalgamToPresentation (inclusion b x)) = inclusion b x
  rw [amalgamToPresentation_inclusion, presentationToAmalgam_copy_apply]

def amalgamEquiv : GroupD ≃* Amalgam where
  toFun := presentationToAmalgam
  invFun := amalgamToPresentation
  left_inv := DFunLike.congr_fun amalgamToPresentation_comp_presentationToAmalgam
  right_inv := DFunLike.congr_fun presentationToAmalgam_comp_amalgamToPresentation
  map_mul' := presentationToAmalgam.map_mul

theorem amalgamEquiv_copy (b : Bool) (x : Compressor.GroupQ) :
    amalgamEquiv (copyHom b x) = inclusion b x := presentationToAmalgam_copy_apply b x

theorem copyHom_injective (b : Bool) : Function.Injective (copyHom b) := by
  intro x y h
  apply inclusion_injective b
  rw [← presentationToAmalgam_copy_apply, ← presentationToAmalgam_copy_apply]
  exact congrArg presentationToAmalgam h

end ThomGame.Double
