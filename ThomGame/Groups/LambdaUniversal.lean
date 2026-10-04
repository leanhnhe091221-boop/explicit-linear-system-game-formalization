module

public import ThomGame.Groups.DoubleToLambda

/-!
# Universal property of the actual finite Λ presentation

The input is a homomorphism from the actual double, an involution j
commuting with its image and with z, and the relation z w z⁻¹ = w j.
The resulting map uses precisely the 74 labels of the source presentation.
-/

@[expose] public section
namespace ThomGame.Lambda

variable (G : Type*) [Group G]

structure Model where
  d : Double.GroupD →* G
  j : G
  z : G
  j_square : j * j = 1
  j_commutes : ∀ x, Commute j (d x)
  j_z : Commute j z
  conjugate_w : z * d Double.obstructionElement * z⁻¹ = d Double.obstructionElement * j

namespace Model
variable {G} (M : Model G)

def assignment (g : Generator) : G :=
  if hg : g.val < 72 then M.d (Double.ofGenerator ⟨g.val, hg⟩)
  else if g = 72 then M.j else M.z

theorem assignment_double (g : Double.Generator) :
    M.assignment (Double.lambdaGenerator g) = M.d (Double.ofGenerator g) := by
  simp [assignment, Double.lambdaGenerator, g.isLt]

theorem assignment_J : M.assignment 72 = M.j := by simp [assignment]
theorem assignment_z : M.assignment 73 = M.z := by simp [assignment]

theorem assignment_copy (b : Bool) (g : Compressor.Generator) :
    M.assignment (copyGenerator b g) = M.d (Double.copyHom b (Compressor.ofGenerator g)) := by
  rw [Double.copyHom_of, ← Double.lambdaGenerator_copy, assignment_double]

theorem assignment_copyRelator (b : Bool) (r : Word Compressor.Generator)
    (hr : r ∈ Compressor.rawRelators) : Word.eval M.assignment (copyWord b r) = 1 := by
  rw [copyWord, Word.eval_map_generators]
  have hf : (fun g => M.assignment (copyGenerator b g)) =
      fun g => (M.d.comp (Double.copyHom b)) (Compressor.ofGenerator g) :=
    funext (M.assignment_copy b)
  rw [hf, ← Word.map_eval, Compressor.eval_rawRelator r hr, map_one]

theorem assignment_w : Word.eval M.assignment w = M.d Double.obstructionElement := by
  rw [Double.obstruction_formula]
  simp only [map_mul, map_inv]
  simp [w, Lambda.h, t₁, t₂, assignment, Double.hElement, Double.t₁Element, Double.t₂Element]

theorem assignment_relator (r : Word Generator) (hr : r ∈ rawRelators) :
    Word.eval M.assignment r = 1 := by
  simp only [rawRelators, List.mem_append] at hr
  rcases hr with (((hr | hr) | hr) | hr) | hr
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact M.assignment_copyRelator false v hv
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact M.assignment_copyRelator true v hv
  · obtain rfl := List.mem_singleton.mp hr
    simpa [J, assignment_J] using M.j_square
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
    change Word.eval M.assignment (Word.commutator J (Word.generator (Double.lambdaGenerator a))) = 1
    simp only [Word.eval_commutator, J, Word.eval_generator, assignment_J, assignment_double]
    rw [(M.j_commutes _).eq]
    simp [mul_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Word.eval_commutator, J, Lambda.z, Word.eval_generator, assignment_J, assignment_z]
      rw [M.j_z.eq]
      simp [mul_assoc]
    · rw [Word.eval_equation_eq_one_iff]
      simpa [Word.eval_append, Word.eval_inverse, Lambda.z, J, assignment_z, assignment_J,
        assignment_w, mul_assoc] using M.conjugate_w

def toHom : GroupLambda →* G :=
  PresentedGroup.toGroup (f := M.assignment) (rels := rawRelationSet) (by
    rintro _ ⟨r, hr, rfl⟩
    exact M.assignment_relator r hr)

theorem toHom_of (g : Generator) : M.toHom (ofGenerator g) = M.assignment g :=
  PresentedGroup.toGroup.of _

theorem toHom_J : M.toHom JElement = M.j := by rw [JElement, toHom_of, assignment_J]
theorem toHom_z : M.toHom stableElement = M.z := by rw [stableElement, toHom_of, assignment_z]

theorem toHom_comp_double : M.toHom.comp Double.toLambda = M.d := by
  apply PresentedGroup.ext
  intro g
  change M.toHom (Double.toLambda (Double.ofGenerator g)) = M.d (Double.ofGenerator g)
  rw [Double.toLambda_of, toHom_of, assignment_double]

theorem toHom_double (x : Double.GroupD) : M.toHom (Double.toLambda x) = M.d x :=
  DFunLike.congr_fun M.toHom_comp_double x

end Model

theorem hom_ext {G : Type*} [Group G] {φ ψ : GroupLambda →* G}
    (hd : φ.comp Double.toLambda = ψ.comp Double.toLambda)
    (hj : φ JElement = ψ JElement) (hz : φ stableElement = ψ stableElement) : φ = ψ := by
  apply PresentedGroup.ext
  intro g
  change φ (ofGenerator g) = ψ (ofGenerator g)
  by_cases hg : g.val < 72
  · have h := DFunLike.congr_fun hd (Double.ofGenerator ⟨g.val, hg⟩)
    have he : Double.lambdaGenerator ⟨g.val, hg⟩ = g := Fin.ext rfl
    simpa only [MonoidHom.comp_apply, Double.toLambda_of, he] using h
  · by_cases hj' : g = 72
    · subst g
      exact hj
    · have hz' : g = 73 := by
        apply Fin.ext
        have hn : g.val ≠ 72 := by intro h; exact hj' (Fin.ext h)
        omega
      subst g
      exact hz

end ThomGame.Lambda
