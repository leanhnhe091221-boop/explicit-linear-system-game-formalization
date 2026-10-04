module

public import ThomGame.Groups.LaurentGroup
public import ThomGame.Groups.CompressorGroup

/-!
# Verification of every defining relation of Q

Each family of the actual ordered relation generator is verified in the
Laurent semidirect matrix group. This constructs a homomorphism from the
actual quotient Q, with no assumed relation-verification certificate.
-/

@[expose] public noncomputable section
namespace ThomGame.LaurentModel

open Compressor

theorem eval_power {G : Type*} [Group G] (f : Generator → G) (w : Word Generator) (n : Nat) :
    Word.eval f (power w n) = (Word.eval f w) ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simpa [power, List.replicate_succ, pow_succ'] using congrArg (Word.eval f w * ·) ih

theorem eval_conjugate {G : Type*} [Group G] (f : Generator → G) (u v : Word Generator) :
    Word.eval f (conjugate u v) = Word.eval f u * Word.eval f v * (Word.eval f u)⁻¹ := by
  simp [conjugate, mul_assoc]

@[simp] theorem eval_X (r : Root) (m : Coeff) :
    Word.eval generatorImage (X r m) = matrixX r (coefficient m) := Word.eval_generator _ _

@[simp] theorem eval_shear (s : Root) :
    Word.eval generatorImage (shear s) = matrixS s := Word.eval_generator _ _

theorem eval_signed_shear (s : Root) (ε : Bool) :
    Word.eval generatorImage (signed (shear s) ε) =
      integralHom (if ε then integralShear s else (integralShear s)⁻¹) := by
  cases ε <;> simp [signed, matrixS]

theorem eval_action (s r : Root) (ε : Bool) (m : Coeff) :
    Word.eval generatorImage (conjugate (signed (shear s) ε) (X r m)) =
      Word.eval generatorImage (actionTarget s r ε m) := by
  rw [eval_conjugate, eval_signed_shear, eval_X, integral_conjugate_matrixX]
  cases m with
  | none => simp [actionTarget, coefficient_none]
  | some p =>
    rcases p with ⟨c, σ⟩
    by_cases hc : c = target s
    · simp only [actionTarget, hc, ↓reduceIte, Word.eval_commutator, eval_X,
        matrixX_commutator_across, shear_coefficient]
    · simp [actionTarget, hc, shear_coefficient]

theorem eval_recoveryWord (c : Axis) :
    Word.eval generatorImage (recoveryWord c) = integralHom (integralRecovery c) := by
  simp [recoveryWord, eval_power, integralRecovery, matrixS, mul_assoc]

theorem eval_recovery (c : Axis) (r : Root) :
    Word.eval generatorImage (conjugate (recoveryWord c) (X r (some (c, true)))) =
      Word.eval generatorImage (X r (some (c, false))) := by
  rw [eval_conjugate, eval_recoveryWord, eval_X, integral_conjugate_matrixX,
    recovery_coefficient, eval_X]

private theorem commute_word {G : Type*} [Group G] {a b : G} (h : Commute a b) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [h.eq]
  simp [mul_assoc]

theorem eval_e0 (v : Word Generator) (hv : v ∈ e0) : Word.eval generatorImage v = 1 := by
  simp only [e0, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨r, _, m, _, rfl⟩ := hv
  rw [eval_power, eval_X, matrixX_fifth]

theorem eval_e1 (v : Word Generator) (hv : v ∈ e1) : Word.eval generatorImage v = 1 := by
  simp only [e1, List.mem_flatMap] at hv
  obtain ⟨r, _, s, _, hv⟩ := hv
  split at hv
  next hrs =>
    simp only [List.mem_flatMap, List.mem_map] at hv
    obtain ⟨m, _, n, _, rfl⟩ := hv
    simpa using commute_word (matrixX_commute r s hrs (coefficient m) (coefficient n))
  next => simp at hv

theorem eval_e2e3 (v : Word Generator) (hv : v ∈ e2e3) : Word.eval generatorImage v = 1 := by
  simp only [e2e3, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv
  obtain ⟨r, _, m, _, hv⟩ := hv
  rcases hv with rfl | rfl <;>
    rw [Word.eval_equation_eq_one_iff] <;>
    simp [coefficient_none, matrixX_commutator]

theorem eval_e4 (v : Word Generator) (hv : v ∈ e4) : Word.eval generatorImage v = 1 := by
  simp only [e4, List.mem_flatMap] at hv
  obtain ⟨r, _, s, _, hv⟩ := hv
  split at hv
  next hrs =>
    simp only [List.mem_flatMap, List.mem_map] at hv
    obtain ⟨m, _, n, _, l, _, rfl⟩ := hv
    simp only [Word.eval_commutator, eval_X, matrixX_commutator]
    exact commute_word (matrixX_commute (across r) s hrs (coefficient m * coefficient n) (coefficient l))
  next => simp at hv

theorem eval_shearComm (v : Word Generator) (hv : v ∈ shearComm) : Word.eval generatorImage v = 1 := by
  simp only [shearComm, List.mem_flatMap] at hv
  obtain ⟨r, _, s, _, hv⟩ := hv
  split at hv
  next hrs =>
    obtain rfl := List.mem_singleton.mp hv
    simpa using commute_word (matrixS_commute r s hrs)
  next => simp at hv

theorem eval_shearRoot (v : Word Generator) (hv : v ∈ shearRoot) : Word.eval generatorImage v = 1 := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
  rw [Word.eval_equation_eq_one_iff]
  simp [matrixS_commutator]

theorem eval_shearTorsion (v : Word Generator) (hv : v ∈ shearTorsion) :
    Word.eval generatorImage v = 1 := by
  simp only [shearTorsion, List.mem_singleton] at hv
  rw [hv, eval_power]
  simpa only [Word.eval_append, Word.eval_inverse, eval_shear, mul_assoc] using matrixS_torsion

theorem eval_actionRelations (v : Word Generator) (hv : v ∈ actionRelations) :
    Word.eval generatorImage v = 1 := by
  simp only [actionRelations, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨s, _, ε, _, r, _, m, _, rfl⟩ := hv
  rw [Word.eval_equation_eq_one_iff]
  exact eval_action s r ε m

theorem eval_negativeRecovery (v : Word Generator) (hv : v ∈ negativeRecovery) :
    Word.eval generatorImage v = 1 := by
  simp only [negativeRecovery, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨c, _, r, _, rfl⟩ := hv
  rw [Word.eval_equation_eq_one_iff]
  exact eval_recovery c r

theorem eval_rawRelator (v : Word Generator) (hv : v ∈ rawRelators) :
    Word.eval generatorImage v = 1 := by
  simp only [rawRelators, List.mem_append] at hv
  rcases hv with (((((((hv | hv) | hv) | hv) | hv) | hv) | hv) | hv) | hv
  · exact eval_e0 v hv
  · exact eval_e1 v hv
  · exact eval_e2e3 v hv
  · exact eval_e4 v hv
  · exact eval_shearComm v hv
  · exact eval_shearRoot v hv
  · exact eval_shearTorsion v hv
  · exact eval_actionRelations v hv
  · exact eval_negativeRecovery v hv

def representation : GroupQ →* ModelGroup :=
  PresentedGroup.toGroup (f := generatorImage) (rels := Compressor.relators) (by
    rintro _ ⟨v, hv, rfl⟩
    exact eval_rawRelator v hv)

theorem representation_ofGenerator (g : Generator) :
    representation (Compressor.ofGenerator g) = generatorImage g := PresentedGroup.toGroup.of _

end ThomGame.LaurentModel
