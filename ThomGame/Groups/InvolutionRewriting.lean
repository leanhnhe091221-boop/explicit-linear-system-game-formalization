module

public import ThomGame.Groups.InvolutionDerivation
public import Mathlib.Logic.Relation

/-!
# Local unsigned-word rewriting with explicit parity

Each step inserts or deletes an adjacent square or one actual defining
word, in an explicit left/right context. A relation step changes the parity
by that relation's bit. Finite sequences of these local steps are proved
equivalent to equality in the actual involution group.
-/

@[expose] public section
namespace ThomGame.InvolutionDerivation

variable {R S : Type*} (P : InvolutionPresentation R S)

inductive Step : State S → State S → Prop
  | eraseSquare (l r : List S) (s : S) (a : ZMod 2) :
      Step (state (l ++ [s, s] ++ r) a) (state (l ++ r) a)
  | insertSquare (l r : List S) (s : S) (a : ZMod 2) :
      Step (state (l ++ r) a) (state (l ++ [s, s] ++ r) a)
  | eraseRelation (l r : List S) (i : R) (a : ZMod 2) :
      Step (state (l ++ P.word i ++ r) a) (state (l ++ r) (P.parity i + a))
  | insertRelation (l r : List S) (i : R) (a : ZMod 2) :
      Step (state (l ++ r) (P.parity i + a)) (state (l ++ P.word i ++ r) a)

abbrev Steps := Relation.ReflTransGen (Step P)

theorem state_cases (u : State S) : ∃ w a, u = state w a :=
  ⟨FreeMonoid.toList u.1, Multiplicative.toAdd u.2, rfl⟩

theorem Step.symm {u v : State S} (h : Step P u v) : Step P v u := by
  cases h with
  | eraseSquare l r s a => exact Step.insertSquare l r s a
  | insertSquare l r s a => exact Step.eraseSquare l r s a
  | eraseRelation l r i a => exact Step.insertRelation l r i a
  | insertRelation l r i a => exact Step.eraseRelation l r i a

instance step_symmetric : Std.Symm (Step P) where
  symm _ _ := Step.symm P

theorem Step.mul_left {u v : State S} (h : Step P u v) (z : State S) :
    Step P (z * u) (z * v) := by
  obtain ⟨w, a, rfl⟩ := state_cases z
  cases h with
  | eraseSquare l r s b =>
    simpa only [state_mul, List.append_assoc] using Step.eraseSquare (P := P) (w ++ l) r s (a + b)
  | insertSquare l r s b =>
    simpa only [state_mul, List.append_assoc] using Step.insertSquare (P := P) (w ++ l) r s (a + b)
  | eraseRelation l r i b =>
    simpa only [state_mul, List.append_assoc, add_left_comm] using
      Step.eraseRelation (P := P) (w ++ l) r i (a + b)
  | insertRelation l r i b =>
    simpa only [state_mul, List.append_assoc, add_left_comm] using
      Step.insertRelation (P := P) (w ++ l) r i (a + b)

theorem Step.mul_right {u v : State S} (h : Step P u v) (z : State S) :
    Step P (u * z) (v * z) := by
  obtain ⟨w, a, rfl⟩ := state_cases z
  cases h with
  | eraseSquare l r s b =>
    simpa only [state_mul, List.append_assoc] using Step.eraseSquare (P := P) l (r ++ w) s (b + a)
  | insertSquare l r s b =>
    simpa only [state_mul, List.append_assoc] using Step.insertSquare (P := P) l (r ++ w) s (b + a)
  | eraseRelation l r i b =>
    simpa only [state_mul, List.append_assoc, add_assoc] using
      Step.eraseRelation (P := P) l (r ++ w) i (b + a)
  | insertRelation l r i b =>
    simpa only [state_mul, List.append_assoc, add_assoc] using
      Step.insertRelation (P := P) l (r ++ w) i (b + a)

theorem steps_mul_left {u v : State S} (h : Steps P u v) (z : State S) :
    Steps P (z * u) (z * v) :=
  Relation.ReflTransGen.lift (fun t => z * t) (fun _ _ h => Step.mul_left P h z) _ _ h

theorem steps_mul_right {u v : State S} (h : Steps P u v) (z : State S) :
    Steps P (u * z) (v * z) :=
  Relation.ReflTransGen.lift (fun t => t * z) (fun _ _ h => Step.mul_right P h z) _ _ h

theorem steps_mul {u v w z : State S} (h₁ : Steps P u v) (h₂ : Steps P w z) :
    Steps P (u * w) (v * z) :=
  (steps_mul_right P h₁ w).trans (steps_mul_left P h₂ v)

theorem basic_steps {u v : State S} (h : Basic P u v) : Steps P u v := by
  apply Relation.ReflTransGen.single
  cases h with
  | square s =>
    simpa only [List.nil_append, List.append_nil] using Step.eraseSquare (P := P) [] [] s 0
  | equation i =>
    simpa only [List.nil_append, List.append_nil, add_zero] using Step.eraseRelation (P := P) [] [] i 0

theorem derives_steps {u v : State S} (h : Derives P u v) : Steps P u v := by
  induction h with
  | of u v h => exact basic_steps P h
  | refl u => exact Relation.ReflTransGen.refl
  | symm h ih => exact symm_of (Steps P) ih
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul h₁ h₂ ih₁ ih₂ => exact steps_mul P ih₁ ih₂

theorem derives_context {u v : State S} (h : Derives P u v) (l r : State S) :
    Derives P (l * u * r) (l * v * r) :=
  ConGen.Rel.mul (ConGen.Rel.mul (ConGen.Rel.refl l) h) (ConGen.Rel.refl r)

theorem Step.derives {u v : State S} (h : Step P u v) : Derives P u v := by
  cases h with
  | eraseSquare l r s a =>
    have hh := derives_context P (ConGen.Rel.of _ _ (Basic.square s)) (state l 0) (state r a)
    simpa only [state_mul, zero_add, List.append_nil, List.nil_append] using hh
  | insertSquare l r s a =>
    have hh := derives_context P (ConGen.Rel.of _ _ (Basic.square s)) (state l 0) (state r a)
    apply ConGen.Rel.symm
    simpa only [state_mul, zero_add, List.append_nil, List.nil_append] using hh
  | eraseRelation l r i a =>
    have hh := derives_context P (ConGen.Rel.of _ _ (Basic.equation i)) (state l 0) (state r a)
    simpa only [state_mul, zero_add, List.append_nil, List.nil_append] using hh
  | insertRelation l r i a =>
    have hh := derives_context P (ConGen.Rel.of _ _ (Basic.equation i)) (state l 0) (state r a)
    apply ConGen.Rel.symm
    simpa only [state_mul, zero_add, List.append_nil, List.nil_append] using hh

theorem steps_derives {u v : State S} (h : Steps P u v) : Derives P u v := by
  induction h with
  | refl => exact ConGen.Rel.refl _
  | tail h hs ih => exact ConGen.Rel.trans ih (Step.derives P hs)

theorem derives_iff_steps (u v : State S) : Derives P u v ↔ Steps P u v :=
  ⟨derives_steps P, steps_derives P⟩

theorem eval_eq_iff_steps (u v : State S) : eval P u = eval P v ↔ Steps P u v :=
  (eval_eq_iff_derives P u v).trans (derives_iff_steps P u v)

theorem word_eq_iff_steps (w : List S) (a : ZMod 2) :
    (w.map (InvolutionPresentation.x P)).prod = (if a = 1 then InvolutionPresentation.J P else 1) ↔
      Steps P (state w 0) (state [] a) :=
  (word_eq_iff_derives P w a).trans (derives_iff_steps P _ _)

end ThomGame.InvolutionDerivation
