module

public import ThomGame.Groups.InvolutionPresentation
public import ThomGame.Groups.CentralTwist
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A complete finite derivation calculus for involution presentations

A state is an unsigned word together with a central parity. Its two kinds
of defining moves are deleting ss and replacing a defining word by its
specified parity. Congruence closure is an inductive, finite derivation.
The quotient is proved to be a group and identified with the existing
free-group presentation. No group equality is a premise of a basic move.
-/

@[expose] public section
namespace ThomGame.InvolutionDerivation

abbrev State (S : Type*) := FreeMonoid S × CentralTwist.C₂

variable {R S : Type*} (P : InvolutionPresentation R S)

def state (w : List S) (a : ZMod 2) : State S :=
  (FreeMonoid.ofList w, Multiplicative.ofAdd a)

theorem state_mul (u v : List S) (a b : ZMod 2) :
    state u a * state v b = state (u ++ v) (a + b) := rfl

theorem state_nil_zero : state ([] : List S) 0 = 1 := rfl

theorem parity_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

inductive Basic : State S → State S → Prop
  | square (s : S) : Basic (state [s, s] 0) (state [] 0)
  | equation (r : R) : Basic (state (P.word r) 0) (state [] (P.parity r))

def congruence : Con (State S) := conGen (Basic P)

abbrev Derives := ConGen.Rel (Basic P)

abbrev QuotientGroup := (congruence P).Quotient

def mk : State S →* QuotientGroup P := (congruence P).mk'

theorem mk_eq_iff (u v : State S) : mk P u = mk P v ↔ Derives P u v :=
  (congruence P).eq

def x (s : S) : QuotientGroup P := mk P (state [s] 0)

def j : QuotientGroup P := mk P (state [] 1)

theorem x_square (s : S) : x P s * x P s = 1 := by
  rw [x, ← map_mul]
  change mk P (state [s, s] 0) = mk P (state [] 0)
  exact (mk_eq_iff P _ _).mpr (ConGen.Rel.of _ _ (Basic.square s))

theorem j_square : j P * j P = 1 := by
  rw [j, ← map_mul]
  change mk P (state [] ((1 : ZMod 2) + 1)) = 1
  have hh : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  rw [hh, state_nil_zero, map_one]

theorem j_commutes_x (s : S) : Commute (j P) (x P s) := by
  change mk P (state [] 1) * mk P (state [s] 0) =
    mk P (state [s] 0) * mk P (state [] 1)
  rw [← map_mul, ← map_mul, state_mul, state_mul]
  simp

theorem mk_word (w : List S) : mk P (state w 0) = (w.map (x P)).prod := by
  induction w with
  | nil => exact map_one (mk P)
  | cons s w ih =>
    have he : state (s :: w) 0 = state [s] 0 * state w 0 := rfl
    rw [he, map_mul, ih]
    rfl

theorem mk_empty (a : ZMod 2) : mk P (state [] a) = if a = 1 then j P else 1 := by
  rcases parity_cases a with rfl | rfl
  · change mk P 1 = _
    simp
  · simp [j]

theorem word_product (r : R) :
    ((P.word r).map (x P)).prod = if P.parity r = 1 then j P else 1 := by
  rw [← mk_word, ← mk_empty]
  exact (mk_eq_iff P _ _).mpr (ConGen.Rel.of _ _ (Basic.equation r))

theorem isUnit_x (s : S) : IsUnit (x P s) :=
  ⟨⟨x P s, x P s, x_square P s, x_square P s⟩, rfl⟩

theorem isUnit_mk (w : FreeMonoid S) (c : CentralTwist.C₂) : IsUnit (mk P (w, c)) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    have hc : IsUnit c := ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, rfl⟩
    exact hc.map ((mk P).comp (MonoidHom.inr _ _))
  | of_mul s w ih =>
    have he : (FreeMonoid.of s * w, c) = (FreeMonoid.of s, 1) * (w, c) := by simp
    rw [he, map_mul]
    exact (isUnit_x P s).mul ih

theorem all_isUnit (g : QuotientGroup P) : IsUnit g := by
  obtain ⟨⟨w, c⟩, rfl⟩ := (congruence P).mk'_surjective g
  exact isUnit_mk P w c

noncomputable instance quotientGroup : Group (QuotientGroup P) := groupOfIsUnit (all_isUnit P)

def model : InvolutionPresentation.Model P (QuotientGroup P) where
  j := j P
  x := x P
  j_square := j_square P
  x_square := x_square P
  j_commutes := j_commutes_x P
  word_product := word_product P

noncomputable def fromPresented : InvolutionPresentation.GroupOf P →* QuotientGroup P := (model P).toHom

theorem fromPresented_J : fromPresented P (InvolutionPresentation.J P) = j P :=
  (model P).toHom_J

theorem fromPresented_x (s : S) : fromPresented P (InvolutionPresentation.x P s) = x P s :=
  (model P).toHom_x s

def eval : State S →* InvolutionPresentation.GroupOf P :=
  (FreeMonoid.lift (InvolutionPresentation.x P)).noncommCoprod
    (CentralTwist.involutionHom (InvolutionPresentation.J P) (InvolutionPresentation.J_sq P)) (by
      intro w c
      rcases CentralTwist.c₂_cases c with rfl | rfl
      · simp
      · rw [CentralTwist.involutionHom_j]
        exact (InvolutionPresentation.J_commutes P _).symm)

theorem eval_state (w : List S) (a : ZMod 2) :
    eval P (state w a) =
      (w.map (InvolutionPresentation.x P)).prod * if a = 1 then InvolutionPresentation.J P else 1 := by
  rcases parity_cases a with rfl | rfl <;>
    simp [eval, state, FreeMonoid.lift_ofList, CentralTwist.involutionHom]

theorem basic_sound {u v : State S} (h : Basic P u v) : eval P u = eval P v := by
  cases h with
  | square s => simp [eval_state, InvolutionPresentation.x_sq]
  | equation r => simp [eval_state, InvolutionPresentation.word_product]

theorem sound {u v : State S} (h : Derives P u v) : eval P u = eval P v := by
  induction h with
  | of u v h => exact basic_sound P h
  | refl u => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | mul h₁ h₂ ih₁ ih₂ => simp only [map_mul, ih₁, ih₂]

def toPresented : QuotientGroup P →* InvolutionPresentation.GroupOf P :=
  (congruence P).lift (eval P) (fun _ _ h => sound P h)

theorem toPresented_mk (u : State S) : toPresented P (mk P u) = eval P u := rfl

theorem toPresented_j : toPresented P (j P) = InvolutionPresentation.J P := by
  change eval P (state [] 1) = _
  simp [eval_state]

theorem toPresented_x (s : S) : toPresented P (x P s) = InvolutionPresentation.x P s := by
  change eval P (state [s] 0) = _
  simp [eval_state]

theorem toPresented_comp_fromPresented :
    (toPresented P).comp (fromPresented P) = MonoidHom.id (InvolutionPresentation.GroupOf P) := by
  apply InvolutionPresentation.hom_ext
  · change toPresented P (fromPresented P (InvolutionPresentation.J P)) = _
    rw [fromPresented_J, toPresented_j]
    rfl
  · intro s
    change toPresented P (fromPresented P (InvolutionPresentation.x P s)) = _
    rw [fromPresented_x, toPresented_x]
    rfl

theorem fromPresented_eval (u : State S) : fromPresented P (eval P u) = mk P u := by
  rcases u with ⟨w, c⟩
  obtain ⟨w, rfl⟩ := FreeMonoid.ofList.surjective w
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective c
  change fromPresented P (eval P (state w a)) = mk P (state w a)
  rw [eval_state, map_mul, map_list_prod, List.map_map]
  have hx : fromPresented P ∘ InvolutionPresentation.x P = x P := funext (fromPresented_x P)
  rw [hx, ← mk_word]
  have he : state w a = state w 0 * state [] a := by simp [state_mul]
  rw [he, map_mul, mk_empty]
  congr 1
  split_ifs <;> simp [fromPresented_J]

theorem fromPresented_comp_toPresented :
    (fromPresented P).comp (toPresented P) = MonoidHom.id (QuotientGroup P) := by
  apply MonoidHom.ext
  intro g
  obtain ⟨u, rfl⟩ := (congruence P).mk'_surjective g
  exact fromPresented_eval P u

noncomputable def presentedEquiv : InvolutionPresentation.GroupOf P ≃* QuotientGroup P where
  toFun := fromPresented P
  invFun := toPresented P
  left_inv := DFunLike.congr_fun (toPresented_comp_fromPresented P)
  right_inv := DFunLike.congr_fun (fromPresented_comp_toPresented P)
  map_mul' := (fromPresented P).map_mul

theorem eval_eq_iff_derives (u v : State S) : eval P u = eval P v ↔ Derives P u v := by
  constructor
  · intro h
    apply (mk_eq_iff P u v).mp
    rw [← fromPresented_eval, ← fromPresented_eval, h]
  · exact sound P

theorem word_eq_iff_derives (w : List S) (a : ZMod 2) :
    (w.map (InvolutionPresentation.x P)).prod = (if a = 1 then InvolutionPresentation.J P else 1) ↔
      Derives P (state w 0) (state [] a) := by
  simpa [eval_state] using eval_eq_iff_derives P (state w 0) (state [] a)

end ThomGame.InvolutionDerivation
