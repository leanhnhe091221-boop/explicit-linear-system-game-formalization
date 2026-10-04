module

public import ThomGame.Pictures.Diagram

/-!
# Reflection and bending the bottom boundary of a diagram

Reflection interchanges top and bottom. Nested cups and caps for an entire
word allow a rectangular diagram u → v to be closed along its bottom to a
single boundary u ++ reverse v. These operations preserve vertex sign and
size, with cups and caps contributing no relation vertices.
-/

@[expose] public section
namespace ThomGame.Pictures.Diagram

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}

def adjoint : {u v : List S} → Diagram P u v → Diagram P v u
  | _, _, .identity w => .identity w
  | _, _, .cap s => .cup s
  | _, _, .cup s => .cap s
  | _, _, .down r => .up r
  | _, _, .up r => .down r
  | _, _, .comp d e => e.adjoint.comp d.adjoint
  | _, _, .tensor d e => d.adjoint.tensor e.adjoint

theorem adjoint_adjoint (d : Diagram P u v) : d.adjoint.adjoint = d := by
  induction d <;> simp [adjoint, *]

theorem labels_adjoint_perm (d : Diagram P u v) : d.adjoint.labels.Perm d.labels := by
  induction d with
  | identity w => exact List.Perm.refl []
  | cap s => exact List.Perm.refl []
  | cup s => exact List.Perm.refl []
  | down r => exact List.Perm.refl [r]
  | up r => exact List.Perm.refl [r]
  | comp d e ihd ihe =>
    exact (ihe.append ihd).trans List.perm_append_comm
  | tensor d e ihd ihe => exact ihd.append ihe

theorem size_adjoint (d : Diagram P u v) : d.adjoint.size = d.size := d.labels_adjoint_perm.length_eq

theorem sign_adjoint (d : Diagram P u v) : d.adjoint.sign = d.sign :=
  (d.labels_adjoint_perm.map P.parity).sum_eq

def cupWord (P : InvolutionPresentation R S) : (w : List S) → Diagram P [] (w ++ w.reverse)
  | [] => .identity []
  | s :: w =>
      ((cup s).comp (((cupWord P w).context [s] [s]).cast (by simp) rfl)).cast rfl
        (by simp [List.reverse_cons, List.append_assoc])

theorem labels_cupWord (w : List S) : (cupWord P w).labels = [] := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [cupWord, labels_cast, labels, labels_context, ih]

theorem sign_cupWord (w : List S) : (cupWord P w).sign = 0 := by simp [sign, labels_cupWord]

theorem size_cupWord (w : List S) : (cupWord P w).size = 0 := by simp [size, labels_cupWord]

def capWord (P : InvolutionPresentation R S) (w : List S) : Diagram P (w ++ w.reverse) [] :=
  (cupWord P w).adjoint

theorem sign_capWord (w : List S) : (capWord P w).sign = 0 := by rw [capWord, sign_adjoint, sign_cupWord]

theorem size_capWord (w : List S) : (capWord P w).size = 0 := by rw [capWord, size_adjoint, size_cupWord]

def close (d : Diagram P u v) : Diagram P (u ++ v.reverse) [] :=
  (d.tensor (identity v.reverse)).comp (capWord P v)

theorem sign_close (d : Diagram P u v) : d.close.sign = d.sign := by
  rw [close, sign_comp, sign_tensor, sign_capWord]
  change d.sign + 0 + 0 = d.sign
  simp

theorem size_close (d : Diagram P u v) : d.close.size = d.size := by
  rw [close, size_comp, size_tensor, size_capWord]
  change d.size + 0 + 0 = d.size
  simp

theorem boundary_close (d : Diagram P u v) :
    ((u ++ v.reverse).map (InvolutionPresentation.x P)).prod =
      if d.sign = 1 then InvolutionPresentation.J P else 1 := by
  have h := d.close.boundary_eq
  simpa only [List.map_nil, List.prod_nil, one_mul, sign_close] using h

end ThomGame.Pictures.Diagram
