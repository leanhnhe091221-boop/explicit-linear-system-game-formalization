module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Group.Equiv.Basic

/-! The actual left and right regular Hilbert-space operators. -/

@[expose] public section
namespace ThomGame.Quantum

open scoped Classical

noncomputable abbrev GroupHilbert (G : Type*) := lp (fun _ : G => ℂ) 2

namespace GroupHilbert

variable {G : Type*}

noncomputable def permute (e : G ≃ G) : GroupHilbert G →ₗᵢ[ℂ] GroupHilbert G where
  toFun f := ⟨fun x => f (e.symm x), by
    apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
    exact e.symm.summable_iff.mpr ((memℓp_gen_iff (p := 2) (by norm_num)).mp f.property)⟩
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun x => ‖f x‖ ^ (2 : ENNReal).toReal)

theorem permute_apply (e : G ≃ G) (f : GroupHilbert G) (x : G) :
    permute e f x = f (e.symm x) := rfl

noncomputable def delta (g : G) : GroupHilbert G := lp.single 2 g 1

theorem permute_delta (e : G ≃ G) (g : G) : permute e (delta g) = delta (e g) := by
  classical
  ext x
  simp only [permute_apply, delta, lp.single_apply, Pi.single_apply]
  have h : e.symm x = g ↔ x = e g := e.symm_apply_eq
  simp only [h]

theorem delta_norm (g : G) : ‖delta g‖ = 1 := by
  rw [delta, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  norm_num

theorem delta_inner (g h : G) : inner ℂ (delta g) (delta h) = if g = h then 1 else 0 := by
  classical
  simp [delta, lp.inner_single_left, lp.single_apply, Pi.single_apply]

variable [Group G]

noncomputable def left (g : G) : GroupHilbert G →L[ℂ] GroupHilbert G :=
  (permute (Equiv.mulLeft g)).toContinuousLinearMap

noncomputable def right (g : G) : GroupHilbert G →L[ℂ] GroupHilbert G :=
  (permute (Equiv.mulRight g⁻¹)).toContinuousLinearMap

theorem left_apply (g : G) (f : GroupHilbert G) (h : G) : left g f h = f (g⁻¹ * h) := rfl

theorem right_apply (g : G) (f : GroupHilbert G) (h : G) : right g f h = f (h * g) := by
  simp [right, permute_apply]

theorem left_one : left (1 : G) = 1 := by ext f h; simp [left_apply]

theorem right_one : right (1 : G) = 1 := by ext f h; simp [right_apply]

theorem left_mul (g h : G) : left (g * h) = left g * left h := by
  ext f k
  simp [left_apply, mul_inv_rev, mul_assoc]

theorem right_mul (g h : G) : right (g * h) = right g * right h := by
  ext f k
  simp [right_apply, mul_assoc]

theorem left_right_commute (g h : G) : Commute (left g) (right h) := by
  ext f k
  simp [left_apply, right_apply, mul_assoc]

theorem left_delta (g h : G) : left g (delta h) = delta (g * h) :=
  permute_delta (Equiv.mulLeft g) h

theorem right_delta (g h : G) : right g (delta h) = delta (h * g⁻¹) :=
  permute_delta (Equiv.mulRight g⁻¹) h

theorem left_inner (g : G) (ξ ζ : GroupHilbert G) :
    inner ℂ (left g ξ) (left g ζ) = inner ℂ ξ ζ :=
  (permute (Equiv.mulLeft g)).inner_map_map ξ ζ

theorem right_inner (g : G) (ξ ζ : GroupHilbert G) :
    inner ℂ (right g ξ) (right g ζ) = inner ℂ ξ ζ :=
  (permute (Equiv.mulRight g⁻¹)).inner_map_map ξ ζ

theorem left_square (g : G) (hg : g * g = 1) : left g * left g = 1 := by
  rw [← left_mul, hg, left_one]

theorem right_square (g : G) (hg : g * g = 1) : right g * right g = 1 := by
  rw [← right_mul, hg, right_one]

theorem left_selfAdjoint (g : G) (hg : g * g = 1) : IsSelfAdjoint (left g) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro ξ ζ
  have hz : left g (left g ζ) = ζ := by rw [← mul_apply_eq_comp, left_square g hg, one_apply_eq_self]
  change inner ℂ (left g ξ) ζ = inner ℂ ξ (left g ζ)
  calc
    inner ℂ (left g ξ) ζ = inner ℂ (left g ξ) (left g (left g ζ)) := by rw [hz]
    _ = inner ℂ ξ (left g ζ) := left_inner g ξ (left g ζ)

theorem right_selfAdjoint (g : G) (hg : g * g = 1) : IsSelfAdjoint (right g) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro ξ ζ
  have hz : right g (right g ζ) = ζ := by rw [← mul_apply_eq_comp, right_square g hg, one_apply_eq_self]
  change inner ℂ (right g ξ) ζ = inner ℂ ξ (right g ζ)
  calc
    inner ℂ (right g ξ) ζ = inner ℂ (right g ξ) (right g (right g ζ)) := by rw [hz]
    _ = inner ℂ ξ (right g ζ) := right_inner g ξ (right g ζ)

end GroupHilbert
end ThomGame.Quantum
