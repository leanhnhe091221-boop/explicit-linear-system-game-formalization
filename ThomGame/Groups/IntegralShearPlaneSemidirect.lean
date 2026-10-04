module

public import ThomGame.Groups.IntegralShearRootPlane
public import ThomGame.Groups.IntegerPlaneShearAction
public import Mathlib.Tactic.Group

/-! Realize the standard free-shear semidirect product in each rank-two corner of the shear group. -/

@[expose] public section
namespace ThomGame.IntegralShear

open Compressor

def freeRootPair (r : Root) : FreeGroup Bool →* ShearGroup :=
  FreeGroup.lift (fun b => if b then of (reverse r) else of r)

@[simp] theorem freeRootPair_of (r : Root) (b : Bool) :
    freeRootPair r (FreeGroup.of b) = if b then of (reverse r) else of r := FreeGroup.lift_apply_of

theorem rootPlaneHom_equivariant (r : Root) (w : FreeGroup Bool) (v : IntegerPlane.Group) :
    rootPlaneHom r (IntegerPlane.freeAction w v) =
      freeRootPair r w * rootPlaneHom r v * (freeRootPair r w)⁻¹ := by
  induction w using FreeGroup.induction_on generalizing v with
  | one => simp
  | of b =>
      cases b
      · exact (rootPlaneElement_conjugate_upper r v.toAdd).symm
      · exact (rootPlaneElement_conjugate_lower r v.toAdd).symm
  | inv_of b ih =>
      let w := FreeGroup.of b
      have h := ih (IntegerPlane.freeAction w⁻¹ v)
      have he : IntegerPlane.freeAction w (IntegerPlane.freeAction w⁻¹ v) = v := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [he] at h
      rw [map_inv]
      calc
        rootPlaneHom r (IntegerPlane.freeAction w⁻¹ v) =
            (freeRootPair r w)⁻¹ *
              (freeRootPair r w * rootPlaneHom r (IntegerPlane.freeAction w⁻¹ v) * (freeRootPair r w)⁻¹) *
              freeRootPair r w := by group
        _ = (freeRootPair r w)⁻¹ * rootPlaneHom r v * freeRootPair r w := by rw [← h]
        _ = _ := by simp only [w, map_inv, inv_inv]
  | mul w z ihw ihz =>
      rw [map_mul, MulAut.mul_apply, ihw, ihz, map_mul]
      group

def rootPlaneSemidirectHom (r : Root) : IntegerPlane.FreeShearProduct →* ShearGroup :=
  SemidirectProduct.lift (rootPlaneHom r) (freeRootPair r) (fun w => by
    ext v
    exact rootPlaneHom_equivariant r w v)

@[simp] theorem rootPlaneSemidirectHom_inl (r : Root) (v : IntegerPlane.Group) :
    rootPlaneSemidirectHom r (SemidirectProduct.inl v) = rootPlaneHom r v :=
  SemidirectProduct.lift_inl _ _ _ v

@[simp] theorem rootPlaneSemidirectHom_inr (r : Root) (w : FreeGroup Bool) :
    rootPlaneSemidirectHom r (SemidirectProduct.inr w) = freeRootPair r w :=
  SemidirectProduct.lift_inr _ _ _ w

theorem rootPlaneSemidirectHom_inl_injective (r : Root) :
    Function.Injective ((rootPlaneSemidirectHom r).comp SemidirectProduct.inl) := by
  intro v w h
  apply rootPlaneHom_injective r
  simpa only [MonoidHom.comp_apply, rootPlaneSemidirectHom_inl] using h

end ThomGame.IntegralShear
