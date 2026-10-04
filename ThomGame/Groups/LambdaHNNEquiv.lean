module

public import ThomGame.Groups.LambdaHNN
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Identification with the HNN extension

The equivalence fixes the entire double, the named central involution,
and the stable letter. The infinite-order hypothesis remains explicit.
-/

@[expose] public section
namespace ThomGame.Lambda

def centralInvolutionHom : CentralTwist.C₂ →* GroupLambda :=
  CentralTwist.involutionHom JElement JElement_square

theorem centralInvolutionHom_j : centralInvolutionHom CentralTwist.j = JElement :=
  CentralTwist.involutionHom_j JElement JElement_square

def baseToLambda : Double.GroupD × CentralTwist.C₂ →* GroupLambda :=
  Double.toLambda.noncommCoprod centralInvolutionHom (by
    intro d c
    rcases CentralTwist.c₂_cases c with rfl | rfl
    · simp
    · rw [centralInvolutionHom_j]
      exact (JElement_central _).symm)

theorem baseToLambda_apply (d : Double.GroupD) (c : CentralTwist.C₂) :
    baseToLambda (d, c) = Double.toLambda d * centralInvolutionHom c := rfl

theorem baseToLambda_double (d : Double.GroupD) : baseToLambda (d, 1) = Double.toLambda d := by
  simp [baseToLambda_apply]

theorem baseToLambda_j : baseToLambda (1, CentralTwist.j) = JElement := by
  simp [baseToLambda_apply, centralInvolutionHom_j]

theorem baseToLambda_twist_coordinates :
    (MulAut.conj stableElement).toMonoidHom.comp
        (baseToLambda.comp (CentralTwist.coordinates Double.obstructionElement)) =
      baseToLambda.comp ((CentralTwist.coordinates Double.obstructionElement).comp
        CentralTwist.coordinateTwist.toMonoidHom) := by
  apply CentralTwist.coordinates_hom_ext
  · have hj : centralInvolutionHom (Multiplicative.ofAdd 1) = JElement := centralInvolutionHom_j
    simpa [MonoidHom.comp_apply, CentralTwist.coordinates, CentralTwist.coordinateTwist,
      CentralTwist.parity, baseToLambda_apply, hj,
      Double.toLambda_obstruction] using stable_conjugates_obstruction
  · have h : stableElement * JElement * stableElement⁻¹ = JElement := by
      rw [← (JElement_central stableElement).eq]
      simp [mul_assoc]
    simpa [MonoidHom.comp_apply, CentralTwist.coordinates, CentralTwist.coordinateTwist,
      CentralTwist.parity, baseToLambda_apply, centralInvolutionHom_j] using h

variable (hw : ¬ IsOfFinOrder Double.obstructionElement)

theorem baseToLambda_twist (a : (CentralTwist.coordinates Double.obstructionElement).range) :
    stableElement * baseToLambda a = baseToLambda (CentralTwist.twist hw a) * stableElement := by
  obtain ⟨c, rfl⟩ := (CentralTwist.coordinateEquiv hw).surjective a
  have h := DFunLike.congr_fun baseToLambda_twist_coordinates c
  rw [CentralTwist.twist_coordinateEquiv]
  exact mul_inv_eq_iff_eq_mul.mp h

noncomputable def fromHNN : CentralTwist.Extension hw →* GroupLambda :=
  HNNExtension.lift baseToLambda stableElement (baseToLambda_twist hw)

theorem fromHNN_base (a : Double.GroupD × CentralTwist.C₂) :
    fromHNN hw (CentralTwist.base hw a) = baseToLambda a :=
  HNNExtension.lift_of _ _ _ a

theorem fromHNN_stable : fromHNN hw (CentralTwist.stable hw) = stableElement :=
  HNNExtension.lift_t _ _ _

theorem fromHNN_comp_toHNN : (fromHNN hw).comp (toHNN hw) = MonoidHom.id GroupLambda := by
  apply hom_ext
  · apply MonoidHom.ext
    intro d
    change fromHNN hw (toHNN hw (Double.toLambda d)) = Double.toLambda d
    rw [toHNN_double, fromHNN_base, baseToLambda_double]
  · change fromHNN hw (toHNN hw JElement) = JElement
    rw [toHNN_J, fromHNN_base, baseToLambda_j]
  · change fromHNN hw (toHNN hw stableElement) = stableElement
    rw [toHNN_z, fromHNN_stable]

theorem toHNN_comp_fromHNN :
    (toHNN hw).comp (fromHNN hw) = MonoidHom.id (CentralTwist.Extension hw) := by
  apply HNNExtension.hom_ext
  · apply MonoidHom.ext
    rintro ⟨d, c⟩
    change toHNN hw (fromHNN hw (CentralTwist.base hw (d, c))) = CentralTwist.base hw (d, c)
    rw [fromHNN_base, baseToLambda_apply, map_mul, toHNN_double]
    rcases CentralTwist.c₂_cases c with rfl | rfl
    · simp
    · rw [centralInvolutionHom_j, toHNN_J, ← map_mul]
      simp
  · change toHNN hw (fromHNN hw (CentralTwist.stable hw)) = CentralTwist.stable hw
    rw [fromHNN_stable, toHNN_z]

noncomputable def hnnEquiv : GroupLambda ≃* CentralTwist.Extension hw where
  toFun := toHNN hw
  invFun := fromHNN hw
  left_inv := DFunLike.congr_fun (fromHNN_comp_toHNN hw)
  right_inv := DFunLike.congr_fun (toHNN_comp_fromHNN hw)
  map_mul' := (toHNN hw).map_mul

theorem hnnEquiv_J : hnnEquiv hw JElement = CentralTwist.base hw (1, CentralTwist.j) := toHNN_J hw
theorem hnnEquiv_z : hnnEquiv hw stableElement = CentralTwist.stable hw := toHNN_z hw
theorem hnnEquiv_double (d : Double.GroupD) :
    hnnEquiv hw (Double.toLambda d) = CentralTwist.base hw (d, 1) := toHNN_double hw d

end ThomGame.Lambda
