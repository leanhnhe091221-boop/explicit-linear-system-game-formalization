module

public import ThomGame.Groups.CentralTwist
public import ThomGame.Groups.LambdaUniversal
public import ThomGame.Groups.DoubleNormalForm

/-!
# The HNN model of the actual Λ presentation

The infinite order of the actual double word is an explicit hypothesis.
In particular, the nontriviality results below do not yet discharge the
Laurent separation argument needed to establish that hypothesis.
-/

@[expose] public section
namespace ThomGame.Lambda

variable (hw : ¬ IsOfFinOrder Double.obstructionElement)

noncomputable def hnnModel : Model (CentralTwist.Extension hw) where
  d := (CentralTwist.base hw).comp (MonoidHom.inl _ _)
  j := CentralTwist.base hw (1, CentralTwist.j)
  z := CentralTwist.stable hw
  j_square := CentralTwist.base_j_square hw
  j_commutes x := by
    change CentralTwist.base hw (1, CentralTwist.j) * CentralTwist.base hw (x, 1) =
      CentralTwist.base hw (x, 1) * CentralTwist.base hw (1, CentralTwist.j)
    simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  j_z := by
    exact ((mul_inv_eq_iff_eq_mul.mp (CentralTwist.stable_j hw))).symm
  conjugate_w := by
    change CentralTwist.stable hw * CentralTwist.base hw (Double.obstructionElement, 1) *
      (CentralTwist.stable hw)⁻¹ = _
    rw [CentralTwist.stable_w]
    simp only [← map_mul, MonoidHom.comp_apply, MonoidHom.inl_apply,
      Prod.mk_mul_mk, one_mul, mul_one]

noncomputable def toHNN : GroupLambda →* CentralTwist.Extension hw := (hnnModel hw).toHom

theorem toHNN_J : toHNN hw JElement = CentralTwist.base hw (1, CentralTwist.j) :=
  (hnnModel hw).toHom_J

theorem toHNN_z : toHNN hw stableElement = CentralTwist.stable hw :=
  (hnnModel hw).toHom_z

theorem toHNN_double (x : Double.GroupD) :
    toHNN hw (Double.toLambda x) = CentralTwist.base hw (x, 1) :=
  (hnnModel hw).toHom_double x

include hw in
theorem JElement_ne_one_of_obstruction_infinite : JElement ≠ 1 := by
  intro h
  apply CentralTwist.base_j_ne_one hw
  rw [← toHNN_J, h, map_one]

include hw in
theorem doubleToLambda_injective_of_obstruction_infinite : Function.Injective Double.toLambda := by
  intro x y h
  have hp := congrArg (toHNN hw) h
  rw [toHNN_double, toHNN_double] at hp
  exact congrArg Prod.fst (CentralTwist.base_injective hw hp)

theorem JElement_ne_one_of_strict_compression
    (hstrict : Compressor.backwardConjugate ∉ Compressor.positiveSubgroup) : JElement ≠ 1 :=
  JElement_ne_one_of_obstruction_infinite (Double.obstruction_not_isOfFinOrder hstrict)

theorem doubleToLambda_injective_of_strict_compression
    (hstrict : Compressor.backwardConjugate ∉ Compressor.positiveSubgroup) :
    Function.Injective Double.toLambda :=
  doubleToLambda_injective_of_obstruction_infinite (Double.obstruction_not_isOfFinOrder hstrict)

end ThomGame.Lambda
