module

public import ThomGame.Analysis.MatrixStarBlocksTransport
public import ThomGame.Analysis.MatrixBoundedScaleTransport
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# The original block labels under unitary pullback

For B=u*Au the constructed block structure has exactly the same sizes
and multiplicities. In particular its actual scale is u*Delta_A u.
-/

@[expose] public section
namespace ThomGame.Analysis

open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {d : Nat} (A : StarSubalgebra ℂ (CMatrix d)) (U : UnitaryMatrix d)

noncomputable abbrev matrixUnitaryPullbackAlgebra : StarSubalgebra ℂ (CMatrix d) :=
  A.map (Unitary.conjStarAlgAut ℂ (CMatrix d) U).symm.toStarAlgHom

noncomputable def matrixUnitaryPullbackHom : matrixUnitaryPullbackAlgebra A U →⋆ₐ[ℂ] A :=
  StarAlgHom.codRestrict
    ((Unitary.conjStarAlgAut ℂ (CMatrix d) U).toStarAlgHom.comp (matrixUnitaryPullbackAlgebra A U).subtype)
    A (by
      rintro ⟨Y, X, hX, hXY⟩
      change Unitary.conjStarAlgAut ℂ (CMatrix d) U Y ∈ A
      rw [← hXY]
      change Unitary.conjStarAlgAut ℂ (CMatrix d) U
        ((Unitary.conjStarAlgAut ℂ (CMatrix d) U).symm X) ∈ A
      rw [StarAlgEquiv.apply_symm_apply]
      exact hX)

theorem matrixUnitaryPullbackHom_bijective : Function.Bijective (matrixUnitaryPullbackHom A U) := by
  constructor
  · intro X Y h
    apply Subtype.ext
    exact (Unitary.conjStarAlgAut ℂ (CMatrix d) U).injective (congrArg Subtype.val h)
  · intro X
    refine ⟨⟨(Unitary.conjStarAlgAut ℂ (CMatrix d) U).symm X, ⟨X, X.property, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (Unitary.conjStarAlgAut ℂ (CMatrix d) U).apply_symm_apply _

noncomputable def matrixUnitaryPullbackEquiv : matrixUnitaryPullbackAlgebra A U ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (matrixUnitaryPullbackHom A U) (matrixUnitaryPullbackHom_bijective A U)

theorem matrixUnitaryPullbackEquiv_coe (X : matrixUnitaryPullbackAlgebra A U) :
    (matrixUnitaryPullbackEquiv A U X : CMatrix d) = U.val * (X : CMatrix d) * U.valᴴ := rfl

theorem matrixUnitaryPullbackEquiv_trace (X : matrixUnitaryPullbackAlgebra A U) :
    Matrix.trace (X : CMatrix d) = Matrix.trace (matrixUnitaryPullbackEquiv A U X : CMatrix d) := by
  rw [matrixUnitaryPullbackEquiv_coe, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  rw [hU, Matrix.one_mul]

variable (P : MatrixSubalgebraStarBlocks A)

noncomputable abbrev matrixUnitaryPullbackBlocks : MatrixSubalgebraStarBlocks (matrixUnitaryPullbackAlgebra A U) :=
  matrixStarBlocksTransport A _ P (matrixUnitaryPullbackEquiv A U)

theorem matrixUnitaryPullbackBlocks_multiplicity (i : Fin P.count) :
    matrixStarRepresentationMultiplicity _ (matrixUnitaryPullbackBlocks A U P)
      (matrixUnitaryPullbackAlgebra A U).subtype i = matrixStarRepresentationMultiplicity A P A.subtype i :=
  matrixStarBlocksTransport_multiplicity A _ P (matrixUnitaryPullbackEquiv A U)
    (matrixUnitaryPullbackEquiv_trace A U) i

theorem matrixUnitaryPullbackBlocks_scale :
    matrixSubalgebraScale _ (matrixUnitaryPullbackBlocks A U P) =
      U.valᴴ * matrixSubalgebraScale A P * U.val := by
  have h := matrixStarBlocksTransport_scale A _ P (matrixUnitaryPullbackEquiv A U)
    (matrixUnitaryPullbackEquiv_trace A U)
  rw [matrixUnitaryPullbackEquiv_coe] at h
  have he := congrArg (fun X : CMatrix d => U.valᴴ * X * U.val) h
  have hU : U.valᴴ * U.val = 1 := U.prop.1
  have hc (X : CMatrix d) : U.valᴴ * (U.val * X * U.valᴴ) * U.val = X := by
    calc
      _ = (U.valᴴ * U.val) * X * (U.valᴴ * U.val) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  rw [hc] at he
  exact he

theorem matrixUnitaryPullbackBlocks_boundedScale (M : CMatrix d) (hM : M.PosDef)
    (hUM : U.val * M = M * U.val) :
    matrixBoundedScale (matrixSubalgebraScale _ (matrixUnitaryPullbackBlocks A U P)) M =
      U.valᴴ * matrixBoundedScale (matrixSubalgebraScale A P) M * U.val := by
  let e := (Unitary.conjStarAlgAut ℂ (CMatrix d) U).symm
  have hMmap : e M = M := by
    change U.valᴴ * M * U.val = M
    rw [Matrix.mul_assoc, ← hUM, ← Matrix.mul_assoc]
    have hi : U.valᴴ * U.val = 1 := U.prop.1
    rw [hi, Matrix.one_mul]
  have hTmap : e (matrixSubalgebraScale A P) =
      matrixSubalgebraScale _ (matrixUnitaryPullbackBlocks A U P) :=
    (matrixUnitaryPullbackBlocks_scale A U P).symm
  have he := matrixBoundedScale_map e.toStarAlgHom.toAlgHom (matrixSubalgebraScale A P) M
    ((matrixSubalgebraScale_posDef A P).add hM).isUnit
  change e (matrixBoundedScale (matrixSubalgebraScale A P) M) =
    matrixBoundedScale (e (matrixSubalgebraScale A P)) (e M) at he
  rw [hTmap, hMmap] at he
  exact he.symm

theorem matrixUnitaryPullback_contains_common (D : StarSubalgebra ℂ (CMatrix d))
    (hDA : D ≤ A) (hU : ∀ X ∈ D, U.val * X = X * U.val) : D ≤ matrixUnitaryPullbackAlgebra A U := by
  intro X hX
  refine ⟨X, hDA hX, ?_⟩
  change U.valᴴ * X * U.val = X
  rw [Matrix.mul_assoc, ← hU X hX, ← Matrix.mul_assoc]
  have hi : U.valᴴ * U.val = 1 := U.prop.1
  rw [hi, Matrix.one_mul]

end ThomGame.Analysis
