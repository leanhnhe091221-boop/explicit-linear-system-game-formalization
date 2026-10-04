module

public import ThomGame.Groups.LaurentRelations
public import ThomGame.Groups.LaurentSupport
public import ThomGame.Groups.CompressorCompression

/-!
# Strict compression from the actual Laurent representation

The image of H lies in the image of GL₃ of the polynomial subring.
The (1,2) entry of the image of t⁻¹ h t is x₂ x₁⁻¹, whose exponent
is outside the nonnegative cone. Thus t⁻¹ h t is not in H.
-/

@[expose] public noncomputable section
namespace ThomGame.LaurentModel

open Compressor ElementaryMatrix

def polynomialEmbedding : Matrix.GeneralLinearGroup Axis polynomialSubring →* ModelGroup :=
  elementaryHom.comp (Matrix.GeneralLinearGroup.map polynomialSubring.subtype)

theorem polynomialEmbedding_entry (M : Matrix.GeneralLinearGroup Axis polynomialSubring) (i j : Axis) :
    (polynomialEmbedding M).left i j ∈ polynomialSubring := (M i j).property

theorem generatorImage_positive (g : Generator) (hg : positive g = true) :
    generatorImage g ∈ polynomialEmbedding.range := by
  cases g with
  | inl p =>
    rcases p with ⟨r, m⟩
    let p : polynomialSubring := ⟨coefficient m, positive_coefficient_mem r m hg⟩
    refine ⟨elem r p, ?_⟩
    change elementaryHom (Matrix.GeneralLinearGroup.map polynomialSubring.subtype (elem r p)) =
      matrixX r (coefficient m)
    rw [map_elem]
    rfl
  | inr s => simp [positive] at hg

theorem representation_positive (x : GroupQ) (hx : x ∈ positiveSubgroup) :
    representation x ∈ polynomialEmbedding.range := by
  have h : positiveSubgroup ≤ polynomialEmbedding.range.comap representation := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, hg, rfl⟩
    change representation (Compressor.ofGenerator g) ∈ polynomialEmbedding.range
    rw [representation_ofGenerator]
    exact generatorImage_positive g hg
  exact h hx

theorem representation_positive_entry (x : GroupQ) (hx : x ∈ positiveSubgroup) (i j : Axis) :
    (representation x).left i j ∈ polynomialSubring := by
  obtain ⟨M, hM⟩ := representation_positive x hx
  rw [← hM]
  exact polynomialEmbedding_entry M i j

theorem representation_backwardConjugate :
    representation backwardConjugate =
      matrixX root12 (monomial (exponentAction ((integralShear root12)⁻¹) (signedExponent 1 true))) := by
  simp only [backwardConjugate, hElement, tElement, map_mul, map_inv, representation_ofGenerator,
    generatorImage, matrixS]
  have h := integral_conjugate_matrixX ((integralShear root12)⁻¹) root12 (coefficient (some (1, true)))
  simpa only [map_inv, inv_inv, coefficient, coefficientExponent, ringAction_monomial] using h

theorem matrixX_root_entry (r : Root) (p : Laurent) :
    (matrixX r p).left (source r) (target r) = p := by
  change (elem r p : Matrix Axis Axis Laurent) (source r) (target r) = p
  rw [coe_elem]
  have hr : source r ≠ target r := r.property
  simp [hr]

theorem representation_backward_entry :
    (representation backwardConjugate).left 0 1 =
      monomial (exponentAction ((integralShear root12)⁻¹) (signedExponent 1 true)) := by
  rw [representation_backwardConjugate]
  exact matrixX_root_entry root12 _

end ThomGame.LaurentModel

namespace ThomGame.Compressor

/-- The separation statement is unconditional: it uses the constructed
Laurent matrix homomorphism and nonnegative polynomial support. -/
theorem backwardConjugate_not_mem_positiveSubgroup : backwardConjugate ∉ positiveSubgroup := by
  intro h
  have he := LaurentModel.representation_positive_entry backwardConjugate h 0 1
  rw [LaurentModel.representation_backward_entry] at he
  exact LaurentModel.backward_monomial_not_polynomial he

theorem h_not_mem_conjugate_positiveSubgroup :
    hElement ∉ positiveSubgroup.map (MulAut.conj tElement).toMonoidHom :=
  fun h => backwardConjugate_not_mem_positiveSubgroup (backwardConjugate_mem_iff.mpr h)

theorem t_conjugate_subgroup_lt :
    positiveSubgroup.map (MulAut.conj tElement).toMonoidHom < positiveSubgroup := by
  refine lt_of_le_of_ne t_conjugate_subgroup_le ?_
  intro he
  apply h_not_mem_conjugate_positiveSubgroup
  rw [he]
  exact h_mem_positiveSubgroup

end ThomGame.Compressor
