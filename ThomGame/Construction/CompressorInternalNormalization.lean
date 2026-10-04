module

public import ThomGame.Analysis.MatrixThomGroupNormalization
public import ThomGame.Groups.CompressorGeneration
public import ThomGame.Groups.DoubleCentralizer

/-!
# The specified compressor obstruction from actual internal commutants

The six specified shears compress the actual positive subgroup and,
together with it, generate Q. Thus the proved analytic normalization
applies to every homomorphism of this Q, including noninjective ones.
In the specified Lambda group it kills the actual central generator.
-/

@[expose] public section
namespace ThomGame.Construction

open Analysis Filter

theorem compressor_matrixCentralizer_normalized {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)] (L : Ultrafilter ι)
    (φ : Compressor.GroupQ →* unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (hH : ∃ A : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter ι))
    (hQ : ∃ D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant φ ⊤ = matrixInternalQuotient dims D (L : Filter ι)) :
    ∀ g, φ g ∈ Subgroup.normalizer
      (Subgroup.centralizer (Set.range (φ.comp Compressor.positiveSubgroup.subtype)) :
        Set (unitary (MatrixTracialQuotient dims (L : Filter ι)))) := by
  let e := (Fintype.equivFin Compressor.Root).symm
  let t := fun j => Compressor.shearElement (e j)
  have hrange : Set.range t = Set.range Compressor.shearElement := by
    ext g
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨e.symm r, congrArg Compressor.shearElement (e.apply_symm_apply r)⟩
  have hgen : Subgroup.closure ((Compressor.positiveSubgroup : Set Compressor.GroupQ) ∪ Set.range t) = ⊤ := by
    rw [hrange]
    exact Compressor.withShears_eq_top
  exact matrixThom_groupCentralizer_normalized dims L Compressor.positiveSubgroup t hgen
    (fun j => Compressor.shear_compresses (e j)) φ hH hQ

theorem lambda_matrix_J_eq_one_of_internal_commutants {ι : Type*}
    (dims : ι → Nat) [∀ n, NeZero (dims n)] (L : Ultrafilter ι)
    (φ : Lambda.GroupLambda →* unitary (MatrixTracialQuotient dims (L : Filter ι)))
    (hH : ∃ A : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant ((φ.comp Double.toLambda).comp (Double.copyHom false))
        Compressor.positiveSubgroup = matrixInternalQuotient dims A (L : Filter ι))
    (hQ : ∃ D : (n : ι) → StarSubalgebra ℂ (CMatrix (dims n)),
      unitaryRepresentationCommutant ((φ.comp Double.toLambda).comp (Double.copyHom false)) ⊤ =
        matrixInternalQuotient dims D (L : Filter ι)) : φ Lambda.JElement = 1 := by
  apply Lambda.hom_J_eq_one_of_normalizes_centralizer
  have hn := compressor_matrixCentralizer_normalized dims L
    ((φ.comp Double.toLambda).comp (Double.copyHom false)) hH hQ Compressor.tElement
  simpa only [Compressor.tElement, MonoidHom.comp_apply, Double.copy_t₁,
    Double.imageCentralizer, Double.positiveHom, MonoidHom.comp_assoc] using hn

end ThomGame.Construction
