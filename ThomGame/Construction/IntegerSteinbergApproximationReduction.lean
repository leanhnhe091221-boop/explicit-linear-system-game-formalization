module

public import ThomGame.Groups.IntegerSteinbergPresentation
public import ThomGame.Construction.CompressorShearSpectralNormalization

/-! A sufficient alternative group input: the actual integer Steinberg Kazhdan theorem. -/

@[expose] public section
namespace ThomGame.Construction

open Analysis

universe u

theorem shear_hasFiniteHilbertKazhdanSet_of_integerSteinberg
    (hSt : HasFiniteHilbertKazhdanSet.{u} IntegerSteinberg.St3Z) :
    HasFiniteHilbertKazhdanSet.{u} IntegralShear.ShearGroup :=
  hasFiniteHilbertKazhdanSet_surjective hSt IntegerSteinberg.toShear IntegerSteinberg.toShear_surjective

theorem sigmaApproximatelyTrivial_of_integerSteinberg
    (hSt : HasFiniteHilbertKazhdanSet.{0} IntegerSteinberg.St3Z) : SigmaApproximatelyTrivial :=
  sigmaApproximatelyTrivial_of_shear (shear_hasFiniteHilbertKazhdanSet_of_integerSteinberg hSt)

end ThomGame.Construction
