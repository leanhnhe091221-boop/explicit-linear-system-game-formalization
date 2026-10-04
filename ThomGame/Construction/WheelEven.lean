module

public import ThomGame.Construction.WheelHom
public import ThomGame.Construction.CentralNontrivial
public import ThomGame.Groups.SolutionEven

/-!
# The homogeneous square for the actual wheel homomorphism

Both vertical maps kill the original central involution. The bottom groups
are the genuine homogeneous presentations and each retains a fresh C₂.
The square commutes on every group element. Injectivity of the homogeneous
map and survival of J in Σ are still separate mathematical obligations.
-/

@[expose] public section
namespace ThomGame.Construction

abbrev HomogeneousInvolutionGroup :=
  InvolutionPresentation.GroupOf involutionPresentation.homogeneous

abbrev HomogeneousSigmaGroup :=
  SolutionGroup.GroupOf (SolutionGroup.homogeneous numberedSystem)

def involutionToWheelModJ : involutionPresentation.ModJ →* SolutionGroup.ModJ system :=
  involutionPresentation.centralDatum.map (SolutionGroup.centralDatum system)
    involutionToWheel involutionToWheel_J

theorem involutionToWheelModJ_quotient (g : InvolutionGroup) :
    involutionToWheelModJ (involutionPresentation.quotientJ g) =
      SolutionGroup.quotientJ system (involutionToWheel g) := rfl

def involutionToSigmaModJ : involutionPresentation.ModJ →* SolutionGroup.ModJ numberedSystem :=
  involutionPresentation.centralDatum.map (SolutionGroup.centralDatum numberedSystem)
    involutionToSigma involutionToSigma_J

theorem involutionToSigmaModJ_quotient (g : InvolutionGroup) :
    involutionToSigmaModJ (involutionPresentation.quotientJ g) =
      SolutionGroup.quotientJ numberedSystem (involutionToSigma g) := rfl

def homogeneousInvolutionToSigma : HomogeneousInvolutionGroup →* HomogeneousSigmaGroup :=
  (SolutionGroup.productToHomogeneous numberedSystem).comp
    ((involutionToSigmaModJ.prodMap (MonoidHom.id CentralTwist.C₂)).comp
      involutionPresentation.homogeneousToProduct)

theorem homogeneousInvolutionToSigma_J :
    homogeneousInvolutionToSigma (InvolutionPresentation.J involutionPresentation.homogeneous) =
      SolutionGroup.J (SolutionGroup.homogeneous numberedSystem) := by
  change SolutionGroup.productToHomogeneous numberedSystem
    ((involutionToSigmaModJ.prodMap (MonoidHom.id CentralTwist.C₂))
      (involutionPresentation.homogeneousToProduct
        (InvolutionPresentation.J involutionPresentation.homogeneous))) = _
  rw [InvolutionPresentation.homogeneousToProduct_J]
  change SolutionGroup.productToHomogeneous numberedSystem
    (involutionToSigmaModJ 1, CentralTwist.j) = _
  rw [map_one, SolutionGroup.productToHomogeneous_j]

theorem homogeneousInvolutionToSigma_x (s : Ordinary) :
    homogeneousInvolutionToSigma (InvolutionPresentation.x involutionPresentation.homogeneous s) =
      SolutionGroup.x (SolutionGroup.homogeneous numberedSystem) (colEquiv (.inl s)) := by
  change SolutionGroup.productToHomogeneous numberedSystem
    ((involutionToSigmaModJ.prodMap (MonoidHom.id CentralTwist.C₂))
      (involutionPresentation.homogeneousToProduct
        (InvolutionPresentation.x involutionPresentation.homogeneous s))) = _
  rw [InvolutionPresentation.homogeneousToProduct_x]
  change SolutionGroup.productToHomogeneous numberedSystem
    (involutionToSigmaModJ (involutionPresentation.quotientJ (ordinaryInvolution s)), 1) = _
  rw [involutionToSigmaModJ_quotient, involutionToSigma_x,
    SolutionGroup.productToHomogeneous_left, SolutionGroup.modJToHomogeneous_quotient]
  exact SolutionGroup.forgetParity_x numberedSystem (colEquiv (.inl s))

theorem homogeneous_square :
    (SolutionGroup.forgetParity numberedSystem).comp involutionToSigma =
      homogeneousInvolutionToSigma.comp involutionPresentation.forgetParity := by
  apply InvolutionPresentation.hom_ext
  · change SolutionGroup.forgetParity numberedSystem (involutionToSigma J_star) =
      homogeneousInvolutionToSigma (involutionPresentation.forgetParity J_star)
    rw [involutionToSigma_J]
    change SolutionGroup.forgetParity numberedSystem (SolutionGroup.J numberedSystem) =
      homogeneousInvolutionToSigma
        (involutionPresentation.forgetParity (InvolutionPresentation.J involutionPresentation))
    rw [SolutionGroup.forgetParity_J, InvolutionPresentation.forgetParity_J, map_one]
  · intro s
    change SolutionGroup.forgetParity numberedSystem (involutionToSigma (ordinaryInvolution s)) =
      homogeneousInvolutionToSigma
        (involutionPresentation.forgetParity (InvolutionPresentation.x involutionPresentation s))
    rw [involutionToSigma_x, InvolutionPresentation.forgetParity_x,
      homogeneousInvolutionToSigma_x]
    exact SolutionGroup.forgetParity_x numberedSystem (colEquiv (.inl s))

theorem involutionToSigma_kernel_of_homogeneous_injective
    (h : Function.Injective homogeneousInvolutionToSigma) (g : InvolutionGroup)
    (hg : involutionToSigma g = 1) : g = 1 ∨ g = J_star := by
  apply (involutionPresentation.forgetParity_eq_one_iff g).mp
  apply h
  have hh := DFunLike.congr_fun homogeneous_square g
  change SolutionGroup.forgetParity numberedSystem (involutionToSigma g) =
    homogeneousInvolutionToSigma (involutionPresentation.forgetParity g) at hh
  rw [hg, map_one] at hh
  exact hh.symm.trans (map_one homogeneousInvolutionToSigma).symm

theorem involutionToSigma_injective_of_homogeneous_injective
    (h : Function.Injective homogeneousInvolutionToSigma)
    (hJ : J_sigma ≠ 1) : Function.Injective involutionToSigma := by
  intro a b hab
  have hm : involutionToSigma (a * b⁻¹) = 1 := by simp [hab]
  rcases involutionToSigma_kernel_of_homogeneous_injective h (a * b⁻¹) hm with he | he
  · exact mul_inv_eq_one.mp he
  · exfalso
    rw [he, involutionToSigma_J] at hm
    exact hJ hm

theorem J_sigma_ne_one_of_reflects_triviality
    (h : J_sigma = 1 → J_star = 1) : J_sigma ≠ 1 :=
  fun hJ => J_star_ne_one (h hJ)

end ThomGame.Construction
