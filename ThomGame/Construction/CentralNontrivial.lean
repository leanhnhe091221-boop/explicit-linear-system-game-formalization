module

public import ThomGame.Groups.LaurentSeparation
public import ThomGame.Groups.LambdaHNNEquiv
public import ThomGame.Construction.InvolutionFaithful

/-!
# Infinite order of w and nontriviality of J in Λ and K

The Laurent representation discharges the strictness hypothesis in the
amalgam and HNN arguments. These theorems have no additional mathematical
assumption. Nontriviality in the final solution group Σ still needs the
separate injectivity of the wagon-wheel homomorphism K → Σ.
-/

@[expose] public section
namespace ThomGame.Double

theorem obstruction_infiniteOrder : ¬ IsOfFinOrder obstructionElement :=
  obstruction_not_isOfFinOrder Compressor.backwardConjugate_not_mem_positiveSubgroup

theorem obstruction_positive_power_ne_one (n : Nat) (hn : 0 < n) : obstructionElement ^ n ≠ 1 :=
  obstruction_pow_ne_one Compressor.backwardConjugate_not_mem_positiveSubgroup n hn

theorem toLambda_injective : Function.Injective toLambda :=
  Lambda.doubleToLambda_injective_of_obstruction_infinite obstruction_infiniteOrder

end ThomGame.Double

namespace ThomGame.Lambda

noncomputable def doubleHNNEquiv :
    GroupLambda ≃* CentralTwist.Extension Double.obstruction_infiniteOrder :=
  hnnEquiv Double.obstruction_infiniteOrder

theorem JElement_ne_one : JElement ≠ 1 :=
  JElement_ne_one_of_obstruction_infinite Double.obstruction_infiniteOrder

end ThomGame.Lambda

namespace ThomGame.Construction

theorem J_star_ne_one : J_star ≠ 1 :=
  fun h => Lambda.JElement_ne_one (J_star_eq_one_iff.mp h)

end ThomGame.Construction
