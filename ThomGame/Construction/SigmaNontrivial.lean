module

public import ThomGame.Construction.WheelCollapse

/-!
# The specified central involution of the actual solution group is nontrivial

A hypothetical trivial J gives a closed odd numbered Sigma graph whose
constellation rims are facial copies. The verified wheel collapse gives
a closed odd K diagram, contradicting the already proved nontrivial J_*.
This establishes central nontriviality, not the full wheel embedding or
the approximate-representation and quantum-value conclusions.
-/

@[expose] public section
namespace ThomGame.Construction

theorem J_sigma_ne_one : J_sigma ≠ 1 := by
  intro hj
  obtain ⟨H, hJ, he, hs, hf⟩ := J_sigma_eq_one_iff_all_facial_copies.mp hj
  let : IsEmpty H.Joint := hJ
  obtain ⟨d, hd⟩ := sigma_facial_copies_diagram H he hf
  exact involution_no_closed_odd_diagram ⟨d, hd.trans hs⟩

end ThomGame.Construction
