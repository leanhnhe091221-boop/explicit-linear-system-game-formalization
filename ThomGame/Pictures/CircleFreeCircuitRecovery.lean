module

public import ThomGame.Pictures.CircuitTrace
public import Mathlib.Data.Fintype.EquivFin

/-! # A smoothing trace with no discarded circles retains every original face orbit -/

@[expose] public section
namespace ThomGame.Pictures.Smoothing

variable {R S : Type*} {P : InvolutionPresentation R S} {u v : List S}
  {G H : PortGraph P u v} (t : Smoothing G H [])

theorem circuitEmbedding_surjective : Function.Surjective t.circuitEmbedding := by
  classical
  apply ((Fintype.bijective_iff_injective_and_card t.circuitEmbedding).mpr
    ⟨t.circuitEmbedding.injective, ?_⟩).2
  simpa only [List.length_nil, mul_zero, add_zero] using t.circuit_card

theorem every_circuit_meets_image (x : G.Dart) :
    ∃ y : H.Dart, G.circuitStep.SameCycle x (t.portEmbedding y) := by
  obtain ⟨q, hq⟩ := t.circuitEmbedding_surjective (G.circuit x)
  refine Quotient.inductionOn q (fun y h => ?_) hq
  refine ⟨y, (G.circuit_eq_iff x (t.portEmbedding y)).mp ?_⟩
  rw [← t.circuitEmbedding_circuit]
  exact h.symm

end ThomGame.Pictures.Smoothing
