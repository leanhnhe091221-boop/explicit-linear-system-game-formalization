module

public import ThomGame.Construction.WheelWholeComponents
public import ThomGame.Pictures.WheelCollapse

/-!
# Actual numbered Sigma pictures collapse to K pictures

The generic collapse is instantiated with the paper's complete wheel
family and actual row/column numbering. Its recovered presentation is
proved equal to K's presentation, not merely related by a word count.
-/

@[expose] public section
namespace ThomGame.Construction

open Pictures PortGraph RibbonConnectivity

theorem wheelFamily_presentation : wheelFamily.presentation = involutionPresentation := by
  have hw : (fun r => List.ofFn (wheelFamily.letter r)) = wheelWord := by
    funext r
    exact List.ofFn_getElem
  exact congrArg (fun w => (⟨w, wheelFamily.parity⟩ : InvolutionPresentation WheelIndex Ordinary)) hw

theorem sigma_facial_copies_collapse (H : SigmaGraph [] []) [IsEmpty H.Joint]
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i) :
    ∃ K : PortGraph involutionPresentation [] [], IsEmpty K.Joint ∧
      eulerDefect K.pairing.perm K.circuitStep = 0 ∧ K.sign = H.sign := by
  rw [← wheelFamily_presentation]
  exact wheelFamily.exists_collapsed_graph rowEquiv colEquiv H
    (fun r => Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))
    (fun r a => hf (.inl r) a) (fun r j a => hf (.inr ⟨r, j⟩) a) he

theorem sigma_facial_copies_diagram (H : SigmaGraph [] []) [IsEmpty H.Joint]
    (he : eulerDefect H.pairing.perm H.circuitStep = 0)
    (hf : ∀ i : WheelCycleIndex, SigmaRimsFacialCopies H i) :
    ∃ d : Diagram involutionPresentation [] [], d.sign = H.sign := by
  rw [← wheelFamily_presentation]
  exact wheelFamily.exists_collapsed_diagram rowEquiv colEquiv H
    (fun r => Nat.le_trans (by decide : 3 ≤ 4) (wheelWord_length_ge_four r))
    (fun r a => hf (.inl r) a) (fun r j a => hf (.inr ⟨r, j⟩) a) he

end ThomGame.Construction
