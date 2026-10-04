module

public import ThomGame.Analysis.ShearWordCertificates

/-! Ten-step Weyl braid derivations, checked against signed defining relators.
The generator order is (12,13,21,23,31,32), each followed by its inverse. -/

@[expose] public section
namespace ThomGame.Analysis

open Compressor

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shearEncodedWord (w : List ℕ) : Word Root :=
  w.map (fun a => (roots.getD (a / 2) root12, a % 2 == 0))

theorem shearWeyl0 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [0, 5, 0]))
    (FreeGroup.mk (shearEncodedWord [5, 0, 5])) 30 := by
  let C0 := shearRootCertificate (roots.getD 4 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [0, 5, 0]))
      (FreeGroup.mk (shearEncodedWord [9, 0, 8, 10, 5, 0])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [5, 0]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 5 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 0, 8, 10, 5, 0]))
      (FreeGroup.mk (shearEncodedWord [9, 0, 5, 10, 0])) 3 :=
    R1.contextual_sound (shearEncodedWord [9, 0])
      (shearEncodedWord [10, 5, 0]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 1 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 0, 5, 10, 0]))
      (FreeGroup.mk (shearEncodedWord [9, 0, 5, 2, 10, 3])) 3 :=
    R2.contextual_sound (shearEncodedWord [9, 0, 5])
      (shearEncodedWord [0]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 2 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 0, 5, 2, 10, 3]))
      (FreeGroup.mk (shearEncodedWord [9, 0, 2, 7, 5, 10, 3])) 3 :=
    R3.contextual_sound (shearEncodedWord [9, 0])
      (shearEncodedWord [2, 10, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 0 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 0, 2, 7, 5, 10, 3]))
      (FreeGroup.mk (shearEncodedWord [9, 7, 0, 5, 10, 3])) 3 :=
    R4.contextual_sound (shearEncodedWord [9])
      (shearEncodedWord [2, 7, 5, 10, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 5 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 7, 0, 5, 10, 3]))
      (FreeGroup.mk (shearEncodedWord [9, 7, 0, 8, 10, 5, 3])) 3 :=
    R5.contextual_sound (shearEncodedWord [9, 7, 0])
      (shearEncodedWord [10, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 4 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 7, 0, 8, 10, 5, 3]))
      (FreeGroup.mk (shearEncodedWord [9, 7, 8, 0, 5, 3])) 3 :=
    R6.contextual_sound (shearEncodedWord [9, 7])
      (shearEncodedWord [8, 10, 5, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 3 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 7, 8, 0, 5, 3]))
      (FreeGroup.mk (shearEncodedWord [5, 7, 0, 5, 3])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [7, 8, 0, 5, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 0 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 7, 0, 5, 3]))
      (FreeGroup.mk (shearEncodedWord [5, 0, 7, 2, 5, 3])) 3 :=
    R8.contextual_sound (shearEncodedWord [5])
      (shearEncodedWord [0, 5, 3]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 2 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 0, 7, 2, 5, 3]))
      (FreeGroup.mk (shearEncodedWord [5, 0, 5])) 3 :=
    R9.contextual_sound (shearEncodedWord [5, 0])
      (shearEncodedWord [2, 5, 3]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

theorem shearWeyl1 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [2, 9, 2]))
    (FreeGroup.mk (shearEncodedWord [9, 2, 9])) 30 := by
  let C0 := shearRootCertificate (roots.getD 2 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [2, 9, 2]))
      (FreeGroup.mk (shearEncodedWord [5, 2, 4, 6, 9, 2])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [9, 2]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 3 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 2, 4, 6, 9, 2]))
      (FreeGroup.mk (shearEncodedWord [5, 2, 9, 6, 2])) 3 :=
    R1.contextual_sound (shearEncodedWord [5, 2])
      (shearEncodedWord [6, 9, 2]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 0 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 2, 9, 6, 2]))
      (FreeGroup.mk (shearEncodedWord [5, 2, 9, 0, 6, 1])) 3 :=
    R2.contextual_sound (shearEncodedWord [5, 2, 9])
      (shearEncodedWord [2]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 4 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 2, 9, 0, 6, 1]))
      (FreeGroup.mk (shearEncodedWord [5, 2, 0, 11, 9, 6, 1])) 3 :=
    R3.contextual_sound (shearEncodedWord [5, 2])
      (shearEncodedWord [0, 6, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 1 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 2, 0, 11, 9, 6, 1]))
      (FreeGroup.mk (shearEncodedWord [5, 11, 2, 9, 6, 1])) 3 :=
    R4.contextual_sound (shearEncodedWord [5])
      (shearEncodedWord [0, 11, 9, 6, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 3 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 11, 2, 9, 6, 1]))
      (FreeGroup.mk (shearEncodedWord [5, 11, 2, 4, 6, 9, 1])) 3 :=
    R5.contextual_sound (shearEncodedWord [5, 11, 2])
      (shearEncodedWord [6, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 2 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 11, 2, 4, 6, 9, 1]))
      (FreeGroup.mk (shearEncodedWord [5, 11, 4, 2, 9, 1])) 3 :=
    R6.contextual_sound (shearEncodedWord [5, 11])
      (shearEncodedWord [4, 6, 9, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 5 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [5, 11, 4, 2, 9, 1]))
      (FreeGroup.mk (shearEncodedWord [9, 11, 2, 9, 1])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [11, 4, 2, 9, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 1 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 11, 2, 9, 1]))
      (FreeGroup.mk (shearEncodedWord [9, 2, 11, 0, 9, 1])) 3 :=
    R8.contextual_sound (shearEncodedWord [9])
      (shearEncodedWord [2, 9, 1]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 4 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [9, 2, 11, 0, 9, 1]))
      (FreeGroup.mk (shearEncodedWord [9, 2, 9])) 3 :=
    R9.contextual_sound (shearEncodedWord [9, 2])
      (shearEncodedWord [0, 9, 1]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

theorem shearWeyl2 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [4, 1, 4]))
    (FreeGroup.mk (shearEncodedWord [1, 4, 1])) 30 := by
  let C0 := shearRootCertificate (roots.getD 5 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [4, 1, 4]))
      (FreeGroup.mk (shearEncodedWord [11, 4, 10, 8, 1, 4])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [1, 4]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 4 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 4, 10, 8, 1, 4]))
      (FreeGroup.mk (shearEncodedWord [11, 4, 1, 8, 4])) 3 :=
    R1.contextual_sound (shearEncodedWord [11, 4])
      (shearEncodedWord [8, 1, 4]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 3 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 4, 1, 8, 4]))
      (FreeGroup.mk (shearEncodedWord [11, 4, 1, 6, 8, 7])) 3 :=
    R2.contextual_sound (shearEncodedWord [11, 4, 1])
      (shearEncodedWord [4]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 0 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 4, 1, 6, 8, 7]))
      (FreeGroup.mk (shearEncodedWord [11, 4, 6, 3, 1, 8, 7])) 3 :=
    R3.contextual_sound (shearEncodedWord [11, 4])
      (shearEncodedWord [6, 8, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 2 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 4, 6, 3, 1, 8, 7]))
      (FreeGroup.mk (shearEncodedWord [11, 3, 4, 1, 8, 7])) 3 :=
    R4.contextual_sound (shearEncodedWord [11])
      (shearEncodedWord [6, 3, 1, 8, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 4 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 3, 4, 1, 8, 7]))
      (FreeGroup.mk (shearEncodedWord [11, 3, 4, 10, 8, 1, 7])) 3 :=
    R5.contextual_sound (shearEncodedWord [11, 3, 4])
      (shearEncodedWord [8, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 5 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 3, 4, 10, 8, 1, 7]))
      (FreeGroup.mk (shearEncodedWord [11, 3, 10, 4, 1, 7])) 3 :=
    R6.contextual_sound (shearEncodedWord [11, 3])
      (shearEncodedWord [10, 8, 1, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 1 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 3, 10, 4, 1, 7]))
      (FreeGroup.mk (shearEncodedWord [1, 3, 4, 1, 7])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [3, 10, 4, 1, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 2 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 3, 4, 1, 7]))
      (FreeGroup.mk (shearEncodedWord [1, 4, 3, 6, 1, 7])) 3 :=
    R8.contextual_sound (shearEncodedWord [1])
      (shearEncodedWord [4, 1, 7]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 0 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 4, 3, 6, 1, 7]))
      (FreeGroup.mk (shearEncodedWord [1, 4, 1])) 3 :=
    R9.contextual_sound (shearEncodedWord [1, 4])
      (shearEncodedWord [6, 1, 7]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

theorem shearWeyl3 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [6, 11, 6]))
    (FreeGroup.mk (shearEncodedWord [11, 6, 11])) 30 := by
  let C0 := shearRootCertificate (roots.getD 0 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [6, 11, 6]))
      (FreeGroup.mk (shearEncodedWord [1, 6, 0, 2, 11, 6])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [11, 6]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 1 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 6, 0, 2, 11, 6]))
      (FreeGroup.mk (shearEncodedWord [1, 6, 11, 2, 6])) 3 :=
    R1.contextual_sound (shearEncodedWord [1, 6])
      (shearEncodedWord [2, 11, 6]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 2 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 6, 11, 2, 6]))
      (FreeGroup.mk (shearEncodedWord [1, 6, 11, 4, 2, 5])) 3 :=
    R2.contextual_sound (shearEncodedWord [1, 6, 11])
      (shearEncodedWord [6]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 5 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 6, 11, 4, 2, 5]))
      (FreeGroup.mk (shearEncodedWord [1, 6, 4, 9, 11, 2, 5])) 3 :=
    R3.contextual_sound (shearEncodedWord [1, 6])
      (shearEncodedWord [4, 2, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 3 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 6, 4, 9, 11, 2, 5]))
      (FreeGroup.mk (shearEncodedWord [1, 9, 6, 11, 2, 5])) 3 :=
    R4.contextual_sound (shearEncodedWord [1])
      (shearEncodedWord [4, 9, 11, 2, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 1 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 9, 6, 11, 2, 5]))
      (FreeGroup.mk (shearEncodedWord [1, 9, 6, 0, 2, 11, 5])) 3 :=
    R5.contextual_sound (shearEncodedWord [1, 9, 6])
      (shearEncodedWord [2, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 0 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 9, 6, 0, 2, 11, 5]))
      (FreeGroup.mk (shearEncodedWord [1, 9, 0, 6, 11, 5])) 3 :=
    R6.contextual_sound (shearEncodedWord [1, 9])
      (shearEncodedWord [0, 2, 11, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 4 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [1, 9, 0, 6, 11, 5]))
      (FreeGroup.mk (shearEncodedWord [11, 9, 6, 11, 5])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [9, 0, 6, 11, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 3 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 9, 6, 11, 5]))
      (FreeGroup.mk (shearEncodedWord [11, 6, 9, 4, 11, 5])) 3 :=
    R8.contextual_sound (shearEncodedWord [11])
      (shearEncodedWord [6, 11, 5]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 5 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [11, 6, 9, 4, 11, 5]))
      (FreeGroup.mk (shearEncodedWord [11, 6, 11])) 3 :=
    R9.contextual_sound (shearEncodedWord [11, 6])
      (shearEncodedWord [4, 11, 5]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

theorem shearWeyl4 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [8, 3, 8]))
    (FreeGroup.mk (shearEncodedWord [3, 8, 3])) 30 := by
  let C0 := shearRootCertificate (roots.getD 3 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [8, 3, 8]))
      (FreeGroup.mk (shearEncodedWord [7, 8, 6, 4, 3, 8])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [3, 8]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 2 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 8, 6, 4, 3, 8]))
      (FreeGroup.mk (shearEncodedWord [7, 8, 3, 4, 8])) 3 :=
    R1.contextual_sound (shearEncodedWord [7, 8])
      (shearEncodedWord [4, 3, 8]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 5 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 8, 3, 4, 8]))
      (FreeGroup.mk (shearEncodedWord [7, 8, 3, 10, 4, 11])) 3 :=
    R2.contextual_sound (shearEncodedWord [7, 8, 3])
      (shearEncodedWord [8]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 1 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 8, 3, 10, 4, 11]))
      (FreeGroup.mk (shearEncodedWord [7, 8, 10, 1, 3, 4, 11])) 3 :=
    R3.contextual_sound (shearEncodedWord [7, 8])
      (shearEncodedWord [10, 4, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 4 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 8, 10, 1, 3, 4, 11]))
      (FreeGroup.mk (shearEncodedWord [7, 1, 8, 3, 4, 11])) 3 :=
    R4.contextual_sound (shearEncodedWord [7])
      (shearEncodedWord [10, 1, 3, 4, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 2 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 1, 8, 3, 4, 11]))
      (FreeGroup.mk (shearEncodedWord [7, 1, 8, 6, 4, 3, 11])) 3 :=
    R5.contextual_sound (shearEncodedWord [7, 1, 8])
      (shearEncodedWord [4, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 3 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 1, 8, 6, 4, 3, 11]))
      (FreeGroup.mk (shearEncodedWord [7, 1, 6, 8, 3, 11])) 3 :=
    R6.contextual_sound (shearEncodedWord [7, 1])
      (shearEncodedWord [6, 4, 3, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 0 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 1, 6, 8, 3, 11]))
      (FreeGroup.mk (shearEncodedWord [3, 1, 8, 3, 11])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [1, 6, 8, 3, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 4 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 1, 8, 3, 11]))
      (FreeGroup.mk (shearEncodedWord [3, 8, 1, 10, 3, 11])) 3 :=
    R8.contextual_sound (shearEncodedWord [3])
      (shearEncodedWord [8, 3, 11]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 1 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 8, 1, 10, 3, 11]))
      (FreeGroup.mk (shearEncodedWord [3, 8, 3])) 3 :=
    R9.contextual_sound (shearEncodedWord [3, 8])
      (shearEncodedWord [10, 3, 11]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

theorem shearWeyl5 : RelatorEquality IntegralShear.relators
    (FreeGroup.mk (shearEncodedWord [10, 7, 10]))
    (FreeGroup.mk (shearEncodedWord [7, 10, 7])) 30 := by
  let C0 := shearRootCertificate (roots.getD 1 root12) false false
  let R0 := CertifiedWordRule.fromRelator C0.word C0.area false 3 1
  have h0 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [10, 7, 10]))
      (FreeGroup.mk (shearEncodedWord [3, 10, 2, 0, 7, 10])) 3 :=
    R0.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [7, 10]) _ _ (by decide +kernel) (by decide +kernel)
  let C1 := shearRootCertificate (roots.getD 0 root12) true false
  let R1 := CertifiedWordRule.fromRelator C1.word C1.area false 4 1
  have h1 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 10, 2, 0, 7, 10]))
      (FreeGroup.mk (shearEncodedWord [3, 10, 7, 0, 10])) 3 :=
    R1.contextual_sound (shearEncodedWord [3, 10])
      (shearEncodedWord [0, 7, 10]) _ _ (by decide +kernel) (by decide +kernel)
  let C2 := shearRootCertificate (roots.getD 4 root12) true false
  let R2 := CertifiedWordRule.fromRelator C2.word C2.area false 3 1
  have h2 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 10, 7, 0, 10]))
      (FreeGroup.mk (shearEncodedWord [3, 10, 7, 8, 0, 9])) 3 :=
    R2.contextual_sound (shearEncodedWord [3, 10, 7])
      (shearEncodedWord [10]) _ _ (by decide +kernel) (by decide +kernel)
  let C3 := shearRootCertificate (roots.getD 3 root12) false false
  let R3 := CertifiedWordRule.fromRelator C3.word C3.area true 2 1
  have h3 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 10, 7, 8, 0, 9]))
      (FreeGroup.mk (shearEncodedWord [3, 10, 8, 5, 7, 0, 9])) 3 :=
    R3.contextual_sound (shearEncodedWord [3, 10])
      (shearEncodedWord [8, 0, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C4 := shearRootCertificate (roots.getD 5 root12) false false
  let R4 := CertifiedWordRule.fromRelator C4.word C4.area true 4 1
  have h4 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 10, 8, 5, 7, 0, 9]))
      (FreeGroup.mk (shearEncodedWord [3, 5, 10, 7, 0, 9])) 3 :=
    R4.contextual_sound (shearEncodedWord [3])
      (shearEncodedWord [8, 5, 7, 0, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C5 := shearRootCertificate (roots.getD 0 root12) true false
  let R5 := CertifiedWordRule.fromRelator C5.word C5.area true 1 1
  have h5 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 5, 10, 7, 0, 9]))
      (FreeGroup.mk (shearEncodedWord [3, 5, 10, 2, 0, 7, 9])) 3 :=
    R5.contextual_sound (shearEncodedWord [3, 5, 10])
      (shearEncodedWord [0, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C6 := shearRootCertificate (roots.getD 1 root12) false false
  let R6 := CertifiedWordRule.fromRelator C6.word C6.area true 3 1
  have h6 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 5, 10, 2, 0, 7, 9]))
      (FreeGroup.mk (shearEncodedWord [3, 5, 2, 10, 7, 9])) 3 :=
    R6.contextual_sound (shearEncodedWord [3, 5])
      (shearEncodedWord [2, 0, 7, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C7 := shearRootCertificate (roots.getD 2 root12) false false
  let R7 := CertifiedWordRule.fromRelator C7.word C7.area true 1 1
  have h7 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [3, 5, 2, 10, 7, 9]))
      (FreeGroup.mk (shearEncodedWord [7, 5, 10, 7, 9])) 3 :=
    R7.contextual_sound (shearEncodedWord [])
      (shearEncodedWord [5, 2, 10, 7, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C8 := shearRootCertificate (roots.getD 5 root12) false true
  let R8 := CertifiedWordRule.fromRelator C8.word C8.area true 3 1
  have h8 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 5, 10, 7, 9]))
      (FreeGroup.mk (shearEncodedWord [7, 10, 5, 8, 7, 9])) 3 :=
    R8.contextual_sound (shearEncodedWord [7])
      (shearEncodedWord [10, 7, 9]) _ _ (by decide +kernel) (by decide +kernel)
  let C9 := shearRootCertificate (roots.getD 3 root12) false true
  let R9 := CertifiedWordRule.fromRelator C9.word C9.area true 0 1
  have h9 : RelatorEquality IntegralShear.relators
      (FreeGroup.mk (shearEncodedWord [7, 10, 5, 8, 7, 9]))
      (FreeGroup.mk (shearEncodedWord [7, 10, 7])) 3 :=
    R9.contextual_sound (shearEncodedWord [7, 10])
      (shearEncodedWord [8, 7, 9]) _ _ (by decide +kernel) (by decide +kernel)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans (h9)))))))))

end ThomGame.Analysis
