module

public import ThomGame.Certificates.NetzerThomWords21
public import ThomGame.Certificates.NetzerThomWordSoundness

@[expose] public section
namespace ThomGame.Certificates.NetzerThom

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def allWordCertificates : List (ResidualClass × WordClassPaths) :=
  wordCertificates0 ++
  wordCertificates1 ++
  wordCertificates2 ++
  wordCertificates3 ++
  wordCertificates4 ++
  wordCertificates5 ++
  wordCertificates6 ++
  wordCertificates7 ++
  wordCertificates8 ++
  wordCertificates9 ++
  wordCertificates10 ++
  wordCertificates11 ++
  wordCertificates12 ++
  wordCertificates13 ++
  wordCertificates14 ++
  wordCertificates15 ++
  wordCertificates16 ++
  wordCertificates17 ++
  wordCertificates18 ++
  wordCertificates19 ++
  wordCertificates20 ++
  wordCertificates21

theorem allWordCertificates_checked :
    allWordCertificates.all (fun e => wordClassCheck e.1 e.2) = true := by
  simp only [allWordCertificates, List.all_append, wordCertificates0_checked, wordCertificates1_checked, wordCertificates2_checked, wordCertificates3_checked, wordCertificates4_checked, wordCertificates5_checked, wordCertificates6_checked, wordCertificates7_checked, wordCertificates8_checked, wordCertificates9_checked, wordCertificates10_checked, wordCertificates11_checked, wordCertificates12_checked, wordCertificates13_checked, wordCertificates14_checked, wordCertificates15_checked, wordCertificates16_checked, wordCertificates17_checked, wordCertificates18_checked, wordCertificates19_checked, wordCertificates20_checked, wordCertificates21_checked, Bool.and_self]

theorem allWordCertificates_classes :
    allWordCertificates.map Prod.fst = residualClasses := by rfl

theorem residualClasses_wordSound (c : ResidualClass) (hc : c ∈ residualClasses) :
    WordClassSound c := by
  rw [← allWordCertificates_classes] at hc
  obtain ⟨⟨c',p⟩, hp, he⟩ := List.mem_map.mp hc
  change c' = c at he
  subst c'
  exact wordClassCheck_sound ((List.all_eq_true.mp allWordCertificates_checked) (c,p) hp)

end ThomGame.Certificates.NetzerThom
