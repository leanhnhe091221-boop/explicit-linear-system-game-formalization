module

public import ThomGame.Certificates.LambdaCanonical00

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_016_correct :
    (raw_016.map canonical).filter (fun r => !r.isEmpty) = clean_016 := by
  decide +kernel

theorem clean_017_correct :
    (raw_017.map canonical).filter (fun r => !r.isEmpty) = clean_017 := by
  decide +kernel

theorem clean_018_correct :
    (raw_018.map canonical).filter (fun r => !r.isEmpty) = clean_018 := by
  decide +kernel

theorem clean_019_correct :
    (raw_019.map canonical).filter (fun r => !r.isEmpty) = clean_019 := by
  decide +kernel

theorem clean_020_correct :
    (raw_020.map canonical).filter (fun r => !r.isEmpty) = clean_020 := by
  decide +kernel

theorem clean_021_correct :
    (raw_021.map canonical).filter (fun r => !r.isEmpty) = clean_021 := by
  decide +kernel

theorem clean_022_correct :
    (raw_022.map canonical).filter (fun r => !r.isEmpty) = clean_022 := by
  decide +kernel

theorem clean_023_correct :
    (raw_023.map canonical).filter (fun r => !r.isEmpty) = clean_023 := by
  decide +kernel


end ThomGame.Lambda.Certificate
