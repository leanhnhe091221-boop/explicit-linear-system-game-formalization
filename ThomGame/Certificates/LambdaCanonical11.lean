module

public import ThomGame.Certificates.LambdaCanonical09

/-! Kernel-checked canonicalization of bounded chunks. Two dependency chains bound build concurrency. -/

set_option maxRecDepth 60000
set_option maxHeartbeats 12000000

@[expose] public section
namespace ThomGame.Lambda.Certificate

theorem clean_088_correct :
    (raw_088.map canonical).filter (fun r => !r.isEmpty) = clean_088 := by
  decide +kernel

theorem clean_089_correct :
    (raw_089.map canonical).filter (fun r => !r.isEmpty) = clean_089 := by
  decide +kernel

theorem clean_090_correct :
    (raw_090.map canonical).filter (fun r => !r.isEmpty) = clean_090 := by
  decide +kernel

theorem clean_091_correct :
    (raw_091.map canonical).filter (fun r => !r.isEmpty) = clean_091 := by
  decide +kernel

theorem clean_092_correct :
    (raw_092.map canonical).filter (fun r => !r.isEmpty) = clean_092 := by
  decide +kernel

theorem clean_093_correct :
    (raw_093.map canonical).filter (fun r => !r.isEmpty) = clean_093 := by
  decide +kernel

theorem clean_094_correct :
    (raw_094.map canonical).filter (fun r => !r.isEmpty) = clean_094 := by
  decide +kernel

theorem clean_095_correct :
    (raw_095.map canonical).filter (fun r => !r.isEmpty) = clean_095 := by
  decide +kernel


end ThomGame.Lambda.Certificate
