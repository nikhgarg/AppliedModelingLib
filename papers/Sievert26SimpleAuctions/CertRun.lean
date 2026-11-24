import Sievert26SimpleAuctions.CertData

/-! Kernel evaluation of the integer certificate (`decide +kernel`, no `native_decide`). -/
namespace Sievert26SimpleAuctions
namespace UBCert

set_option maxRecDepth 1000000

theorem tan0_ok : tanLoop (y0n 0) (y0d 0) (bn 0) (kn 0) xs0 1000 0 0 = true := by decide +kernel
theorem tan1_ok : tanLoop (y0n 1) (y0d 1) (bn 1) (kn 1) xs1 1000 0 0 = true := by decide +kernel
theorem tan2_ok : tanLoop (y0n 2) (y0d 2) (bn 2) (kn 2) xs2 1000 0 0 = true := by decide +kernel
theorem tan3_ok : tanLoop (y0n 3) (y0d 3) (bn 3) (kn 3) xs3 1000 0 0 = true := by decide +kernel
theorem tab_ok : tabOk tab Vmax = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem lev_ok : allLev tab Vmax kap gCap 0 al0 levels = true := by decide +kernel

end UBCert
end Sievert26SimpleAuctions
