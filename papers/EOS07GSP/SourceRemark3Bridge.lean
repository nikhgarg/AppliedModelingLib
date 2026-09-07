import EOS07GSP.MainTheorems

/-!
# Exact source witness for EOS Remark 3

The reusable library's GSP non-truthfulness example uses different numerical
parameters. This file records the witness printed in EOS Remark 3: values
`(10, 4, 2)`, click-through rates `(200, 199)`, and bidder 1's report of `3`.
-/

namespace EOS07GSP

open AppliedModelingLib.Auction

noncomputable section

def remark3SourceEnvironment : PositionEnvironment (Fin 2) where
  clickThroughRate slot := if slot = (0 : Fin 2) then 200 else 199

def remark3SourceValues (bidder : Fin 3) : ℝ :=
  if bidder = (0 : Fin 3) then 10 else if bidder = (1 : Fin 3) then 4 else 2

def remark3SourceShadedBids (bidder : Fin 3) : ℝ :=
  if bidder = (0 : Fin 3) then 3 else if bidder = (1 : Fin 3) then 4 else 2

theorem remark3_source_truthful_utility :
    PositionMechanism.utility remark3SourceEnvironment gsp3TwoSlotMechanism
      remark3SourceValues remark3SourceValues (0 : Fin 3) = 1200 := by
  norm_num [PositionMechanism.utility, PositionOutcome.utility,
    remark3SourceEnvironment, remark3SourceValues, gsp3TwoSlotMechanism,
    topBidder3, secondBidder3, thirdBidder3]

theorem remark3_source_shaded_utility :
    PositionMechanism.utility remark3SourceEnvironment gsp3TwoSlotMechanism
      remark3SourceValues remark3SourceShadedBids (0 : Fin 3) = 1592 := by
  norm_num [PositionMechanism.utility, PositionOutcome.utility,
    remark3SourceEnvironment, remark3SourceValues, remark3SourceShadedBids,
    gsp3TwoSlotMechanism, topBidder3, secondBidder3, thirdBidder3]

theorem remark3_source_not_truthful :
    ¬ PositionMechanism.TruthfulDominantStrategy remark3SourceEnvironment
      gsp3TwoSlotMechanism := by
  intro htruth
  have hdeviation := htruth remark3SourceValues (0 : Fin 3) 3
  have hshaded : Function.update remark3SourceValues (0 : Fin 3) 3 =
      remark3SourceShadedBids := by
    funext bidder
    fin_cases bidder <;> norm_num [remark3SourceValues, remark3SourceShadedBids,
      Function.update]
  rw [hshaded, remark3_source_shaded_utility,
    remark3_source_truthful_utility] at hdeviation
  norm_num at hdeviation

end
end EOS07GSP
