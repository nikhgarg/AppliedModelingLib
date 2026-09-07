import LBG24SpatialUnderreporting.MainTheorems

/-!
# Empirical observation-endpoint formulas for LBG24

The two definitions in this module are the paper's direct preprocessing
formulas.  They are kept outside the historical proof-support surface so the
audited paper root can expose them without importing legacy constructions.
-/

namespace LBG24SpatialUnderreporting

/-- Eq. (33), NYC preprocessing: close at the earliest of 100 days after the
start, inspection, and work-order times. -/
def equation33_nyc_observation_end
    (startTime inspectionTime workOrderTime : ℝ) : ℝ :=
  min (min (startTime + (100 : ℝ)) inspectionTime) workOrderTime

/-- Eq. (34), Chicago preprocessing: close at the earliest of 100 days after
the first report, closure, and data-retrieval times. -/
def equation34_chicago_observation_end
    (firstReportTime closedTime retrievalTime : ℝ) : ℝ :=
  min (min (firstReportTime + (100 : ℝ)) closedTime) retrievalTime

end LBG24SpatialUnderreporting
