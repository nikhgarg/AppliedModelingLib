import DGD26AdmissionsPredictability.AuditInterface

namespace DGD26AdmissionsPredictability

open AppliedModelingLib.FiniteChoice

variable {α : Type*} [DecidableEq α]

/-- The paper's recursive queue composition on the remaining applicant pool. -/
def sequentialCompositionSource : List (PaperChoiceRule α) → PaperChoiceRule α
  | [] => fun _ => ∅
  | C :: Cs => fun X =>
      let chosen := C X
      chosen ∪ sequentialCompositionSource Cs (X \ chosen)

/-- The paper's feasible, objective-optimal maximum-weight assignment model. -/
def lapModel {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  paper_definition_lap_assignment_feasible X A ∧
    ∀ B : LAP.Assignment α σ,
      paper_definition_lap_assignment_feasible X B →
        LAP.Assignment.objective w B ≤ LAP.Assignment.objective w A

end DGD26AdmissionsPredictability
