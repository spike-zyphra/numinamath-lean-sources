import Mathlib

/- Is there a first- or second-degree polynomial that takes the values $100,90,70,40,0$ for the variable values $0,1,2,3,4$ respectively? -/
theorem algebra_160965 :
    ∃ P : Polynomial ℝ, (P.natDegree = 1 ∨ P.natDegree = 2) ∧ P.eval 0 = 100 ∧ P.eval 1 = 90 ∧ P.eval 2 = 70 ∧ P.eval 3 = 40 ∧ P.eval 4 = 0 := by
  use -5 * Polynomial.X ^ 2 - 5 * Polynomial.X + 100
  refine ⟨?_, ?_⟩
  . right
    compute_degree!
  . norm_num