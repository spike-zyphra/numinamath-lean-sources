import Mathlib

def P (y : ℝ) := ∃ x, y = x^2 - 6 * x + 10
def M (y : ℝ) := ∃ x, y = -x^2 + 2 * x + 8

theorem algebra_115358 :
    {y | P y ∧ M y} = {y | 1 ≤ y ∧ y ≤ 9} := by 
  ext y
  simp [P, M]
  constructor
  · -- Assume $y \in P \cap M$, then there exists $x$ where $y = x^2 -6 x +10$ and there exists $x' where $y = -x'^2 +2 x' +8$.
    rintro ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩
    have h1 : 1 ≤ y := by 
      nlinarith [sq_nonneg (x - 3)]
    have h2 : y ≤ 9 := by
      nlinarith [sq_nonneg (x' - 1)]
    exact ⟨h1, h2⟩
  · -- Assume $y \in \{y \mid 1 \leq y \land y \leq 9\}$, we need to prove $y \in P \cap M$.
    rintro ⟨h1, h2⟩
    constructor
    · -- Show $Py$
      use 3 + Real.sqrt (y - 1)
      nlinarith [Real.sqrt_nonneg (y - 1), Real.sq_sqrt (show (y - 1) ≥ 0 by linarith)]
    · -- Show $My$
      use 1 + Real.sqrt (9 - y)
      nlinarith [Real.sqrt_nonneg (9 - y), Real.sq_sqrt (show (9 - y) ≥ 0 by linarith)]