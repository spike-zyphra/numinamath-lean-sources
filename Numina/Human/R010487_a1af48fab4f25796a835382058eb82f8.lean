import Mathlib

/- The solution set of the inequality $|x| - |x - 3| < 2$ is ___. -/
theorem algebra_9059 (x : ℝ) :
    |x| - |x - 3| < 2 ↔ x < 5/2 := by
  -- Three cases, x ≥ 3, 0 ≤ x < 3, x < 0
  have h : x ≥ 3 ∨ 0 ≤ x ∧ x < 3 ∨ x < 0 := by
    by_contra! h
    replace h : x < 3 ∧ 3 ≤ x := by tauto
    linarith

  -- Case analysis
  obtain h | ⟨h1, h2⟩ | h := h
  -- Break down the absolute values in each case
  -- And then linarith can solve them
  . rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    constructor <;> intro <;> linarith
  . rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    constructor <;> intro <;> linarith
  . rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    constructor <;> intro <;> linarith
