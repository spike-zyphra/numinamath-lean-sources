import Mathlib

theorem algebra_610346 (a b : ℝ) (h : {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} = {(a, b)}) : a + b = 8 := by
  have h1 : (a, b) ∈ {(x, y) : ℝ × ℝ | y = -x + 8 ∧ 173 * y = -289 * x + 2021} := by
    rw [h]
    simp
  rcases h1 with ⟨h_eq1, h_eq2⟩
  linarith