import Mathlib

theorem algebra_153520 (a b : ℝ) (h : ∃ d, 10 + d = a ∧ a + d = b ∧ b + d = a * b) :
    (a, b) = (4, -2) ∨ (a, b) = (5 / 2, -5) := by
  rcases h with ⟨d, h1, h2, h3⟩
  have eq1 : d = a - 10 := by linarith
  have eq2 : b = 2 * a - 10 := by
    have eq3 : d = a - 10 := by linarith
    have eq3' : a + d = b := by linarith
    rw [eq3] at eq3'
    linarith
  have eq3' : b + d = a * b := by linarith
  rw [eq1, eq2] at eq3'
  have h4 : 2 * a ^ 2 - 13 * a + 20 = 0 := by
    nlinarith
  have h5 : (a - 4) * (2 * a - 5) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- a = 4
    have h8 : a = 4 := by linarith
    have h9 : b = -2 := by
      rw [h8] at eq2
      linarith
    left
    exact Prod.ext h8 h9
  · -- 2 * a - 5 = 0, hence a = 5/2
    have h10 : a = 5 / 2 := by linarith
    have h11 : b = -5 := by 
      rw [h10] at eq2 
      linarith
    right 
    exact Prod.ext h10 h11