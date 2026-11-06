import Mathlib

theorem algebra_166111 {x y : ℝ} (h1 : x^2 + y^2 = 34) (h2 : x + y + x * y = 23) :
    (x = 3 ∧ y = 5) ∨ (x = 5 ∧ y = 3) := by
  have h3 : (x + y) ^ 2 + 2 * (x + y) - 80 = 0 := by
    nlinarith [h1, h2]
  have h4 : (x + y - 8) * (x + y + 10) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $x + y = 8$
    have h7 : x + y = 8 := by linarith
    have h8 : x * y = 15 := by
      nlinarith [h7, h2]
    have h9 : (x - 3) * (x - 5) = 0 := by
      nlinarith [h7, h8]
    cases' (mul_eq_zero.mp h9) with h11 h12
    · -- $x - 3 = 0$, so $x = 3$, and $y = 5$
      have hx1 : x = 3 := by linarith
      have hy1 : y = 5 := by
        nlinarith [h7, hx1]
      left
      exact ⟨hx1, hy1⟩
    · -- $x - 5 = 0$, so $x = 5$, and $y = 3$
      have hx2 : x = 5 := by linarith
      have hy2 : y = 3 := by
        nlinarith [h7, hx2]
      right
      exact ⟨hx2, hy2⟩
  · -- Case where $x + y = -10$
    have h12 : x + y = -10 := by linarith
    have h13 : x * y = 33 := by 
      nlinarith [h12, h2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 33), sq_nonneg (x + y + 10), sq_nonneg (x - y)]