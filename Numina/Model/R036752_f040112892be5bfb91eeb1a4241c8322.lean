import Mathlib

theorem algebra_181509 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hroots : ∃ x, x > 1 ∧ x^2 + a * x - 100 = 0 ∧ x^2 - 200 * x + b = 0) :
    b - a > 100 := by 
  rcases hroots with ⟨r, hr1, hr2, hr3⟩
  have h3 : b = 200 * r + a * r - 100 := by
    nlinarith
  have h5 : b - a > 100 := by
    rw [h3]
    have h6 : 200 * r + a * r - 100 - a > 100 := by
      nlinarith [mul_pos ha (show 0 < r - 1 by linarith), sq_pos_of_pos ha, sq_pos_of_pos (show 0 < r - 1 by linarith)]
    linarith
  linarith