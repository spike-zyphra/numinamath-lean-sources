import Mathlib

theorem inequalities_7688 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b^2 + c^2 = 9) :
    (a + b^2 + c^3 ≥ 239 / 27) ∧ (a + b^3 + c^3 ≥ 235 / 27) ∧ (a^3 + b^3 + c^3 ≥ 17) := by
  have ha' : a = 9 - b^2 - c^2 := by linarith
  constructor
  · -- First inequality 
    have h1 : a + b^2 + c^3 ≥ 239 / 27 := by
      rw [ha']
      nlinarith [sq_nonneg (c - 2/3), sq_nonneg (b^2 - 4/9), sq_nonneg (b - 2/3), sq_nonneg (c^2 - 4/9), sq_nonneg (c * b - 4/9), sq_nonneg (c^2 - 4/9), sq_nonneg (b^2 - 4/9), sq_nonneg (c^2 - 4/9), sq_nonneg (c - 2/3), sq_nonneg (b - 2/3), sq_nonneg (c * b - 4/9), mul_pos ha (show 0 < b^2 by nlinarith), mul_pos ha (show 0 < c^2 by nlinarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    exact h1
  constructor
  · -- Second inequality 
    have h2 : a + b^3 + c^3 ≥ 235 / 27 := by
      rw [ha']
      nlinarith [sq_nonneg (c - 2/3), sq_nonneg (b - 2/3), sq_nonneg (c^2 - 4/9), sq_nonneg (b^2 - 4/9), sq_nonneg (c * b - 4/9), sq_nonneg (c^2 - 4/9), sq_nonneg (b^2 - 4/9), sq_nonneg (c * b - 4/9), sq_nonneg (c * (c - 2/3)), sq_nonneg (b * (b - 2/3)), mul_pos ha (show 0 < b^2 by nlinarith), mul_pos ha (show 0 < c^2 by nlinarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    exact h2
  · -- Third inequality
    have h3 : a^3 + b^3 + c^3 ≥ 17 := by 
      rw [ha']
      nlinarith [sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (b + 2), sq_nonneg (c + 2), sq_nonneg (b^2 - 4), sq_nonneg (c^2 - 4), sq_nonneg (c - b), sq_nonneg ((9 - b^2 - c^2) - 1), mul_pos (show 0 < b by linarith) (show 0 < c by linarith), mul_pos (show 0 < 9 - b^2 - c^2 by nlinarith) (show 0 < b by linarith), mul_pos (show 0 < 9 - b^2 - c^2 by nlinarith) (show 0 < c by linarith), mul_pos (show 0 < b^2 by nlinarith) (show 0 < c^2 by nlinarith)]
    exact h3