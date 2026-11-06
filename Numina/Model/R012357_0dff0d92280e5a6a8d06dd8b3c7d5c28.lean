import Mathlib.Tactic

theorem algebra_143322 (x y z : ℝ) (h₀ : x < y) (h₁ : y < z)
    (h₂ : x + y + z = 6) (h₃ : x * y + y * z + z * x = 9) :
    0 < x ∧ x < 1 ∧ 1 < y ∧ y < 3 ∧ 3 < z ∧ z < 4 := by
  have h4 : z = 6 - x - y := by
    linarith
  rw [show z = 6 - x - y by linarith [h₂]] at h₃
  have h5 : 0 < x := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  have h6 : x < 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  have h7 : 1 < y := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  have h8 : y < 3 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 3), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  have h9 : 3 < z := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 3), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  have h10 : z < 4 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 3), sq_nonneg (y - (6 - x - y)), sq_pos_of_pos (show y - x > 0 by linarith), sq_pos_of_pos (show (6 - x - y) - y > 0 by nlinarith)]
  constructor
  · exact h5
  constructor
  · exact h6
  constructor
  · exact h7
  constructor
  · exact h8
  constructor
  · exact h9
  · exact h10