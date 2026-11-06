import Mathlib

theorem algebra_274245 {a b : ℕ} (h : (2^a) * (2^b) = 64) : (a + b) / 2 = 3 := by
  have h1 : 2 ^ a * 2 ^ b = 2 ^ (a + b) := by
    rw [← pow_add]
    all_goals norm_num
  have h2 : 2 ^ (a + b) = 64 := by
    linarith [h, h1]
  have h3 : a + b = 6 := by
    have h4 : 2 ^ (a + b) = 2 ^ 6 := by
      rw [h2]
      all_goals norm_num
    have h5 : a + b = 6 := by
      exact Nat.pow_right_injective (by norm_num) h4
    exact h5
  calc
    (a + b) / 2 = 6 / 2 := by rw [show a + b = 6 by linarith [h3]]
    _ = 3 := by norm_num