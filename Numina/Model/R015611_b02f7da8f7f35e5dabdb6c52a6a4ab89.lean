import Mathlib

theorem algebra_10436 {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a + b = 9) (h2 : a * b = 20) : 1 / a + 1 / b = 9 / 20 := by 
  have h3 : a = 4 ∨ a = 5 := by
    have h4 : a ≤ 9 := by 
      nlinarith [h1, h2]
    have h5 : a ≥ 0 := by 
      nlinarith [h1, h2]
    interval_cases a <;> omega 
  rcases h3 with (ha4 | ha5)
  · -- Case a = 4 
    have hb5 : b = 5 := by
      omega 
    rw [ha4, hb5]
    all_goals 
      norm_num 
  · -- Case a = 5
    have hb4 : b = 4 := by
      omega 
    rw [ha5, hb4]
    all_goals 
      norm_num