import Mathlib

open Classical

theorem algebra_946
  (x y z : ℤ)
  (h1 : x * y + z = 94)
  (h2 : x + y * z = 95) :
  x * y * z = 0 ∨ x * y * z = 1984 := by

  have eq1 : (x - z) * (1 - y) = 1 := by
    nlinarith

  have h4 : (x - z) = 1 ∨ (x - z) = -1 := by
    have h5 : (x - z) * (1 - y) = 1 := eq1
    have h7 : (x - z) ∣ 1 := by 
      use (1 - y)
      all_goals linarith
    have h8 : (x - z) = 1 ∨ (x - z) = -1 := by
      have h9 : (x - z) ∣ 1 := h7
      have h10 : (x - z) = 1 ∨ (x - z) = -1 := by 
        have h11 : (x - z) ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h9
        have h12 : (x - z) ≥ -1 := by 
          have h13 : (- (x - z)) ∣ 1 := by
            exact Int.neg_dvd.2 h9
          have h14 : - (x - z) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h13
          linarith
        interval_cases (x - z) <;> tauto
      assumption
    assumption

  cases h4 with
  | inl h5 =>
    have h6 : z = x - 1 := by linarith
    have h7 : y = 0 := by
      have h8 : (1 - y) = 1 := by 
        have h9 : (x - z) * (1 - y) = 1 := eq1
        rw [show (x - z) = 1 by linarith] at h9
        linarith
      linarith
    have h8 : x * y * z = 0 := by
      rw [show y = 0 by linarith [h7]]
      norm_num
    left
    exact h8
  | inr h5 =>
    have h8 : z = x + 1 := by linarith
    have h7 : y = 2 := by
      have h9 : (1 - y) = -1 := by 
        have h10 : (x - z) * (1 - y) = 1 := eq1
        rw [show (x - z) = -1 by linarith] at h10
        linarith
      linarith
    have hx : x = 31 := by
      rw [show y = 2 by linarith [h7], show z = x + 1 by linarith [h8] ] at h1
      nlinarith
    have h9 : z = 32 := by
      rw [show x = 31 by linarith [hx] ] at h8
      linarith
    have h10 : x * y * z = 1984 := by
      rw [show x = 31 by linarith [hx], show y = 2 by linarith [h7], show z = 32 by linarith [h9]]
      norm_num
    right
    exact h10