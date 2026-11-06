import Mathlib

theorem algebra_53888 {x y : ℕ} (hx : (Nat.digits 10 x).length = 2)
    (hy : (Nat.digits 10 y).length = 3) (h : 1000 * x + y = 9 * x * y) :
    x + y = 126 := by
  have h1 : x ≥ 10 := by
    by_contra h1
    push_neg at h1
    interval_cases x <;> norm_num at hx <;> omega
  have h2 : x ≤ 99 := by
    by_contra h2
    push_neg at h2
    have h3 : x ≥ 100 := by omega
    have h4 : (Nat.digits 10 x).length > 2 := by
      have h5 : x ≥ 100 := by linarith
      have h6 : (Nat.log 10 x) ≥ 2 := by
        apply Nat.le_log_of_pow_le (by norm_num) h5
      have h7 : (Nat.digits 10 x).length = Nat.log 10 x + 1 := by
        rw [Nat.digits_len]
        all_goals linarith
      rw [h7] at *
      omega
    linarith [h4, hx]
  have h3 : y ≥ 100 := by
    by_contra h3
    push_neg at h3
    interval_cases y <;> norm_num at hy <;> omega
  have h4 : y ≤ 999 := by
    by_contra h4
    push_neg at h4
    have h5 : y ≥ 1000 := by omega
    have h6 : (Nat.digits 10 y).length > 3 := by
      have h7 : y ≥ 1000 := by linarith
      have h8 : (Nat.log 10 y) ≥ 3 := by
        apply Nat.le_log_of_pow_le (by norm_num) h7
      have h9 : (Nat.digits 10 y).length = Nat.log 10 y + 1 := by
        rw [Nat.digits_len]
        all_goals linarith
      rw [h9] at *
      omega
    linarith [h6, hy]
  interval_cases x <;> omega