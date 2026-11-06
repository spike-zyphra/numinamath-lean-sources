import Mathlib

theorem algebra_20417 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : 2^x * 3^y = 1296) : x + y = 8 := by 
  have h1 : x ≤ 10 := by
    by_contra h1
    push_neg at h1
    have h2 : x >= 11 := by linarith
    have h3 : 2^x * 3^y >= 2^11 * 3^1 := by
      have h4 : 2^x >= 2^11 := by
        have h5 : x >= 11 := h2
        have h6 : 2^x >= 2^11 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h5
        linarith
      have h7 : 3^y >= 3^1 := by
        have h8 : y >= 1 := by linarith
        have h9 : 3^y >= 3^1 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h8
        linarith
      nlinarith [h4, h7, show 2 > 0 by norm_num, show 3 > 0 by norm_num]
    nlinarith
  have h2 : y ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h3 : y >= 9 := by linarith
    have h4 : 2^x * 3^y >= 2^1 * 3^9 := by
      have h5 : 2^x >= 2^1 := by
        have h6 : x >= 1 := by linarith
        have h7 : 2^x >= 2^1 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h6
        linarith
      have h8 : 3^y >= 3^9 := by
        have h9 : y >= 9 := h3
        have h10 : 3^y >= 3^9 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h9
        linarith
      nlinarith [h5, h8, show 2 > 0 by norm_num, show 3 > 0 by norm_num]
    nlinarith
  interval_cases x <;> interval_cases y
    <;> omega