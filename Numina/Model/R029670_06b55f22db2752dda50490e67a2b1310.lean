import Mathlib

theorem algebra_21124 {x y : ℕ} (h : 12^2 * 18^3 = 2^x * 3^y) : x + y = 15 := by
  have h2 : x ≤ 20 := by
    by_contra h2
    push_neg at h2
    have h4 : 2^x * 3^y ≥ 2^21 := by
      have h5 : x ≥ 21 := by omega
      have h6 : 2^x ≥ 2^21 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      have h7 : 3^y ≥ 1 := by
        have h1 : 3^0 = 1 := by norm_num
        have h8 : 3^y ≥ 3^0 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        rw [h1] at h8
        all_goals omega
      have h8 : 2^x * 3^y ≥ 2^21 * 1 := by
        nlinarith [show 0 < 2^21 by positivity, show 0 < 3^y by positivity]
      linarith
    have h7 : 2^x * 3^y = 12^2 * 18^3 := by
      linarith
    have h8 : 2^21 ≤ 12^2 * 18^3 := by
      linarith [h4, h7]
    norm_num at h8
  have h3 : y ≤ 20 := by
    by_contra h4
    push_neg at h4
    have h5 : 2^x * 3^y ≥ 3^21 := by
      have h5 : y ≥ 21 := by omega
      have h6 : 3^y ≥ 3^21 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      have h7 : 2^x ≥ 1 := by
        have h1 : 2^0 = 1 := by norm_num
        have h8 : 2^x ≥ 2^0 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        rw [h1] at h8
        all_goals omega
      have h8 : 2^x * 3^y ≥ 1 * 3^21 := by
        nlinarith [show 0 < 3^21 by positivity, show 0 < 2^x by positivity]
      have h9 : (1 * 3^21 : ℕ) = (3^21 : ℕ) := by ring
      rw [h9] at h8
      linarith
    have h7 : 2^x * 3^y = 12^2 * 18^3 := by
      linarith
    have h10 : 3^21 ≤ 12^2 * 18^3 := by
      linarith [h5, h7]
    norm_num at h10
  interval_cases x <;> interval_cases y <;> omega