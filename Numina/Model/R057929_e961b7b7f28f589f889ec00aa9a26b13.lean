import Mathlib

theorem algebra_4879 (x : ℕ) (hx : x > 0) : (29 ^ x + 2023 = 594825344) ↔ x = 6 := by
  constructor
  · -- Assume 29 ^ x + 2023 = 594825344, prove x = 6
    intro h
    have h1 : 29 ^ x = 594823321 := by 
      omega

    have h2 : x ≤ 6 := by
      by_contra h2
      push_neg at h2
      have h2' : x ≥ 7 := by omega
      have h3 : 29 ^ x ≥ 29 ^ 7 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals omega
      have h4 : 29 ^ x > 594823321 := by
        have h5 : 29 ^ 7 > 594823321 := by norm_num
        linarith [h3, h5]
      linarith [h1, h4]

    interval_cases x <;> norm_num at h1 <;> omega

  · -- Assume x = 6, prove 29 ^ x + 2023 = 594825344
    intro h_eq
    rw [h_eq]
    all_goals norm_num