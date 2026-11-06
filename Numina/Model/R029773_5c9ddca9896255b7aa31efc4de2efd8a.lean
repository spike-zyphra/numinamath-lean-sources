import Mathlib

theorem algebra_5809 (x : ℕ) : (21^x + 2019 = 37822861380) ↔ x = 8 := by
  constructor
  · -- Assume 21^x + 2019 = 37822861380, prove x = 8
    intro h
    have eq1 : 21 ^ x = 37822861380 - 2019 := by
      omega
    have eq2 : 21 ^ x = 37822859361 := by
      norm_num at eq1 ⊢
      omega
    have h1 : x ≤ 9 := by
      by_contra h2
      push_neg at h2
      have h2' : x ≥ 10 := by omega
      have h3 : 21 ^ x ≥ 21 ^ 10 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals norm_num
        all_goals omega
      norm_num at h3
      all_goals omega
    interval_cases x <;> norm_num at eq2 ⊢
    all_goals omega
  · -- Assume x = 8, prove 21^x + 2019 = 37822861380
    intro h
    rw [h]
    all_goals norm_num