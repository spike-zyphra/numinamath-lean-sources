import Mathlib

theorem algebra_4623 (x : ℕ) : 2^(4 - x) + 2^x = 17 ↔ x = 0 ∨ x = 4 := by
  constructor
  · -- Assume $2^(4 - x) + 2^x = 17$ prove $x = 0 ∨ x = 4$
    intro h
    have h1 : x ≤ 4 := by
      by_contra h1
      push_neg at h1
      have h2 : x > 4 := h1
      have h3 : 4 - x = 0 := by
        omega
      have h4 : 2 ^ (4 - x) = 1 := by
        rw [h3]
        all_goals norm_num
      have h5 : 2 ^ x = 16 := by
        have h6 : 2 ^ (4 - x) + 2 ^ x = 17 := h
        rw [h4] at h6
        omega
      have h6 : x = 4 := by
        have h7 : 2 ^ x = 16 := h5
        have h8 : x = 4 := by
          have h9 : 2 ^ x = 2 ^ 4 := by
            rw [h7]
            all_goals norm_num
          exact Nat.pow_right_injective (by norm_num) h9
        exact h8
      linarith
    interval_cases x <;> norm_num at h ⊢ <;> tauto
  · -- Assume $x = 0 ∨ x = 4$ prove $2^(4 - x) + 2^x = 17$
    rintro (h | h)
    · -- x = 0
      rw [h]
      all_goals norm_num
    · -- x = 4
      rw [h]
      all_goals norm_num