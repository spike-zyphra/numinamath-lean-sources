import Mathlib

theorem algebra_286869 :
  {x : ℕ | 2^(x + 3) + 4^(x + 1) = 320} = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left-hand side, prove x is in the right-hand side
    intro h
    have eq1 : 2^(x + 3) + 4^(x + 1) = 320 := h
    have eq2 : x = 3 := by
      have h1 : 2 ^ (x + 3) + 4 ^ (x + 1) = 320 := eq1
      have h2 : x ≤ 4 := by 
        by_contra h3
        push_neg at h3
        have h3' : x ≥ 5 := by omega
        have h4 : 2 ^ (x + 3) + 4 ^ (x + 1) ≥ 2 ^ (5 + 3) + 4 ^ (5 + 1) := by
          have h5 : x ≥ 5 := h3'
          have h6 : x + 1 ≥ 6 := by omega
          have h7 : 4 ^ (x + 1) ≥ 4 ^ (5 + 1) := by
            have h6' : x + 1 ≥ 6 := by omega
            have h11 : 4 ^ (x + 1) ≥ 4 ^ (6) := by 
              apply Nat.pow_le_pow_of_le_right (by norm_num) h6'
            have h12 : 4 ^ (6) = 4 ^ (5 + 1) := by 
              norm_num
            have h7 : 4 ^ (x + 1) ≥ 4 ^ (5 + 1) := by 
              rw [h12] at h11
              linarith
            exact h7 
          have h8 : 2 ^ (x + 3) ≥ 2 ^ (5 + 3) := by 
            have h9 : x + 3 ≥ 5 + 3 := by omega
            apply Nat.pow_le_pow_of_le_right (by norm_num) h9 
          apply add_le_add 
          exact h8 
          exact h7 
        have h5 : 2 ^ (5 + 3) + 4 ^ (5 + 1) = 4352 := by norm_num
        nlinarith
      interval_cases x <;> norm_num at h1 <;> omega 
    exact eq2
  · -- Assume x = 3, prove 2^(x + 3) + 4^(x + 1) = 320
    intro h
    rw [h]
    all_goals norm_num