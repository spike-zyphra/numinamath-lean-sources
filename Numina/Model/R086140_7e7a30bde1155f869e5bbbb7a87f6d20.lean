import Mathlib

theorem algebra_15146 : 
  {x : ℝ | x^2 + 11 * x - 8 ≠ 0 ∧ x^2 + 2 * x - 8 ≠ 0 ∧ x^2 - 13 * x - 8 ≠ 0 ∧ 1 / (x^2 + 11 * x - 8) + 1 / (x^2 + 2 * x - 8) + 1 / (x^2 - 13 * x - 8) = 0} = {8, 1, -1, -8} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward direction: if x is in the left side, it's in the right
    intro h
    rcases h with ⟨h1, h2, h3, heq⟩
    
    have eq1 : (x - 8) * (x - 1) * (x + 1) * (x + 8) = 0 := by
      field_simp [show x^2 + 11 * x - 8 ≠ 0 by exact h1, 
          show x^2 + 2 * x - 8 ≠ 0 by exact h2, 
          show x^2 - 13 * x - 8 ≠ 0 by exact h3] at heq
      ring_nf at heq ⊢
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 64), sq_nonneg (x - 1), sq_nonneg (x + 8), sq_pos_of_ne_zero (show x ^ 2 + 11 * x - 8 ≠ 0 by exact h1), sq_pos_of_ne_zero (show x ^ 2 + 2 * x - 8 ≠ 0 by exact h2), sq_pos_of_ne_zero (show x ^ 2 - 13 * x - 8 ≠ 0 by exact h3)
      ]
    
    cases' (mul_eq_zero.mp eq1) with h4 h5
    cases' mul_eq_zero.mp h4 with h6 h7
    cases' mul_eq_zero.mp h6 with h8 h9
    
    · -- Case x - 8 = 0, so x = 8
      left
      nlinarith
    · -- Case x - 1 = 0, so x = 1
      right
      left
      nlinarith
    · -- Case x + 1 = 0, so x = -1
      right
      right
      left
      nlinarith
    · -- Case x + 8 = 0, so x = -8
      right
      right
      right
      nlinarith
  
  · -- Backward direction: if x is in the right side, it's in the left
    rintro (rfl | rfl | rfl | rfl)
    · -- Check x = 8
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check x = 1
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check x = -1
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check x = -8
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num