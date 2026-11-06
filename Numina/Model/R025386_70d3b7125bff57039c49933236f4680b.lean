import Mathlib

theorem algebra_13762 (x : ℤ) :
    (3 < Real.sqrt (2 * x) ∧ Real.sqrt (2 * x) < 4) ↔ x = 5 ∨ x = 6 ∨ x = 7 := by
  constructor
  · -- Assume (3 < Real.sqrt (2 * x) ∧ Real.sqrt (2 * x) < 4), prove x = 5 ∨ x = 6 ∨ x = 7
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- x ≥ 0
      have h4 : (2 * (x : ℝ)) ≥ 0 := by
        exact_mod_cast (show (2 * x : ℤ) ≥ 0 by omega)
      have h5 : (3 : ℝ) < Real.sqrt (2 * (x : ℝ)) := by exact_mod_cast h1
      have h6 : Real.sqrt (2 * (x : ℝ)) < (4 : ℝ) := by exact_mod_cast h2
      have h7 : (Real.sqrt (2 * (x : ℝ)) : ℝ) ^ 2 = (2 * (x : ℝ)) := by
        rw [Real.sq_sqrt]
        linarith
      -- Square both sides to remove the square root
      have h8 : (3 : ℝ) ^ 2 < (Real.sqrt (2 * (x : ℝ)) : ℝ) ^ 2 := by nlinarith [h5, Real.sqrt_nonneg (2 * (x : ℝ))]
      have h9 : (Real.sqrt (2 * (x : ℝ)) : ℝ) ^ 2 < (4 : ℝ) ^ 2 := by nlinarith [h6, Real.sqrt_nonneg (2 * (x : ℝ))]
      have h10 : (3 : ℝ) ^ 2 = 9 := by norm_num
      have h11 : (4 : ℝ) ^ 2 = 16 := by norm_num
      rw [h7] at h8 h9
      have h12 : (2 * (x : ℝ) : ℝ) > (9 : ℝ) := by linarith
      have h13 : (2 * (x : ℝ) : ℝ) < (16 : ℝ) := by linarith
      -- Convert back to integer inequalities.
      have h14 : 2 * x > 9 := by
        by_contra h
        push_neg at h
        have : (2 * (x : ℝ)) ≤ (9 : ℝ) := by exact_mod_cast h
        linarith
      have h15 : 2 * x < 16 := by
        by_contra h
        push_neg at h
        have : (2 * (x : ℝ)) ≥ (16 : ℝ) := by exact_mod_cast h
        linarith
      -- 2 * x > 9 and 2 * x < 16 implies x = 5, 6, 7.
      have h2x1 : x = 5 ∨ x = 6 ∨ x = 7 := by
        omega
      assumption
    · -- x < 0
      have h4 : (2 * (x : ℝ)) < 0 := by
        have h4 : (x : ℝ) < (0 : ℝ) := by exact_mod_cast (show x < (0 : ℤ) by omega)
        nlinarith
      have h6 : Real.sqrt (2 * (x : ℝ)) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals linarith
      -- Contradicts 3 < Real.sqrt (2 * x)
      have h7 : (3 : ℝ) < Real.sqrt (2 * (x : ℝ)) := by exact_mod_cast h1
      rw [h6] at h7
      all_goals linarith
  · -- Assume x = 5 ∨ x = 6 ∨ x = 7 prove 3 < Real.sqrt (2 * x) ∧ Real.sqrt (2 * x) < 4
    rintro (h | h | h)
    · -- x = 5
      rw [h]
      constructor
      · -- 3 < Real.sqrt (2 * (5 : ℤ))
        rw [show (2 * (5 : ℤ) : ℝ) = (10 : ℝ) by norm_num]
        have h1 : (3 : ℝ) < Real.sqrt (10 : ℝ) := by
          rw [Real.lt_sqrt] <;> norm_num
        exact_mod_cast h1
      · -- Real.sqrt (2 * (5 : ℤ)) < (4 : ℝ)
        rw [show (2 * (5 : ℤ) : ℝ) = (10 : ℝ) by norm_num]
        have h2 : Real.sqrt (10 : ℝ) < (4 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        exact_mod_cast h2
    · -- x = 6
      rw [h]
      constructor
      · -- 3 < Real.sqrt (2 * (6 : ℤ))
        rw [show (2 * (6 : ℤ) : ℝ) = (12 : ℝ) by norm_num]
        have h1 : (3 : ℝ) < Real.sqrt (12 : ℝ) := by
          rw [Real.lt_sqrt] <;> norm_num
        exact_mod_cast h1
      · -- Real.sqrt (2 * (6 : ℤ)) < (4 : ℝ)
        rw [show (2 * (6 : ℤ) : ℝ) = (12 : ℝ) by norm_num]
        have h2 : Real.sqrt (12 : ℝ) < (4 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        exact_mod_cast h2
    · -- x = 7
      rw [h]
      constructor
      · -- 3 < Real.sqrt (2 * (7 : ℤ))
        rw [show (2 * (7 : ℤ) : ℝ) = (14 : ℝ) by norm_num]
        have h1 : (3 : ℝ) < Real.sqrt (14 : ℝ) := by
          rw [Real.lt_sqrt] <;> norm_num
        exact_mod_cast h1
      · -- Real.sqrt (2 * (7 : ℤ)) < (4 : ℝ)
        rw [show (2 * (7 : ℤ) : ℝ) = (14 : ℝ) by norm_num]
        have h2 : Real.sqrt (14 : ℝ) < (4 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        exact_mod_cast h2