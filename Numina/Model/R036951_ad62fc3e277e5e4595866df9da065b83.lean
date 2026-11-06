import Mathlib

theorem algebra_9218 :
    IsLeast {n : ℕ | n > 0 ∧ ∃ k : ℤ, Real.sqrt (27 * n) = k} 3 := by
  constructor
  -- Show 3 is in the set
  · constructor
    · norm_num
    · use 9
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  -- Show if n ∈ { ... | ... > 0 ∧ E k, Real.sqrt(27n) = (K : ℤ) } runs the minimum, 3.
  · intro n hn
    rcases hn with ⟨hn_pos, k, hk⟩
    by_contra h
    push_neg at h
    have h1 : n < 3 := by
      omega
    have h2 : n = 1 ∨ n = 2 := by
      interval_cases n <;> omega
    rcases h2 with (h2 | h2)
    · -- Case n = 1
      have h3 : (n : ℝ) = 1 := by
        exact_mod_cast h2
      have eq1 : Real.sqrt (27 * (n : ℝ)) = (Real.sqrt 27 : ℝ) := by
        rw [h3]
        all_goals norm_num
      rw [eq1] at hk
      have h4 : (Real.sqrt 27 : ℝ) = (k : ℝ) := by
        linarith [hk]
      have h5 : (Real.sqrt (27 : ℝ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
        rw [h4]
      have h6 : (Real.sqrt (27 : ℝ) : ℝ) ^ 2 = (27 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : (k : ℝ) ^ 2 = (27 : ℝ) := by
        nlinarith [h5, h6]
      have h8 : k ^ 2 = 27 := by
        exact_mod_cast (h7)
      have h9 : k ≤ 5 := by
        nlinarith [show k ^ 2 < 30 from by nlinarith]
      have h10 : k ≥ -5 := by
        nlinarith [show k ^ 2 < 30 from by nlinarith]
      interval_cases (k : ℤ) <;> omega
    · -- Case n = 2
      have h4 : (n : ℝ) = (2 : ℝ) := by
        exact_mod_cast h2
      have eq1 : Real.sqrt (27 * (n : ℝ)) = Real.sqrt (54 : ℝ) := by
        rw [h4]
        all_goals norm_num
      rw [eq1] at hk
      have h4 : Real.sqrt (54 : ℝ) = (k : ℝ) := by
        linarith [hk]
      have h5 : (Real.sqrt (54 : ℝ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
        rw [h4]
      have h6 : (Real.sqrt (54 : ℝ) : ℝ) ^ 2 = (54 : ℝ) := Real.sq_sqrt (by norm_num)
      have h7 : (k : ℝ) ^ 2 = (54 : ℝ) := by
        nlinarith [h5, h6]
      have h8 : k ^ 2 = 54 := by
        exact_mod_cast (h7)
      have h9 : k ≤ 7 := by
        nlinarith [show k ^ 2 < 55 by nlinarith]
      have h10 : k ≥ -7 := by
        nlinarith [show k ^ 2 < 55 by nlinarith]
      interval_cases (k : ℤ) <;> omega