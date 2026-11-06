import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21721 : IsGreatest {x | ¬∃ y, x = y ∧ y^2 - 5 ≠ 0 ∧ (y - 2) / (y^2 - 5) > 0} (Real.sqrt 5) := by
  constructor
  · -- Show that sqrt(5) is in the set
    show ¬∃ y, Real.sqrt 5 = y ∧ y^2 - 5 ≠ 0 ∧ (y - 2) / (y^2 - 5) > 0
    rintro ⟨y, hy1, hy2, hy3⟩
    have h1 : y = Real.sqrt 5 := by linarith
    rw [h1] at hy2
    have h2 : (Real.sqrt 5 : ℝ) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    have h3 : (Real.sqrt 5 : ℝ) ^ 2 - (5 : ℝ) = (0 : ℝ) := by linarith [h2]
    contradiction
  · -- Show that sqrt(5) is the greatest element in the set
    intro x hx
    have h1 : ¬∃ y, x = y ∧ y^2 - 5 ≠ 0 ∧ (y - 2) / (y^2 - 5) > 0 := by simpa using hx
    by_contra h
    push_neg at h
    -- Assume x > sqrt(5), derive a contradiction with h1
    have h2 : ∃ y, x = y ∧ y^2 - 5 ≠ 0 ∧ (y - 2) / (y^2 - 5) > 0 := by
      use x
      constructor
      · -- Show x = x
        rfl
      constructor
      · -- Show x^2 - 5 ≠ 0
        have h3 : x ^ 2 - (5 : ℝ) ≠ 0 := by
          have h4 : x > Real.sqrt 5 := by linarith
          have h5 : x ^ 2 > (5 : ℝ) := by
            have h6 : x > Real.sqrt 5 := by linarith
            have h7 : x ^ 2 > (Real.sqrt 5) ^ 2 := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
            have h8 : (Real.sqrt 5 : ℝ) ^ 2 = (5 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
            nlinarith [h7, h8]
          -- If x² > 5, then x² - 5 ≠ 0
          by_contra h
          have : x ^ 2 = (5 : ℝ) := by linarith
          linarith
        exact h3
      · -- Show (x - 2) / (x ^ 2 - 5) > 0
        have hx4 : (x - 2) / (x ^ 2 - 5) > 0 := by
          apply div_pos
          · -- Show x - 2 > 0
            have h5 : Real.sqrt 5 > (2 : ℝ) := by
              have h1 : (2 : ℝ) ^ 2 < (5 : ℝ) := by norm_num
              have h2 : (2 : ℝ) < Real.sqrt 5 := by
                nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
              linarith
            have h3 : x > (2 : ℝ) := by nlinarith [show Real.sqrt 5 > (2 : ℝ) by linarith [h5], h]
            linarith
          · -- Show x ^ 2 - 5 > 0
            have h3 : x ^ 2 - (5 : ℝ) > 0 := by
              have h4 : x > Real.sqrt 5 := by linarith
              have h5 : x ^ 2 > (5 : ℝ) := by
                have h6 : x > Real.sqrt 5 := by linarith
                have h7 : x ^ 2 > (Real.sqrt 5) ^ 2 := by nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
                have h8 : (Real.sqrt 5 : ℝ) ^ 2 = (5 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
                nlinarith [h7, h8]
              linarith
            linarith
        simpa using hx4
    contradiction