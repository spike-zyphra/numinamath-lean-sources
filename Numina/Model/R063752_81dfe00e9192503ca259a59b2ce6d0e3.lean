import Mathlib

theorem algebra_304996 :
    IsLeast {x : ℝ | ∃ a b, x = max (max (|a + b|) (|a - b|)) (|1 - b|)} (1 / 2) := by
  constructor
  · -- Show 1/2 is in the set
    use 0, 1 / 2
    norm_num [abs_of_nonneg, abs_of_nonpos, max_eq_left, max_eq_right]
  · -- Show 1/2 is the least in the set
    rintro x ⟨a, b, rfl⟩
    by_contra h
    push_neg at h
    -- Suppose max (max (|a + b|) (|a - b|)) (|1 - b|) < 1/2
    -- This implies all three expressions must be less than 1/2
    have h1 : max (max (|a + b|) (|a - b|)) (|1 - b|) < (1 / 2 : ℝ) := by 
      simpa using h
    have h2 : max (|a + b|) (|a - b|) < (1 / 2 : ℝ) := by
      have h2 : max (|a + b|) (|a - b|) ≤ max (max (|a + b|) (|a - b|)) (|1 - b|) := by
        apply le_max_left
      linarith
    have h3 : |1 - b| < (1 / 2 : ℝ) := by
      have h3 : |1 - b| ≤ max (max (|a + b|) (|a - b|)) (|1 - b|) := by
        apply le_max_right
      linarith
    have h4 : |a + b| < (1 / 2 : ℝ) := by
      have h4 : |a + b| ≤ max (|a + b|) (|a - b|) := by
        apply le_max_left
      linarith
    have h5 : |a - b| < (1 / 2 : ℝ) := by
      have h5 : |a - b| ≤ max (|a + b|) (|a - b|) := by
        apply le_max_right
      linarith
    -- From |1 - b| < 1/2, derive 1/2 < b < 3/2
    have h6 : (1 / 2 : ℝ) < b := by
      linarith [abs_lt.mp h3]
    have h7 : b < (3 / 2 : ℝ) := by
      linarith [abs_lt.mp h3]
    -- From |a + b| < 1/2
    have h8 : - (1 / 2 : ℝ) < a + b := by 
      linarith [abs_lt.mp h4]
    have h9 : a + b < (1 / 2 : ℝ) := by 
      linarith [abs_lt.mp h4]
    -- From |a - b| < 1/2
    have h10 : - (1 / 2 : ℝ) < a - b := by 
      linarith [abs_lt.mp h5]
    have h11 : a - b < (1 / 2 : ℝ) := by 
      linarith [abs_lt.mp h5]
    -- Now deriving the contradiction
    linarith