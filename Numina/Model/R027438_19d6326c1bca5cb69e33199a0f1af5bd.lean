import Mathlib

theorem algebra_228024 (x : ℝ) :
    (3 * Real.sqrt ((x + 1)^2) + Real.sqrt (x^2 - 4 * x + 4)) =
    (|1 + 6 * x| - 4 * |x - 1|) ↔ x ∈ Set.Icc 1 2 := by
  constructor
  · -- Assume the equation holds, prove x ∈ [1, 2]
    intro h_eq
    have h1 : Real.sqrt ((x + 1) ^ 2) = abs (x + 1) := by
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (x^2 - 4 * x + 4) = abs (x - 2) := by
      have h3 : x^2 - 4 * x + 4 = (x - 2) ^ 2 := by
        ring
      rw [h3]
      have h4 : Real.sqrt ((x - 2) ^ 2) = abs (x - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      linarith [h4]
    rw [h1, h2] at h_eq

    constructor
    · -- Show that 1 ≤ x
      by_cases h3 : x ≥ 1
      · -- Case where x ≥ 1
        by_cases h4 : x ≤ 2
        · -- Case where 1 ≤ x ≤ 2
          have h5 : abs (x + 1) = x + 1 := by
            rw [abs_of_nonneg]
            nlinarith
          have h6 : abs (x - 2) = 2 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = 1 + 6 * x := by
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = x - 1 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          rw [h5, h6, h7, h8] at h_eq
          all_goals nlinarith
        · -- Case where x > 2
          have h4' : x > 2 := by linarith
          have h5 : abs (x + 1) = x + 1 := by
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h6 : abs (x - 2) = x - 2 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = 1 + 6 * x := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = x - 1 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          rw [h5, h6, h7, h8] at h_eq
          all_goals nlinarith 
      · -- Case where x < 1
        by_cases h4 : x ≥ -1
        · -- Case where x ∈ [-1, 1)
          by_cases h6 : 1 + 6 * x ≥ 0
          · -- Case where 1 + 6 * x ≥ 0
            -- so x ≥ -1/6
            -- Subcase where x ∈ [-1/6, 1)
            -- Derive substitutions
            have h5 : abs (x + 1) = x + 1 := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h6' : abs (x - 2) = 2 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h7 : abs (1 + 6 * x) = 1 + 6 * x := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h8 : abs (x - 1) = 1 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            -- Now make substitution in eq
            -- RHS =
            -- (1 + 6x) -4 (1 - x) = 1 + 6x -4 + 4x = -3 + 10x
            -- LHS = x + 1 : (x+ 1 2x 5)!
            -- 3 * (x+1) + (2 - x) = 3x + 3 + 2 - x = (x+2) + (x+5-5)!
            -- wait a substitution step is still needed 
            -- solving  | to simplifies
            -- so  l1=a  l3=d  l6=e  
            linarith [h5, h6', h7, h8, h_eq]
          · -- Case where 1 + 6 * x < 0 
            -- so x < -1/6
            -- Subcase where x ∈ [-1, -1/6)
            have h5 : abs (x + 1) = x + 1 := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h6' : abs (x - 2) = 2 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h7 : abs (1 + 6 * x) = - (1 + 6 * x) := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h8 : abs (x - 1) = 1 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            linarith [h5, h6', h7, h8, h_eq]
        · -- Case where x < -1
          have h4' : x < -1 := by nlinarith
          have h5 : abs (x + 1) = -(x + 1) := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h6 : abs (x - 2) = 2 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = - (1 + 6 * x) := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = 1 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          linarith [h5, h6, h7, h8, h_eq]
    · -- Show that x ≤ 2
      by_cases h3 : x ≥ 1
      · -- Case where x ≥ 1
        by_cases h4 : x ≤ 2
        · -- Case where 1 ≤ x ≤ 2
          have h5 : abs (x + 1) = x + 1 := by
            rw [abs_of_nonneg]
            nlinarith
          have h6 : abs (x - 2) = 2 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = 1 + 6 * x := by
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = x - 1 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          rw [h5, h6, h7, h8] at h_eq
          all_goals nlinarith
        · -- Case where x > 2
          have h4' : x > 2 := by linarith
          have h5 : abs (x + 1) = x + 1 := by
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h6 : abs (x - 2) = x - 2 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = 1 + 6 * x := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = x - 1 := by 
            rw [abs_of_nonneg]
            all_goals 
            nlinarith
          rw [h5, h6, h7, h8] at h_eq
          all_goals nlinarith
      · -- Case where x < 1
        by_cases h4 : x ≥ -1
        · -- Case where x ∈ [-1, 1)
          by_cases h6 : 1 + 6 * x ≥ 0
          · -- Case where 1 + 6 * x ≥ 0
            have h5 : abs (x + 1) = x + 1 := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h6' : abs (x - 2) = 2 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h7 : abs (1 + 6 * x) = 1 + 6 * x := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h8 : abs (x - 1) = 1 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            linarith [h5, h6', h7, h8, h_eq]
          · -- Case where 1 + 6 * x < 0 
            have h5 : abs (x + 1) = x + 1 := by
              rw [abs_of_nonneg]
              all_goals 
              nlinarith
            have h6' : abs (x - 2) = 2 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h7 : abs (1 + 6 * x) = - (1 + 6 * x) := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            have h8 : abs (x - 1) = 1 - x := by
              rw [abs_of_nonpos]
              all_goals 
              nlinarith
            linarith [h5, h6', h7, h8, h_eq]
        · -- Case where x < -1
          have h4' : x < -1 := by nlinarith
          have h5 : abs (x + 1) = -(x + 1) := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h6 : abs (x - 2) = 2 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h7 : abs (1 + 6 * x) = - (1 + 6 * x) := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          have h8 : abs (x - 1) = 1 - x := by 
            rw [abs_of_nonpos]
            all_goals 
            nlinarith
          linarith [h5, h6, h7, h8, h_eq]
  · -- Assume x ∈ [1, 2], prove the equation
    rintro ⟨h1, h2⟩
    have h1 : Real.sqrt ((x + 1) ^ 2) = abs (x + 1) := by
      rw [Real.sqrt_sq_eq_abs]
    have h2 : Real.sqrt (x^2 - 4 * x + 4) = abs (x - 2) := by 
      have h3 : x^2 - 4 * x + 4 = (x - 2) ^ 2 := by 
        ring
      rw [h3]
      have h4 : Real.sqrt ((x - 2) ^ 2) = abs (x - 2) := by
        rw [Real.sqrt_sq_eq_abs]
      linarith [h4]
    rw [h1, h2]
    have h3 : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg]
      nlinarith
    have h4 : abs (x - 2) = 2 - x := by 
      rw [abs_of_nonpos]
      all_goals
      nlinarith
    have h5 : abs (1 + 6 * x) = 1 + 6 * x := by 
      rw [abs_of_nonneg]
      all_goals
      nlinarith
    have h6 : abs (x - 1) = x - 1 := by 
      rw [abs_of_nonneg]
      all_goals 
      nlinarith
    rw [h3, h4, h5, h6]
    all_goals
    linarith