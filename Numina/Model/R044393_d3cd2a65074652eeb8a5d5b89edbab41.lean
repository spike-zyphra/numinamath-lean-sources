import Mathlib

theorem algebra_200757 {x y : ℝ} : abs (x - 1) + abs (x + y) = 6 ∧ abs (y - 1) + abs (x + y + 1) = 4 ↔
    (x = -2 ∧ y = -1) ∨ (x = -14 / 3 ∧ y = 13 / 3) := by
  constructor
  · -- Forward direction: Prove that equations hold solutions
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h3 : x - 1 ≥ 0
    · -- Assume x ≥ 1
      have h1' : abs (x - 1) = x - 1 := abs_of_nonneg h3
      by_cases h4 : x + y ≥ 0
      · -- Assume x + y ≥ 0
        have h1'' : abs (x + y) = x + y := abs_of_nonneg h4
        by_cases h5 : y - 1 ≥ 0
        · -- Assume y ≥ 1
          have h6 : abs (y - 1) = y - 1 := abs_of_nonneg h5
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
        · -- Assume y < 1
          have h6 : abs (y - 1) = -(y - 1) := abs_of_neg (show y - 1 < 0 by linarith)
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
      · -- Assume x + y < 0
        have h1'' : abs (x + y) = -(x + y) := abs_of_neg (show x + y < 0 by linarith)
        by_cases h5 : y - 1 ≥ 0
        · -- Assume y ≥ 1
          have h6 : abs (y - 1) = y - 1 := abs_of_nonneg h5
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
        · -- Assume y < 1
          have h6 : abs (y - 1) = -(y - 1) := abs_of_neg (show y - 1 < 0 by linarith)
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
    · -- Assume x < 1
      have h1' : abs (x - 1) = -(x - 1) := abs_of_neg (show x - 1 < 0 by linarith)
      by_cases h4 : x + y ≥ 0
      · -- Assume x + y ≥ 0
        have h1'' : abs (x + y) = x + y := abs_of_nonneg h4
        by_cases h5 : y - 1 ≥ 0
        · -- Assume y ≥ 1
          have h6 : abs (y - 1) = y - 1 := abs_of_nonneg h5
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
        · -- Assume y < 1
          have h6 : abs (y - 1) = -(y - 1) := abs_of_neg (show y - 1 < 0 by linarith)
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
      · -- Assume x + y < 0
        have h1'' : abs (x + y) = -(x + y) := abs_of_neg (show x + y < 0 by linarith)
        by_cases h5 : y - 1 ≥ 0
        · -- Assume y ≥ 1
          have h6 : abs (y - 1) = y - 1 := abs_of_nonneg h5
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            right
            constructor
            · -- Show x = -14/3
              linarith
            · -- Show y = 13/3
              linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            exfalso
            linarith
        · -- Assume y < 1
          have h6 : abs (y - 1) = -(y - 1) := abs_of_neg (show y - 1 < 0 by linarith)
          by_cases h7 : x + y + 1 ≥ 0
          · -- Assume x + y + 1 ≥ 0
            have h8 : abs (x + y + 1) = x + y + 1 := abs_of_nonneg h7
            exfalso
            linarith
          · -- Assume x + y + 1 < 0
            have h8 : abs (x + y + 1) = -(x + y + 1) := abs_of_neg (show x + y + 1 < 0 by linarith)
            left
            constructor
            · -- Show x = -2
              linarith
            · -- Show y = -1
              linarith
  · -- Backward direction: Prove equations from solutions
    rintro (h | h)
    · -- First solution
      rcases h with ⟨hx, hy⟩
      constructor
      · -- Check the first equation
        rw [show x = -2 by linarith, show y = -1 by linarith]
        norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos]
      · -- Check the second equation
        rw [show x = -2 by linarith, show y = -1 by linarith]
        norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos]
    · -- Second solution
      rcases h with ⟨hx, hy⟩
      constructor
      · -- Check the first equation
        rw [show x = -14 / 3 by linarith, show y = 13 / 3 by linarith]
        norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos]
      · -- Check the second equation
        rw [show x = -14 / 3 by linarith, show y = 13 / 3 by linarith]
        norm_num [abs_of_nonneg, abs_of_nonpos, abs_of_nonneg, abs_of_nonpos]