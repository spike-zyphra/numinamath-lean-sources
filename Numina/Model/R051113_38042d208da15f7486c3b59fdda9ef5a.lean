import Mathlib

theorem algebra_311843 : IsLeast {x | ∃ a : ℝ, x = abs (a + 1) + abs (a + 2) + abs (a + 3) + abs (a + 4)} 4 := by 
  constructor
  · -- Let's prove that 4 is in the set
    use -2.5
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num 
  · -- Now we need to show that 4 is the smallest
    intro x hx
    rcases hx with ⟨a, rfl⟩
    have h1 : abs (a + 1) + abs (a + 2) + abs (a + 3) + abs (a + 4) ≥ 4 := by 
      have h2 : abs (a + 1) + abs (a + 4) ≥ 3 := by 
        have h3 : abs (a + 1) + abs (a + 4) ≥ abs ((a + 1) - (a + 4)) := by 
          apply abs_sub
        have h4 : abs ((a + 1) - (a + 4)) = 3 := by
          norm_num [abs_of_nonneg, abs_of_nonpos]
          all_goals linarith
        linarith [h3, h4]
      have h5 : abs (a + 2) + abs (a + 3) ≥ 1 := by 
        have h6 : abs (a + 2) + abs (a + 3) ≥ abs ((a + 2) - (a + 3)) := by 
          apply abs_sub
        have h7 : abs ((a + 2) - (a + 3)) = 1 := by
          norm_num [abs_of_nonneg, abs_of_nonpos]
          all_goals linarith
        linarith [h6, h7]
      linarith [h2, h5]
    linarith [h1]