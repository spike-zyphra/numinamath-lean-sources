import Mathlib

theorem algebra_19524 :
    IsLeast {y : ℝ | ∃ x, y = abs (x - 1) + abs (x - 1.5) + abs (x - 2)} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 1.5
    norm_num [abs]
  · -- Show that 1 is the least element
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : abs (x - 1) + abs (x - 1.5) + abs (x - 2) ≥ 1 := by
      by_cases h1 : x ≥ 2
      · -- x ≥ 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        nlinarith
      by_cases h1_5 : x ≥ 1.5
      · -- 1.5 ≤ x < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        nlinarith
      by_cases h1 : x ≥ 1
      · -- 1 ≤ x < 1.5
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        nlinarith
      · -- x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        nlinarith
    linarith [hx, h]