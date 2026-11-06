import Mathlib

theorem algebra_13626 : IsLeast {n : ℝ | ∃ x, n = abs (x ^ 2 - 4 * x + 9)} 5 := by
  constructor
  · -- Prove that 5 belongs to the set
    use 2
    norm_num [abs_of_nonneg]
  · -- Prove that 5 is a lower bound
    intro n hn
    rcases hn with ⟨x, hx⟩
    have h1 : abs (x ^ 2 - 4 * x + 9) ≥ 5 := by
      have h2 : x^2 - 4 * x + 9 ≥ 5 := by
        nlinarith [sq_nonneg (x - 2)]
      rw [abs_of_nonneg (by linarith)]
      linarith
    linarith [hx, h1]