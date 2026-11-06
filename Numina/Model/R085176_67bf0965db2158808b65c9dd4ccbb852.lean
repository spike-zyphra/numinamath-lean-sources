import Mathlib

theorem algebra_301341 (a b : ℝ) (ha : a < b) (f : ℝ → ℝ)
    (hf : ∀ x, f x = abs (x - a) - abs (x - b)) :
    IsLeast {x | ∃ y, f y = x} (a - b) := by
  constructor
  · -- First, we need to prove that (a - b) is attained by f
    use a
    rw [hf a]
    have h1 : abs (a - a) = 0 := by simp
    have h2 : abs (a - b) = b - a := by
      rw [abs_of_neg (show a - b < 0 by linarith)]
      ring
    rw [h1, h2]
    all_goals linarith
  · -- Now, we need to prove that (a - b) is the smallest value
    intro x hx
    rcases hx with ⟨y, hy⟩
    rw [hf y] at hy
    by_cases h1 : y ≥ b
    · -- Case 1: y ≥ b
      rw [abs_of_nonneg (show y - a ≥ 0 by linarith), abs_of_nonneg (show y - b ≥ 0 by linarith)] at hy
      linarith
    · -- Case 2: y < b, so either y < a or a ≤ y < b
      by_cases h2 : y ≥ a
      · -- Subcase 2a: a ≤ y < b
        rw [abs_of_nonneg (show y - a ≥ 0 by linarith), abs_of_nonpos (show y - b ≤ 0 by linarith)] at hy
        all_goals linarith
      · -- Case 2b: y < a
        rw [abs_of_nonpos (show y - a ≤ 0 by linarith), abs_of_nonpos (show y - b ≤ 0 by linarith)] at hy
        all_goals linarith