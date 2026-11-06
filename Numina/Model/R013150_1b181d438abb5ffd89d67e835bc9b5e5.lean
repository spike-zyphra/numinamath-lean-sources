import Mathlib

theorem algebra_310077 (f : ℝ → ℝ) (hf : ∀ x, x < 0 → f x = 0) (hf' : ∀ x, x ≥ 0 → f x = 1) :
    ∀ x, f (f x) = 1 := by
  intro x
  have h1 : f x = 0 ∨ f x = 1 := by
    by_cases h2 : x < 0
    · -- Case where x < 0
      left
      apply hf x h2
    · -- Case where x ≥ 0
      right
      apply hf' x (by linarith)
  rcases h1 with (h | h)
  · -- Case where f x = 0, so we need to compute f 0
    rw [h]
    -- Now we need to show f 0 = 1
    norm_num [hf']
  · -- Case where f x = 1, so we need to compute f 1
    rw [h]
    -- Now we need to show f 1 = 1
    norm_num [hf']