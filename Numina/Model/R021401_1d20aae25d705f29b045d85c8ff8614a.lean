import Mathlib

theorem other_65171 (a : ℕ → ℚ) (ha : ∀ n, a n = 11 * a (n - 1) - n)
    (ha' : ∀ n, 0 < a n) :
    IsLeast {x | ∃ a : ℕ → ℚ, (∀ n, a n = 11 * a (n - 1) - n) ∧ (∀ n, 0 < a n) ∧ x = a 1} (121 / 11) := by
  have h1 := ha 0
  have h2 := ha' 0
  norm_num at h1
  norm_num at h2
  all_goals
    linarith