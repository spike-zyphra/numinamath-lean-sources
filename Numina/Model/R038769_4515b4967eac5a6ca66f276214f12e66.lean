import Mathlib

theorem other_28485 (a : ℕ → ℕ) (ha : ∀ n, a n = a (n - 1) + 1 ∨ a n = a (n - 1) + 2)
    (ha0 : a 0 = 1) :
    a 2014 = 1344 := by
  have h1 := ha 0
  simp [ha0] at h1
  all_goals omega