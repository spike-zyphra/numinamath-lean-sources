import Mathlib

theorem algebra_206546 (n : ℕ) :
    ∃ x : ℤ, x^2 - 3 * n * x + n + 3 = 0 ↔ n = 2 := by
  use 1
  constructor
  · -- Assume 1^2 - 3n*1 +n +3 =0, prove n =2
    intro h
    have h1 : (4 : ℤ) - 2 * (n : ℤ) = 0 := by
      norm_num at h ⊢
      linarith
    have hn : (n : ℤ) = 2 := by
      linarith
    have h2 : n = 2 := by
      exact_mod_cast hn
    exact h2
  · -- Assume n =2, prove 1^2 -3n*1 +n +3 =0
    intro h
    rw [h]
    norm_num