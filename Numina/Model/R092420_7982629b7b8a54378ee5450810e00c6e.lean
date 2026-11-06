import Mathlib

theorem number_theory_105460 (a : ℕ → ℕ) (ha : ∀ n, a n = 8 ∨ a n = 9) :
    ∀ n, a n + a (n + 1) ≤ 18 := by
  intro n
  have h1 : a n = 8 ∨ a n = 9 := ha n
  have h2 : a (n + 1) = 8 ∨ a (n + 1) = 9 := ha (n + 1)
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> simp [h1, h2] at *
  <;> omega