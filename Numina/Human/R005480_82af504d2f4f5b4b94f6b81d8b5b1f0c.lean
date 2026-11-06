import Mathlib

/-Explain how any unit fraction 1/n can be decomposed into other unit fractions.-/
theorem number_theory_608454: ∀ n: ℕ, 0 < n → (1: ℚ) / n = 1 / (2 * n) + 1 / (3 * n) + 1 / (6 * n) := by
  -- we decompose 1/n into 1/2*n + 1/3*n + 1/6*n --
  intro n
  intro hn
  field_simp
  ring_nf
