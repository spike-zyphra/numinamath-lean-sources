import Mathlib

theorem number_theory_64663 (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a ^ 2 + a + 1 : ℚ) / (b ^ 2 + b + 1) = n ^ 2 + n + 1 := by

  use (n + 1) ^ 2, n + 1
  constructor
  · -- Show a is positive
    have hn' : 0 < n := hn
    have a_pos : 0 < (n + 1) ^ 2 := by
      have : n + 1 > 0 := by linarith
      positivity
    exact a_pos
  constructor
  · -- Show b is positive
    have hn' : 0 < n := hn
    have : n + 1 > 0 := by linarith
    positivity
  · -- Show $\frac{a^2 +a +1}{b^2+b+1} = n^2 +n +1$
    field_simp
    <;> ring_nf