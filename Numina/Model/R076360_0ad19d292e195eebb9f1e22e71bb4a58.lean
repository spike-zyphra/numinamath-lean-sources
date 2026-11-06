import Mathlib

theorem number_theory_210923 (a : ℕ → ℤ) (ha : ∀ n, a n = 1 ∨ a n = -1) :
    ∃ b : ℕ → ℤ, (∀ n, b n = 1 ∨ b n = -1) ∧
      13 ∣ ∑ i ∈ Finset.range 8, b i * 8^(7 - i) := by
  use fun n => 1
  constructor
  · -- Prove that for all n, b(n) = 1 ∨ b(n) = -1.
    intro n
    left
    rfl
  · -- Show 13 ∣ ∑ i ∈ Finset.range 8, (1 : ℤ) * 8^(7 - i)
    norm_num [Finset.sum_range_succ]