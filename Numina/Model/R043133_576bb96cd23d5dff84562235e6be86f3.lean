import Mathlib

theorem number_theory_266741 (n : ℤ) : 3 * (n + 1) ∣ (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) := by
  have h1 : n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3 = 3 * (n + 1) * (n ^ 2 + 2 * n + 3) := by
    ring
  rw [h1]
  use n ^ 2 + 2 * n + 3
  all_goals ring