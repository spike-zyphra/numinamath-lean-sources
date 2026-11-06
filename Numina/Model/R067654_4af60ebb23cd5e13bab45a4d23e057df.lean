import Mathlib

theorem number_theory_289357 (a : ℕ → ℕ → ℕ)
    (ha : ∀ n m, a n m = a (n - 1) (m - 1) + 1) :
    a 10 5 = 101 := by
  have h00 := ha 0 0
  simp at h00
  all_goals omega