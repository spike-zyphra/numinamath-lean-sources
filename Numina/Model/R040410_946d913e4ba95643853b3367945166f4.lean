import Mathlib

theorem number_theory_124391 (a : ℕ → ℕ) (ha : ∀ n, a n > 0)
    (h1 : a 1 = 11) (h2 : a 2 = 13) (h3 : ∀ n, a (n + 2) = a n + 2 * a (n + 1)) :
    IsGreatest {k | ∃ m, ∀ i ∈ Finset.range k, Nat.Prime (a (m + i))} 5 := by
  have h4 := h3 0
  simp [h1, h2] at h4
  all_goals linarith [ha 0, ha 1, ha 2]