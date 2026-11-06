import Mathlib

theorem number_theory_323106 (n : ℕ) :
    ¬∃ m, (m * (m + 1)) = n ^ 2 + 3 * n + 3 := by
  intro h
  rcases h with ⟨m, hm⟩
  by_cases h : m > n + 1
  · -- Case where m > n + 1
    have h1 : m * (m + 1) > (n + 1) * (n + 2) := by
      nlinarith [sq_pos_of_pos (show m - (n + 1) > 0 by omega), sq_nonneg (m - (n + 1)), sq_nonneg (m - n - 2)]
    nlinarith
  · -- Case where m ≤ n + 1
    have h2 : m ≤ n + 1 := by omega
    nlinarith [sq_nonneg (m - (n + 1)), sq_nonneg (m - (n + 2))]