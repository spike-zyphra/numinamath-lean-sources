import Mathlib

theorem number_theory_99423 {n : ℕ} 
    (hn : ∃ k, n = k * (k + 1)) (h : 6 < n) :
  ∃ m p, n = m + p ∧ ∃ q, m = q * (q + 1) ∧ ∃ r, p = 3 * (r * (r + 1)) := by
  rcases hn with ⟨k, rfl⟩
  use k * (k + 1), 0
  constructor
  · -- Show the equality k * (k + 1) = k * (k + 1) + 0
    simp
  · -- Show m = k * (k + 1)
    use k
    constructor
    · -- Show the equality k * (k + 1) = k * (k + 1)
      rfl
    · -- Show p = 3 * (0 * (0 + 1))
      use 0
      all_goals
        simp