import Mathlib

theorem number_theory_8189 (p : ℕ) (hp : Nat.Prime p) :
    ∃ k, k^2 = p^3 - 4 * p + 9 ↔ p = 2 ∨ p = 7 := by

  -- Now, we will prove the bi-directional implication
  -- Check if p = 2: compute k^2 = 9
  -- Check if p = 7: compute k^2 = 324
  by_cases hp2 : p = 2
  · -- Case 1: p = 2
    use 3
    rw [hp2]
    all_goals norm_num
  · -- Case 2: p ≠ 2, check p = 7
    by_cases hp7 : p = 7
    · -- Case 2a: p = 7
      use 18
      rw [hp7]
      all_goals norm_num
    · -- Case 2b: p ≠ 2 and p ≠ 7
      use 0
      simp [hp2, hp7]
      all_goals omega