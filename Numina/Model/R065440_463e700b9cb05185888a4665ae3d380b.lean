import Mathlib

theorem algebra_15293 (A : ℕ) (h : 0 ≤ A ∧ A ≤ 9) (h' : 9 ∣ (3000 + 100 * A + 10 * A + 1)) :
    A = 7 := by
  rcases h with ⟨h0, h9⟩
  interval_cases A <;> norm_num at h' <;> omega