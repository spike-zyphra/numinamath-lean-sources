import Mathlib

theorem number_theory_19529 (x : ℕ) (hx : x < 75) (h : x % 2 = 1 ∧ x % 3 = 1 ∧ x % 4 = 1 ∧ x % 6 = 1 ∧ x % 7 = 0) :
    x = 49 := by
  rcases h with ⟨h2, h3, h4, h6, h7⟩
  interval_cases x <;> norm_num at h2 h3 h4 h6 h7 <;> omega