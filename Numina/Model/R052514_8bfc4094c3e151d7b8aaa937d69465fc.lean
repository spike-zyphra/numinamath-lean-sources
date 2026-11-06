import Mathlib

theorem number_theory_209046 (x : ℕ) (hx : x > 0) (h : 4 * x + 2 * (x / 3) + (x / 2) = 765) :
    x = 13 ∨ x = 41 ∨ x = 130 := by

  have h1 : x ≤ 191 := by
    omega

  interval_cases x <;> norm_num at h ⊢ <;> omega