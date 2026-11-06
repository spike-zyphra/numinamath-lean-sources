import Mathlib

theorem algebra_178434 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : ∃ x : ℕ, a * x - 6 = b * x - 4) (h2 : ∀ x : ℕ, a * x - 6 = b * x - 4 → x = 2) :
    (a = 7 ∧ b = 5) ∨ (a = 4 ∧ b = 3) := by

  have h8 := h2 0 (by
    simp
  )

  all_goals
    omega