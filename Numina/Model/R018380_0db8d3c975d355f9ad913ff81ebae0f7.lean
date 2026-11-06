import Mathlib

theorem number_theory_286103 {x : ℕ} (h : x / 7 = 12 ∧ x % 7 = 5) : x = 89 := by
  have h1 : x / 7 = 12 := h.1
  have h2 : x % 7 = 5 := h.2
  have h3 : x = 7 * 12 + 5 := by
    rw [←Nat.div_add_mod x 7]
    rw [h1, h2]
  norm_num at h3
  all_goals omega