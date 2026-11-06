import Mathlib

theorem number_theory_184596 (p : ℕ) (hp : p.Prime) (h : 4/23 < 1/p ∧ 1/p < 8/19) :
    p = 5 := by
  have h1 : 4 / 23 < 1 / p := h.1
  have h2 : 1 / p < 8 / 19 := h.2
  norm_num at h1 h2
  all_goals
    omega