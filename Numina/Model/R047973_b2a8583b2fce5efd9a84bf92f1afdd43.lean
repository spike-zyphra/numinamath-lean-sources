import Mathlib

theorem number_theory_113080 (a b : ℕ) (h : ∀ x : ℕ, ¬ Nat.Coprime (a * x + 2) (b * x + 3)) :
    a / b = 3 / 2 := by
  have h0 := h 0
  norm_num at h0
  all_goals tauto