import Mathlib

theorem inequalities_324235 (n k : ℕ) (h : 9 / 17 < n / (n + k) ∧ n / (n + k) < 8 / 15)
    (h' : ∀ k' : ℕ, 9 / 17 < n / (n + k') ∧ n / (n + k') < 8 / 15 → k' = k) :
    n = 17 ∨ n = 144 := by 
  have h1 : 9 / 17 < n / (n + k) := h.1
  have h2 : n / (n + k) < 8 / 15 := h.2
  norm_num at h1 h2 
  all_goals
    omega