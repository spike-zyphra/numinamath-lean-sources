import Mathlib

theorem algebra_12910 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * (x - 4) ^ 2 + 1 = a * x ^ 2)
    (h' : a * (-4) ^ 2 + 1 = 4) :
    a = 1 / 4 ∧ b = 2 ∧ c = 3 := by 
  have h1 := h 0
  have h2 := h 4
  have h3 := h 2
  have h4 := h 1
  have h5 := h (-4)
  have h6 := h 5
  have eq1 := h 2
  have eq2 := h 1
  norm_num at h1 h2 h3 h4 h5 h6 eq1 eq2 h'
  all_goals 
    linarith