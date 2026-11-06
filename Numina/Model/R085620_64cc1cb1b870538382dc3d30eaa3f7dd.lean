import Mathlib

theorem algebra_103173 {a b c x1 x2 : ℝ} (ha : a ≠ 0) (h1 : a * x1^2 + b * x1 + c = a * x2^2 + b * x2 + c)
    (hx1 : x1 ≠ x2) : a * (x1 + x2)^2 + b * (x1 + x2) + c = c := by
  have h2 : a * x1^2 + b * x1 + c - (a * x2^2 + b * x2 + c) = 0 := by linarith
  have h3 : a * (x1^2 - x2^2) + b * (x1 - x2) = 0 := by 
    linarith
  have h4 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · 
    exfalso
    exact hx1 (by linarith)
  · 
    have h7 : a * (x1 + x2)^2 + b * (x1 + x2) = 0 := by
      have : a * (x1 + x2)^2 + b * (x1 + x2) = (a * (x1 + x2) + b) * (x1 + x2) := by
        ring
      rw [this, h6]
      all_goals linarith
    linarith