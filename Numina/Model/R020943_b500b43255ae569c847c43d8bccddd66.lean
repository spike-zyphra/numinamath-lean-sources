import Mathlib

theorem algebra_275977 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c / b = b / a) :
    ∀ x, a * x ^ 2 + b * x + c > 0 := by

  have h1 : a * c = b ^ 2 := by
    have h2 : b ≠ 0 := by linarith
    have h3 : a ≠ 0 := by linarith
    field_simp [h2, h3] at h ⊢
    nlinarith

  intro x

  have h2 : a * x ^ 2 + b * x + c > 0 := by
    nlinarith [sq_nonneg (a * x + b / 2), sq_nonneg (x + b / 2), sq_nonneg (x + b / (2 * a)), 
          sq_nonneg (b ^ 2 - 4 * a * c), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          h1, sq_nonneg (x * a + b / 2), sq_nonneg (a * x + b / 2), sq_nonneg (x + (b / a)), sq_nonneg ((a * x) + b / 2)
    ]

  exact h2