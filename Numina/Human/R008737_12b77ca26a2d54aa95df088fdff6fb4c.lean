import Mathlib

/- Let $f(x) = ax^7 + bx^3 + cx - 5.$  If $f(-7) = 7,$ then find $f(7).$ -/
theorem algebra_14165 {a b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 7 + b * x ^ 3 + c * x - 5)
    (h : f (-7) = 7) : f 7 = -17 := by
  rw [hf] at h ⊢; linarith