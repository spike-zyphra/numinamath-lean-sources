import Mathlib

/- If $f(x)=ax^4-bx^2+x+5$ and $f(-3)=2,$ then what is the value of $f(3)$? -/
theorem algebra_20843 {a b : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₁ : f (-3) = 2) : f 3 = 8 := by 
  rw [h₀] at h₁; simp_all
  linarith