import Mathlib

/- Let $A$ and $B$ be real numbers such that $\frac{A}{x-5}+B(x+1)=\frac{-3x^2+12x+22}{x-5}$. What is $A+B$? -/
theorem algebra_10274 {A B : ℝ} (h : ∀ x, x ≠ 5 → A / (x - 5) + B * (x + 1) = (-3 * x ^ 2 + 12 * x + 22) / (x - 5)) :
    A + B = 4 := by 
  have h₁ := h 6
  have h₂ := h 4
  have h₃ := h 7
  norm_num at h₁ h₂ h₃
  linarith