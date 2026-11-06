import Mathlib

/- If $x, y, z$ are real numbers such that $x y=6, x-z=2$, and $x+y+z=9$, compute $\frac{x}{y}-\frac{z}{x}-\frac{z^{2}}{x y}$. Proposed by: Ragulan Sivakumar -/
theorem algebra_610208 (x y z : ℝ) (h₁ : x * y = 6) (h₂ : x - z = 2) (h₃ : x + y + z = 9) :
    x / y - z / x - z ^ 2 / (x * y) = 2 := by
  -- Multiply both sides by x * y
  field_simp
  -- We have x ≠ 0 and y ≠ 0 because x * y = 6
  have ⟨hx, hy⟩ : x ≠ 0 ∧ y ≠ 0 := by
    constructor
    all_goals
      rintro rfl
      simp at h₁
  ring_nf
  -- Simplify the expression
  rw [show x * y * z * x⁻¹ = y * z by field_simp; ring,
      show x ^ 2 * y * y⁻¹ = x ^ 2 by field_simp]
  -- Now the goal is a linear combination of the given equations
  linear_combination -3 * h₁ + (x + y + z) * h₂ + 2 * h₃
