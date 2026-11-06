import Mathlib

/- If the square root of the length of the hypotenuse of a right triangle is 2 units, what is the sum of the squares of the length of the two other sides? -/
theorem algebra_20688 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : Real.sqrt c = 2) :
    a^2 + b^2 = 16 := by
  -- $c = 4$ since $\sqrt{c} = 2$ and $c > 0$.
  have ceq : c = 4 := by
    apply congrArg (fun x ↦ x ^ 2) at h₄
    rw [Real.sq_sqrt (by linarith)] at h₄
    norm_num [h₄]
  -- $a^2 + b^2 = 16$ since $a^2 + b^2 = c^2$ and $c = 4$.
  norm_num [h₃, ceq]
