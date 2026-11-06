import Mathlib

/-The diagonals of a rhombus are $10$ inches and $24$ inches. What is the perimeter of the rhombus, in inches?-/
theorem algebra_13460 (a c d : ℝ) (h₀ : a > 0)
    (h₂ : c = 10) (h₃ : d = 24) (h₄ : a^2 = (c / 2)^2 + (d / 2)^2) :
    4 * a = 52 := by
  -- The diagonals are perpendicular bisectors of each other, so therefore the side length of the rhombus can be calculated as $\sqrt{5^2+12^2} = 13$. Therefore, the perimeter of the rhombus is $4 \times 13 = \boxed{52}$ inches.
  rw [h₂, h₃] at h₄
  norm_num at h₄
  have h₁: a = 13 := by
    rw [(by linarith : (169 : ℝ) = 13^2)] at h₄
    have h₄ := (Real.sqrt_inj (by linarith) (by linarith)).mpr h₄
    rw [Real.sqrt_sq (by linarith), Real.sqrt_sq (by linarith)] at h₄
    exact h₄
  rw [h₁]
  norm_num
