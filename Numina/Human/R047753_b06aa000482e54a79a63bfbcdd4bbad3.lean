import Mathlib

/- There exists a positive real number $x$ such that $\cos \left(\tan ^{-1}(x)\right)=x$. Find the value of $x^{2}$.-/
theorem algebra_611195 (x : ℝ) (h₀ : 0 < x) (h₁ : Real.cos (Real.arctan x) = x) : x ^ 2 = (-1 + Real.sqrt 5) / 2 := by
  -- Square both sides of cos(arctan x) = x.
  have h₂ : Real.cos (Real.arctan x) ^ 2 = x ^ 2 := by
    rw [h₁]
  -- We have 1 / (1 + x²) = x².
  rw [Real.cos_sq_arctan] at h₂
  -- We have x⁴ + x² - 1 = 0.
  have h₃ : (2 * x ^ 2 + 1) ^ 2 = (Real.sqrt 5) ^ 2 := by
    field_simp at h₂ ⊢
    linarith
  -- Since x > 0, we have x² = (-1 + √5) / 2.
  rw [sq_eq_sq₀] at h₃
  linarith
  positivity
  positivity
  