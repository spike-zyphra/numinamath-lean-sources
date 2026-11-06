import Mathlib

theorem algebra_241351 (x y a b : ℝ) (h₀ : 2 * Real.sin x - 3 * Real.cos y = a)
    (h₁ : 2 * Real.cos x + 3 * Real.sin y = b) :
    Real.sin (x - y) = (13 - a^2 - b^2) / 12 := by
  have h2 : Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
    rw [Real.sin_sub]
  have eq1 : a^2 + b^2 = 4 * (Real.sin x)^2 + 9 * (Real.cos y)^2 + 4 * (Real.cos x)^2 + 9 * (Real.sin y)^2 + 12 * (Real.cos x * Real.sin y - Real.sin x * Real.cos y) := by
    calc
      a^2 + b^2 = (2 * Real.sin x - 3 * Real.cos y) ^ 2 + (2 * Real.cos x + 3 * Real.sin y) ^ 2 := by
        rw [show a = 2 * Real.sin x - 3 * Real.cos y by linarith [h₀], show b = 2 * Real.cos x + 3 * Real.sin y by linarith [h₁]]
      _ = 4 * (Real.sin x)^2 + 9 * (Real.cos y)^2 + 4 * (Real.cos x)^2 + 9 * (Real.sin y)^2 + 12 * (Real.cos x * Real.sin y - Real.sin x * Real.cos y) := by
        ring
  have eq2 : 4 * (Real.sin x)^2 + 4 * (Real.cos x)^2 = 4 := by
    have h2 : (Real.sin x)^2 + (Real.cos x)^2 = 1 := Real.sin_sq_add_cos_sq x
    linarith
  have eq3 : 9 * (Real.cos y)^2 + 9 * (Real.sin y)^2 = 9 := by
    have h3 : (Real.cos y)^2 + (Real.sin y)^2 = 1 := Real.cos_sq_add_sin_sq y
    nlinarith
  have eq4 : 4 * (Real.sin x)^2 + 9 * (Real.cos y)^2 + 4 * (Real.cos x)^2 + 9 * (Real.sin y)^2 = 13 := by
    nlinarith [eq2, eq3, Real.sin_sq_add_cos_sq x, Real.cos_sq_add_sin_sq y]
  have eq5 : Real.sin x * Real.cos y - Real.cos x * Real.sin y = (13 - a^2 - b^2) / 12 := by
    nlinarith [eq1, eq4, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.cos_sq_add_sin_sq y, Real.cos_sq_add_sin_sq x]
  rw [h2]
  linarith [eq5]