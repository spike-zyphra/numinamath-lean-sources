import Mathlib

theorem algebra_48118 {x y : ℝ} (h₀ : Real.sin x + Real.cos y = 1) (h₁ : Real.sin y + Real.cos x = -1) :
    Real.cos (2 * x) = Real.cos (2 * y) := by
  have eq1 : Real.sin x = 1 - Real.cos y := by linarith [h₀]
  have eq2 : Real.sin y = -1 - Real.cos x := by linarith [h₁]
  have eq3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq4 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  rw [eq1] at eq3
  rw [eq2] at eq4
  have eq5 : -2 * Real.cos y + Real.cos y ^ 2 + Real.cos x ^ 2 = 0 := by
    nlinarith [eq3]
  have eq6 : 2 * Real.cos x + Real.cos x ^ 2 + Real.cos y ^ 2 = 0 := by
    nlinarith [eq4]
  have eq7 : Real.cos y = - Real.cos x := by
    nlinarith [eq5, eq6]
  have eq9 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  have eq10 : Real.cos (2 * y) = 1 - 2 * Real.sin y ^ 2 := by
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  have eq11 : Real.sin y ^ 2 = Real.sin x ^ 2 := by
    have h2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      linarith
    have h3 : Real.sin y ^ 2 = 1 - Real.cos y ^ 2 := by
      have h3 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
      linarith
    rw [eq7] at h3
    linarith [h2, h3]
  rw [eq9, eq10]
  linarith [eq11]