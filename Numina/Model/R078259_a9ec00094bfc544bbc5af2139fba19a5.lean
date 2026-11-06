import Mathlib

theorem algebra_3183 :
    ∀ (x y : ℝ), Real.sin x ^ 2 * Real.cos y + Real.cos x ^ 2 * Real.cos y = Real.cos y := by 
  intro x y
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  calc
    Real.sin x ^ 2 * Real.cos y + Real.cos x ^ 2 * Real.cos y 
        = (Real.sin x ^ 2 + Real.cos x ^ 2) * Real.cos y := by ring
    _ = 1 * Real.cos y := by rw [h1]
    _ = Real.cos y := by ring