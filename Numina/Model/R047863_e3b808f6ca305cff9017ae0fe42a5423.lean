import Mathlib

theorem algebra_167513 (x y z : ℝ) (h₁ : Real.sin x + Real.sin y + Real.sin z = 0)
    (h₂ : Real.sin x + Real.sin y - Real.sin z = 0) (h₃ : Real.cos x + Real.cos y + Real.cos z = 0)
    (h₄ : Real.cos x + Real.cos y - Real.cos z = 0) :
    Real.cos x ^ 2 + Real.cos y ^ 2 + Real.cos z ^ 2 = 3 / 2 := by
  have h5 : Real.sin z = 0 := by
    linarith
  have h6 : Real.cos z = 0 := by
    linarith
  -- Now with h5 Real.sin z = 0 and h6 Real.cos z = 0
  have eq4 : Real.sin z ^ 2 + Real.cos z ^ 2 = 0 := by
    rw [h5, h6]
    norm_num
  have eq5 : Real.sin z ^ 2 + Real.cos z ^ 2 = 1 := Real.sin_sq_add_cos_sq z
  have h8 : (0 : ℝ) = 1 := by linarith [eq4, eq5]
  have h9 : False := by nlinarith
  exfalso
  exact h9