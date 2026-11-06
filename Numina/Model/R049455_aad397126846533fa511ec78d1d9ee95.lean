import Mathlib

theorem algebra_144874 (x : ℝ) :
    (Real.sin x)^6 + (Real.cos x)^6 + (Real.sin x)^2 =
    2 * (Real.sin x)^4 + (Real.cos x)^4 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    linarith [h1]
  have h3 : Real.cos x ^ 4 = (1 - Real.sin x ^ 2) ^ 2 := by
    calc
      Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
      _ = (1 - Real.sin x ^ 2) ^ 2 := by rw [h2]
  have h4 : Real.cos x ^ 6 = (1 - Real.sin x ^ 2) ^ 3 := by
    calc
      Real.cos x ^ 6 = (Real.cos x ^ 2) ^ 3 := by ring
      _ = (1 - Real.sin x ^ 2) ^ 3 := by rw [h2]
  rw [h4, h3]
  ring_nf
  <;> nlinarith [Real.sin_sq_le_one x, Real.cos_sq_le_one x]