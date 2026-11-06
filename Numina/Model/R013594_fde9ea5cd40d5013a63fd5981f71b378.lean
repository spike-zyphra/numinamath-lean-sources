import Mathlib

theorem algebra_276447 {a b c d x y : ℝ} (h1 : a * d - c * b ≠ 0) (h2 : a * x + b * y = 0)
    (h3 : c * x + d * y = 0) : x = 0 ∧ y = 0 := by

  have eq1 : (a * d - c * b) * x = 0 := by
    have eq2 : a * d * x + b * d * y = 0 := by
      have h4 : a * d * x + b * d * y = d * (a * x + b * y) := by
        ring
      rw [h4, h2]
      norm_num
    have eq3 : b * c * x + b * d * y = 0 := by
      have h5 : b * c * x + b * d * y = b * (c * x + d * y) := by
        ring
      rw [h5, h3]
      norm_num
    linarith
  have hx : x = 0 := by
    cases (mul_eq_zero.mp eq1) with
    | inl h4 => 
      exfalso
      apply h1
      linarith
    | inr h5 => 
      linarith
  have eq2 : (a * d - c * b) * y = 0 := by
    have eq3 : a * c * x + a * d * y = 0 := by
      have h4 : a * c * x + a * d * y = a * (c * x + d * y) := by
        ring
      rw [h4, h3]
      norm_num
    have eq4 : a * c * x + b * c * y = 0 := by
      have h5 : a * c * x + b * c * y = c * (a * x + b * y) := by
        ring
      rw [h5, h2]
      norm_num
    linarith
  have hy : y = 0 := by
    cases (mul_eq_zero.mp eq2) with
    | inl h4 => 
      exfalso
      apply h1
      linarith
    | inr h5 => 
      linarith
  constructor
  · exact hx
  · exact hy