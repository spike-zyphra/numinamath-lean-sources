import Mathlib

theorem algebra_11872 (x : ℝ) : (3 : ℝ)^(2*x^2-5*x+2) = (3 : ℝ)^(2*x^2+7*x-4) ↔
    x = 1/2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 1/2
    intro h
    have h1 : 2 * x^2 - 5 * x + 2 = 2 * x^2 + 7 * x - 4 := by
      apply_fun (Real.logb 3) at h
      simp at h ⊢
      linarith
    nlinarith
  · -- Backward direction: if x = 1/2, then the equation holds
    intro h
    rw [h]
    norm_num
    <;> norm_num