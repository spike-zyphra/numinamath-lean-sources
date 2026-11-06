import Mathlib

theorem algebra_3565 {x y z : ℝ} (h1 : x + y = 2) (h2 : |z + 3| = x * y - 6 * y - 4) :
    x + 2 * y + 3 * z = -9 := by
  have hx : x = 2 - y := by linarith
  rw [hx] at h2
  have h5 : (z + 3) ^ 2 = 0 := by
    cases abs_cases (z + 3) with
    | inl hz =>
      have : (z + 3) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (y + 2)]
      assumption
    | inr hz =>
      have : (z + 3) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (y + 2)]
      assumption
  have h6 : z + 3 = 0 := by 
    rw [sq_eq_zero_iff] at h5
    exact h5
  have h7 : z = -3 := by linarith
  have h8 : y + 2 = 0 := by
    cases abs_cases (z + 3) with
    | inl hz =>
      have : y + 2 = 0 := by 
        nlinarith [sq_nonneg (y + 2)]
      assumption
    | inr hz =>
      have : y + 2 = 0 := by 
        nlinarith [sq_nonneg (y + 2)]
      assumption
  have h9 : y = -2 := by linarith
  have h10 : x = 4 := by 
    linarith
  linarith [h7, h9, h10]