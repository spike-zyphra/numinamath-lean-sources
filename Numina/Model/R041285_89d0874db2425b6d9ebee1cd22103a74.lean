import Mathlib

theorem inequalities_69410 (x y z t : ℝ)
    (h₁ : abs (x + y + z - t) ≤ 1)
    (h₂ : abs (y + z + t - x) ≤ 1)
    (h₃ : abs (z + t + x - y) ≤ 1)
    (h₄ : abs (t + x + y - z) ≤ 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 ≤ 1 := by
  have h11 : -1 ≤ x + y + z - t := by
    linarith [abs_le.mp h₁]
  have h12 : x + y + z - t ≤ 1 := by
    linarith [abs_le.mp h₁]
  have h21 : -1 ≤ y + z + t - x := by
    linarith [abs_le.mp h₂]
  have h22 : y + z + t - x ≤ 1 := by
    linarith [abs_le.mp h₂]
  have h31 : -1 ≤ z + t + x - y := by
    linarith [abs_le.mp h₃]
  have h32 : z + t + x - y ≤ 1 := by
    linarith [abs_le.mp h₃]
  have h41 : -1 ≤ t + x + y - z := by
    linarith [abs_le.mp h₄]
  have h42 : t + x + y - z ≤ 1 := by
    linarith [abs_le.mp h₄]
  nlinarith [sq_nonneg (x + y + z - t), sq_nonneg (y + z + t - x), sq_nonneg (z + t + x - y), sq_nonneg (t + x + y - z)]