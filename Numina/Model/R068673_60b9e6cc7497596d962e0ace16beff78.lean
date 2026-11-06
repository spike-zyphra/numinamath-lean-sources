import Mathlib

theorem algebra_173529 (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 2 + b * x + c) (hroots : ¬∃ x, f x = 0) :
    ∀ x, f x + f (x - 1) - f (x + 1) > -4 * a := by
  intro x
  have hfx : f x = a * x^2 + b * x + c := hf x
  have hfx1 : f (x - 1) = a * (x - 1)^2 + b * (x - 1) + c := hf (x - 1)
  have hfx2 : f (x + 1) = a * (x + 1)^2 + b * (x + 1) + c := hf (x + 1)
  rw [hfx, hfx1, hfx2]
  have h2 : b ^ 2 - 4 * a * c < 0 := by 
    by_contra h
    push_neg at h
    have h3 : ∃ x, f x = 0 := by 
      use (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
      rw [hf]
      field_simp
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * a * c) by nlinarith), sq_nonneg (b + Real.sqrt (b ^ 2 - 4 * a * c)), sq_pos_of_ne_zero (show 2 * a ≠ 0 by nlinarith)]
    exact hroots h3
  nlinarith [sq_nonneg (a * x + (b - 4 * a) / 2), sq_nonneg (x - ( (4 * a - b) / (2 * a) )), sq_pos_of_pos ha, h2]