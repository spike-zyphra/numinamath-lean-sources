import Mathlib

theorem algebra_284621 {m n : ℝ} (h₀ : m ≠ n) (h₁ : m^2 = n + 2) (h₂ : n^2 = m + 2) :
    4 * m * n - m^3 - n^3 = 0 := by
  have h₃ : m^2 - n^2 = n - m := by linarith
  have h₄ : (m - n) * (m + n) = - (m - n) := by 
    linarith [h₃]
  have h₅ : m + n = -1 := by
    apply (mul_left_inj' (sub_ne_zero.mpr h₀)).mp
    linarith
  have h₆ : m * n = -1 := by
    nlinarith [sq_pos_of_ne_zero (show m - n ≠ 0 by
      intro h
      apply h₀
      linarith), h₁, h₂, h₅]
  have h₇ : m^3 + n^3 = -4 := by 
    have h₈ : m^3 + n^3 = (m + n)^3 - 3 * (m + n) * (m * n) := by 
      ring
    rw [h₈, h₅, h₆]
    nlinarith
  nlinarith [h₇, h₆]