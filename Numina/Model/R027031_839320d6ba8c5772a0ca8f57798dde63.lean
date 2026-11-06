import Mathlib

theorem algebra_55053 {a b c d : ℝ}
    (h₀ : a + b - c - d = 3)
    (h₁ : a * b - 3 * b * c + c * d - 3 * d * a = 4)
    (h₂ : 3 * a * b - b * c + 3 * c * d - d * a = 5) :
    11 * (a - c) ^ 2 + 17 * (b - d) ^ 2 = 63 := by
  have eq1 : (a - c) + (b - d) = 3 := by
    linarith
  have eq2 : (a - c) * (b - d) = 9 / 4 := by
    have h3 : a * b - 3 * b * c + c * d - 3 * d * a + (3 * a * b - b * c + 3 * c * d - d * a) = 4 + 5 := by
      linarith [h₁, h₂]
    have h4 : a * b - 3 * b * c + c * d - 3 * d * a + (3 * a * b - b * c + 3 * c * d - d * a) =
        4 * (a * b - b * c + c * d - d * a) := by
      ring
    have h5 : a * b - b * c + c * d - d * a = 9 / 4 := by
      linarith
    have h6 : (a - c) * (b - d) = a * b - b * c + c * d - d * a := by
      ring
    rw [h6, h5]
  have eq3 : a - c = 3 / 2 := by
    have h7 : (a - c) + (b - d) = 3 := eq1
    have h8 : (a - c) * (b - d) = 9 / 4 := eq2
    have h9 : (a - c - 3 / 2) ^ 2 = 0 := by
      have h10 : b - d = 3 - (a - c) := by linarith
      rw [h10] at h8
      nlinarith
    have h11 : a - c - 3 / 2 = 0 := by
      apply pow_eq_zero
      exact h9
    linarith
  have eq4 : b - d = 3 / 2 := by
    linarith [eq3, eq1]
  rw [show (a - c) = 3 / 2 by linarith [eq3], show (b - d) = 3 / 2 by linarith [eq4]]
  norm_num