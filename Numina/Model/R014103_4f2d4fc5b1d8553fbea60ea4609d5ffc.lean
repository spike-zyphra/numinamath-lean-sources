import Mathlib

theorem algebra_19415 {A B C : ℝ} (hA : A > 0) (hB : B > 0) (hC : C > 0)
    (h : ∀ x, 24 * x ^ 2 - 19 * x - 35 = (A * x - 5) * (2 * B * x + C)) :
    A * B - 3 * C = -9 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1 : ℝ)
  have eq4 := h (2 : ℝ)
  have hC_eq : C = 7 := by
    nlinarith
  have h1 : 2 * A * B = 24 := by
    have eq1 := h 1
    have eq2 := h (0 : ℝ)
    have eq3 := h (-1 : ℝ)
    simp [hC_eq] at eq1 eq2 eq3
    nlinarith [mul_pos hA hB]
  have h2 : 7 * A - 10 * B = -19 := by
    have eq1 := h 1
    have eq2 := h (-1 : ℝ)
    simp [hC_eq] at eq1 eq2
    nlinarith [mul_pos hA hB]
  have h3 : A = 3 := by
    nlinarith [h1, h2, mul_pos hA hB]
  have h4 : B = 4 := by
    nlinarith [h1, h3, mul_pos hA hB]
  rw [h3, h4, hC_eq]
  norm_num