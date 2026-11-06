import Mathlib

theorem algebra_3108 {x : ℝ} (hx : x ≠ 0) (h : x ^ 2 - 5 * x + 8 / x = 15 / x - 8) :
    (x ^ 2 - 6 * x + 9) * (x ^ 2 - 2 * x + 2) ^ 2 = 1 := by
  have h1 : x ^ 3 - 5 * x ^ 2 + 8 = 15 - 8 * x := by
    have h1 : x ≠ 0 := hx
    have eq1 : x ^ 2 - 5 * x + 8 / x = 15 / x - 8 := h
    have eq2 : x * (x ^ 2 - 5 * x + 8 / x) = x * (15 / x - 8) := by
      rw [eq1]
    have eq3 : x * (x ^ 2 - 5 * x + 8 / x) = x ^ 3 - 5 * x ^ 2 + 8 := by
      have h1 : x ≠ 0 := hx
      field_simp [h1]
      <;> ring
    have eq4 : x * (15 / x - 8) = 15 - 8 * x := by
      have h1 : x ≠ 0 := hx
      field_simp [h1]
      <;> ring
    rw [eq3, eq4] at eq2
    linarith
  have h2 : x ^ 3 - 5 * x ^ 2 + 8 * x - 7 = 0 := by
    nlinarith [h1]
  have h3 : (x ^ 2 - 6 * x + 9) * (x ^ 2 - 2 * x + 2) ^ 2 = 1 := by
    nlinarith [sq_nonneg (x ^ 2 - 2 * x + 2), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 4 * x + 2), 
              sq_nonneg (x - 1), sq_nonneg (x * (x - 3)), sq_nonneg (x - 2), sq_nonneg (x - 7)]
  exact h3