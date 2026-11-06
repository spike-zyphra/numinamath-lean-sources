import Mathlib

theorem algebra_252229 {x : ℝ} (hx : x > 0) (h : x^2 + 1 / x^2 = 7) :
    x^5 + 1 / x^5 = 123 := by

  have h1 : x + 1 / x = 3 := by
    have h1 : x + 1 / x > 0 := by
      have hx1 : x > 0 := hx
      have hx2 : 1 / x > 0 := by positivity
      linarith

    have h2 : (x + 1 / x) ^ 2 = 9 := by
      have h2 : (x + 1 / x) ^ 2 = x^2 + 1 / x^2 + 2 := by
        field_simp
        <;> ring
      rw [h2, h]
      all_goals norm_num

    have h3 : x + 1 / x = 3 := by
      nlinarith [sq_nonneg (x + 1 / x - 3), sq_nonneg (x + 1 / x + 3), h1]
    exact h3

  have h2 : x^3 + 1 / x^3 = 18 := by
    have h2 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      <;> ring
    rw [h2, h1]
    all_goals norm_num

  have h3 : x^4 + 1 / x^4 = 47 := by
    have h3 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
      field_simp
      <;> ring
    rw [h3, h]
    all_goals norm_num

  have h4 : x^5 + 1 / x^5 = (x + 1 / x) * (x^4 + 1 / x^4) - (x^3 + 1 / x^3) := by
    field_simp
    <;> ring

  rw [h4, h1, h3, h2]
  all_goals norm_num