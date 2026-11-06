import Mathlib

theorem algebra_291436 {x : ℝ} (hx : x > 0) (h : x^3 + 1 / x^3 + x^6 + 1 / x^6 = 2754) :
    x + 1 / x = 4 := by

  have eq1 : x^6 + 1 / x^6 = (x^3 + 1 / x^3) ^ 2 - 2 := by
    field_simp
    <;> ring
  have eq2 : x^3 + 1 / x^3 + x^6 + 1 / x^6 = (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2 := by
    linarith [eq1]

  have eq3 : (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2 = 2754 := by
    linarith [h, eq2]

  have eq4 : x^3 + 1 / x^3 = 52 := by
    have h1 : (x^3 + 1 / x^3) ^ 2 + (x^3 + 1 / x^3) - 2756 = 0 := by linarith [eq3]
    have h2 : (x^3 + 1 / x^3 - 52) * (x^3 + 1 / x^3 + 53) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Show that x^3 + 1/x^3 = 52
      linarith
    · -- Show that x^3 + 1/x^3 + 53 = 0 is impossible
      have h6 : x ^ 3 + 1 / x ^ 3 > 0 := by
        have h7 : x ^ 3 > 0 := by positivity
        have h8 : 1 / x ^ 3 > 0 := by
          apply div_pos
          norm_num
          positivity
        linarith
      nlinarith

  have eq5 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) = 52 := by
    have eq4' : x^3 + 1 / x^3 = 52 := eq4
    have eq6 : x ^ 3 + 1 / x ^ 3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      field_simp
      <;> ring
    linarith [eq4', eq6]

  have eq6 : (x + 1 / x) = 4 := by
    have eq7 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) - 52 = 0 := by linarith [eq5]
    have h2 : ((x + 1 / x) - 4) * ((x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case ((x + 1 / x) - 4) = 0
      linarith
    · -- Case ((x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13) = 0
      have h7 : (x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13 = 0 := h4
      nlinarith [sq_nonneg (x + 1 / x + 2)]

  exact eq6