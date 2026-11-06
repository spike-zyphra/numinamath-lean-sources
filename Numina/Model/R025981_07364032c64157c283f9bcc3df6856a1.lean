import Mathlib

theorem inequalities_189997 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    3 * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) -
    8 * (x / y + y / x) + 10 ≥ 0 := by

  have h1 : x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 = (x ^ 4 + y ^ 4) / (x ^ 2 * y ^ 2) := by
    field_simp [hx, hy]
    <;> ring

  have h2 : x / y + y / x = (x ^ 2 + y ^ 2) / (x * y) := by
    field_simp [hx, hy]
    <;> ring

  have h3 : 3 * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) - 8 * (x / y + y / x) + 10 ≥ 0 := by

    have h4 : 3 * (x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2) - 8 * (x / y + y / x) + 10 =
        (3 * (x ^ 4 + y ^ 4) - 8 * (x ^ 2 + y ^ 2) * (x * y) + 10 * (x ^ 2 * y ^ 2)) / (x ^ 2 * y ^ 2) := by
      field_simp [hx, hy, h1, h2]
      <;> ring

    rw [h4]

    have h5 : x ^ 2 * y ^ 2 > 0 := by
      positivity

    have h6 : (3 * (x ^ 4 + y ^ 4) - 8 * (x ^ 2 + y ^ 2) * (x * y) + 10 * (x ^ 2 * y ^ 2)) ≥ 0 := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 2), sq_nonneg (x * y - 1), sq_nonneg (x * y + 1), sq_nonneg (x * y + 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x), sq_nonneg (y)]

    have h7 : (3 * (x ^ 4 + y ^ 4) - 8 * (x ^ 2 + y ^ 2) * (x * y) + 10 * (x ^ 2 * y ^ 2)) / (x ^ 2 * y ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      nlinarith

    linarith

  linarith [h3]