import Mathlib

theorem algebra_240832 (x y : ℝ) (hx : x ≠ y) (hxy : 2 * x * y + 1 ≠ 0) :
    (6 * x ^ 2 * y ^ 2 + x * y - 1) / (2 * x * y + 1) < (x * (x ^ 2 - 1) - y * (y ^ 2 - 1)) / (x - y) := by
  have h1 : x - y ≠ 0 := by
    intro h'
    apply hx
    linarith

  have h2 : (x * (x ^ 2 - 1) - y * (y ^ 2 - 1)) / (x - y) = x^2 + y^2 + x * y - 1 := by
    have h3 : x - y ≠ 0 := h1
    field_simp [h3]
    ring_nf
    <;> field_simp [h3]
    <;> nlinarith
    all_goals nlinarith

  rw [h2]

  have h4 : (6 * x ^ 2 * y ^ 2 + x * y - 1) / (2 * x * y + 1) - (x^2 + y^2 + x * y - 1) < 0 := by
    have h5 : (6 * x ^ 2 * y ^ 2 + x * y - 1) / (2 * x * y + 1) - (x^2 + y^2 + x * y - 1) =
        ( (6 * x ^ 2 * y ^ 2 + x * y - 1) - (x^2 + y^2 + x * y - 1) * (2 * x * y + 1) ) / (2 * x * y + 1) := by
      field_simp [hxy]
      <;> ring
    rw [h5]

    have h5 : ( (6 * x ^ 2 * y ^ 2 + x * y - 1) - (x^2 + y^2 + x * y - 1) * (2 * x * y + 1) ) = - (x - y) ^ 2 * (2 * x * y + 1) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y)]

    rw [h5]

    have h6 : ( - (x - y) ^ 2 * (2 * x * y + 1) ) / (2 * x * y + 1) = - (x - y) ^ 2 := by
      field_simp [hxy]
      <;> ring

    rw [h6]

    have h7 : (x - y) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      exact h1

    nlinarith

  linarith