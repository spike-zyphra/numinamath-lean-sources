import Mathlib

theorem inequalities_155632 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (x + 5 * y) + y / (y + 5 * x) ≤ 1 := by
  have h1 : 0 < x + 5 * y := by linarith [hx, hy]
  have h2 : 0 < y + 5 * x := by linarith [hx, hy]

  have h3 : x / (x + 5 * y) + y / (y + 5 * x) - 1 ≤ 0 := by
    have h4 : x * (y + 5 * x) + y * (x + 5 * y) - (x + 5 * y) * (y + 5 * x) = -24 * x * y := by
      nlinarith
    have h5 : (x / (x + 5 * y) + y / (y + 5 * x) - 1) =
        ( (x * (y + 5 * x) + y * (x + 5 * y) - (x + 5 * y) * (y + 5 * x)) ) / ( (x + 5 * y) * (y + 5 * x) ) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring

    rw [h5]
    rw [h4]
    have h6 : (x + 5 * y) * (y + 5 * x) > 0 := by positivity
    have h7 : -24 * x * y ≤ 0 := by nlinarith [mul_pos hx hy]

    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity

  linarith [h3]