import Mathlib

theorem algebra_326436 (x y z : ℝ) :
    abs (abs (x - y) + x + y - 2 * z) + abs (x - y) + x + y + 2 * z =
    4 * max (max x y) z := by
  have h1 : abs (x - y) + x + y = 2 * max x y := by
    cases max_cases x y with
    | inl h =>
      rw [abs_of_nonneg (by linarith)]
      linarith
    | inr h =>
      rw [abs_of_nonpos (by linarith)]
      linarith
  have h2 : abs (abs (x - y) + x + y - 2 * z) + abs (x - y) + x + y + 2 * z =
    2 * (abs (max x y - z) + max x y + z) := by
    have h3 : abs (x - y) + x + y = 2 * max x y := h1
    have h4 : abs (x - y) + x + y - 2 * z = 2 * (max x y - z) := by
      linarith
    rw [h4]
    have h5 : abs (2 * (max x y - z)) = 2 * abs (max x y - z) := by
      rw [abs_mul]
      norm_num
    rw [h5]
    linarith [h1]
  rw [h2]
  have h3 : abs (max x y - z) + max x y + z = 2 * max (max x y) z := by
    cases max_cases (max x y) z with
    | inl h =>
      rw [abs_of_nonneg (by linarith)]
      linarith
    | inr h =>
      rw [abs_of_nonpos (by linarith)]
      linarith
  linarith [h3]