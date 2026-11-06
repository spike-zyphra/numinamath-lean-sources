import Mathlib

theorem algebra_739 :
    {(x, y) : ℝ × ℝ | abs (abs x - abs (x - 3.1415926)) + abs (abs (y + 11 / 8) - abs (2 * y - 7.13)) = 0} = {(1.5707963, (1151 / 600 : ℝ)), (1.5707963, (1701 / 200 : ℝ))} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume that (x, y) satisfies the equation, prove it is one of the two solutions
    intro h
    have h1 : abs (abs x - abs (x - 3.1415926)) = 0 := by
      linarith [abs_nonneg (abs x - abs (x - 3.1415926)), abs_nonneg (abs (y + 11 / 8) - abs (2 * y - 7.13))]
    have h2 : abs (abs (y + 11 / 8) - abs (2 * y - 7.13)) = 0 := by
      linarith [abs_nonneg (abs x - abs (x - 3.1415926)), abs_nonneg (abs (y + 11 / 8) - abs (2 * y - 7.13))]
    have h3 : abs x - abs (x - 3.1415926) = 0 := by
      rwa [abs_eq_zero] at h1
    have h4 : abs (y + 11 / 8) - abs (2 * y - 7.13) = 0 := by
      rwa [abs_eq_zero] at h2
    have hx1 : x = 1.5707963 := by
      cases abs_eq_abs.1 (by linarith : abs x = abs (x - 3.1415926)) with
      | inl h_left =>
        nlinarith
      | inr h_right =>
        nlinarith
    have hy1 : y = (1151 / 600 : ℝ) ∨ y = (1701 / 200 : ℝ) := by
      cases abs_eq_abs.1 (by linarith : abs (y + 11 / 8) = abs (2 * y - 7.13)) with
      | inl h_left =>
        right
        nlinarith
      | inr h_right =>
        left
        nlinarith
    rcases hy1 with h1 | h2
    · -- First solution
      left
      simp [hx1, h1]
      <;> norm_num
    · -- Second solution
      right
      simp [hx1, h2]
      <;> norm_num
  · -- Show that the two given solutions satisfy the equation
    rintro (h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl⟩
      norm_num [abs_of_nonneg, abs_of_nonpos]
      <;> norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl⟩
      norm_num [abs_of_nonneg, abs_of_nonpos]
      <;> norm_num