import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_1550 :
  IsGreatest {y : ℝ | ∃ x, y = (3 - 4 * x) / (x ^ 2 + 1)} 4 ∧
  IsLeast {y : ℝ | ∃ x, y = (3 - 4 * x) / (x ^ 2 + 1)} (-1) := by
  constructor
  · -- We need to show that 4 is the greatest value of the function.
    constructor
    · -- First part of IsGreatest: show that 4 is in the image.
      use (-1 / 2)
      norm_num
    · -- Second part of IsGreatest: show that for any y in the image, y ≤ 4.
      intro y
      rintro ⟨x, hx⟩
      rw [hx]
      have h1 : (3 - 4 * x) / (x ^ 2 + 1) ≤ 4 := by
        have h2 : x ^ 2 + 1 > 0 := by
          nlinarith [sq_nonneg x]
        have h4 : (3 - 4 * x) ≤ 4 * (x ^ 2 + 1) := by
          nlinarith [sq_nonneg (x + 1 / 2)]
        have h5 : (3 - 4 * x) / (x ^ 2 + 1) ≤ 4 := by
          apply (div_le_iff₀ (by positivity)).mpr
          linarith [h4, sq_nonneg (x ^ 2 + 1)]
        linarith
      linarith
  · -- We need to show that -1 is the least value of the function.
    constructor
    · -- First part of IsLeast: show that -1 is in the image.
      use (2 : ℝ)
      norm_num
    · -- Second part of IsLeast: show that any y in the image is ≥ -1.
      intro y
      rintro ⟨x, hx⟩
      rw [hx]
      have h1 : (3 - 4 * x) / (x ^ 2 + 1) ≥ -1 := by
        have h2 : x ^ 2 + 1 > 0 := by
          nlinarith [sq_nonneg x]
        have h4 : (3 - 4 * x) ≥ -1 * (x ^ 2 + 1) := by
          nlinarith [sq_nonneg (x - 2)]
        have h5 : (3 - 4 * x) / (x ^ 2 + 1) ≥ -1 := by
          apply (le_div_iff₀ (by positivity)).mpr
          linarith [h4, sq_nonneg (x ^ 2 + 1)]
        linarith
      linarith