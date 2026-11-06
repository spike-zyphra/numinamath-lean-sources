import Mathlib

theorem algebra_5283 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ t = (2 * x + 3 * y) * (8 / x + 3 / y)} 49 := by
  constructor
  · -- Show that 49 is achievable, with x = 2 and y = 1
    use 2, 1
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 49 is the least element of the set
    rintro t ⟨x, y, hx, hy, ht⟩
    have h1 : (2 * x + 3 * y) * (8 / x + 3 / y) ≥ 49 := by
      have h2 : (2 * x + 3 * y) * (8 / x + 3 / y) = 25 + 6 * (x / y) + 24 * (y / x) := by
        field_simp
        ring_nf
      rw [h2]
      have h3 : 6 * (x / y) + 24 * (y / x) ≥ 24 := by
        have h4 : x / y > 0 := by
          apply div_pos
          all_goals linarith
        have h5 : y / x > 0 := by
          apply div_pos
          all_goals linarith
        have h6 : (x / y) * (y / x) = 1 := by
          field_simp
          <;> nlinarith
        nlinarith [sq_nonneg (x / y - 2), sq_nonneg ((y / x) - 2), sq_nonneg (x / y - 4 * (y / x)), sq_nonneg (x / y), sq_nonneg (y / x),
                  sq_nonneg (x / y - 2 * (y / x)), sq_nonneg (x / y - 4), sq_nonneg ((y / x) - 1 / 4),
                  mul_nonneg (show (0 : ℝ) ≤ x / y by linarith) (show (0 : ℝ) ≤ y / x by linarith)]
      linarith
    linarith [h1, ht]