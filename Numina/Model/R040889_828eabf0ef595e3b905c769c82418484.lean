import Mathlib

theorem algebra_997 (x : ℝ) (hx : x ≠ -3 / 2) (hx2 : x ≠ 4) :
    (2 * x + 3) / 4 + 4 / (2 * x + 3) = (4 - x) / 3 + 3 / (4 - x) ↔
    x = 0 ∨ x = 7 / 10 ∨ x = 5 / 2 := by
  constructor
  · -- Assume the left side, prove the right side
    intro h
    have h1 : 2 * x + 3 ≠ 0 := by
      intro h1
      apply hx
      linarith
    have h2 : 4 - x ≠ 0 := by
      intro h2
      apply hx2
      linarith
    field_simp [(show (2 * x + 3) ≠ 0 by intro h11; apply hx; linarith),
        (show (4 - x) ≠ 0 by intro h11; apply hx2; linarith)] at h
    have h3 : (x - 0) * (x - 7 / 10) * (x - 5 / 2) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show (2 * x + 3) ≠ 0 by intro h11; apply hx; linarith),
          sq_pos_of_ne_zero (show (4 - x) ≠ 0 by intro h11; apply hx2; linarith)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h4 h6
    · -- x - 0 = 0, so x = 0
      left
      linarith
    · -- x - 7/10 = 0, so x = 7/10
      right
      left
      linarith
    · -- x - 5/2 = 0, so x = 5/2
      right
      right
      linarith
  · -- Assume the right side, prove the left side
    rintro (h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 7/10
      rw [h]
      norm_num
    · -- x = 5/2
      rw [h]
      norm_num