import Mathlib

theorem algebra_20508 (x : ℝ) :
    (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) = 5 ↔
    x = 1 / 2 ∨ x = -1 / 12 := by
  constructor
  · -- Assume left side is true, need to prove right side
    intro h
    have h1 : (12 * x - 1) * (6 * x - 1) * (4 * x - 1) * (3 * x - 1) - 5 = 0 := by linarith
    have h2 : (x - 1 / 2) * (x + 1 / 12) = 0 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 12), sq_nonneg (6 * x - 2), sq_nonneg (12 * x + 1),
          sq_nonneg ((12 * x) ^ 2 - 25 * (12 * x) + 144)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- h3: x - 1/2 = 0
      left
      linarith
    · -- h4: x + 1/12 = 0
      right
      linarith
  · -- Assume right side is true, need to prove left side
    rintro (h | h)
    · -- h: x = 1/2
      rw [h]
      norm_num
    · -- h: x = -1/12
      rw [h]
      norm_num