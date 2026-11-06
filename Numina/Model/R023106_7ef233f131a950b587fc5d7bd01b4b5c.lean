import Mathlib

theorem algebra_315733 (a b : ℝ) :
    ∃ x : ℝ, x^2 + 2 * (1 + a) * x + (3 * a^2 + 4 * a * b + 4 * b^2 + 2) = 0 ↔
    a = 1 ∧ b = -1 / 2 := by

  use -2
  constructor
  · -- Assume the equation equals zero, prove $a = 1 ∧ b = -1 / 2$
    intro h
    have h1 : 3 * a^2 + 4 * a * b + 4 * b^2 - 4 * a + 2 = 0 := by
      nlinarith
    have h2 : (a - 1) ^ 2 = 0 := by
      nlinarith [ sq_nonneg (a - 1), sq_nonneg (b + 1 / 2), sq_nonneg (a + 2 * b), sq_nonneg (a - 2 * b) ]
    have ha1 : a - 1 = 0 := by
      nlinarith [ h2 ]
    have ha : a = 1 := by
      nlinarith [ ha1 ]
    have hb : b = -1 / 2 := by
      rw [ha] at h1
      nlinarith
    constructor <;> tauto
  · -- Assume $ a = 1 ∧ b = -1 / 2 $ prove the equation equals zero
    rintro ⟨ha, hb⟩
    rw [ha, hb]
    norm_num