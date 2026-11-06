import Mathlib

theorem algebra_3101 : {a : ℝ | a^3 = 658503} = {87} := by
  ext a
  simp
  constructor
  · intro ha
    have h1 : a^3 - 658503 = 0 := by linarith
    have h2 : (a - 87) * (a^2 + 87 * a + 87^2) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · linarith
    · have h5 : a^2 + 87 * a + 87^2 > 0 := by
        have h5 : a^2 + 87 * a + 87^2 = (a + 87 / 2)^2 + 3 * 87^2 / 4 := by ring
        have h6 : (a + 87 / 2)^2 ≥ 0 := sq_nonneg (a + 87 / 2)
        have h7 : 3 * 87^2 / 4 > 0 := by norm_num
        linarith
      linarith
  · intro ha
    rw [ha]
    norm_num