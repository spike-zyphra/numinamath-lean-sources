import Mathlib

theorem algebra_9808
  {a b : ℂ}
  (ha : a^2 + 7*a + 23 = 0)
  (hb : b^2 + 7*b + 23 = 0)
  (hab : a ≠ b) :
  a^3 + b^3 = 140 := by

  have h1 : a + b = -7 := by
    have h2 : a^2 + 7*a + 23 - (b^2 + 7*b + 23) = 0 := by
      rw [show a^2 + 7*a + 23 - (b^2 + 7*b + 23) = (a^2 + 7*a + 23) - (b^2 + 7*b + 23) by ring]
      rw [ha, hb]
      all_goals norm_num
    have h3 : (a - b) * (a + b + 7) = 0 := by
      ring_nf at h2 ⊢
      simpa using h2
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- a - b = 0
      exfalso
      apply hab
      have : a = b := by
        have h7 : a - b = 0 := h4
        have : a = b := by
          calc
            a = b + (a - b) := by ring_nf
            _ = b + 0 := by rw [h7]
            _ = b := by ring_nf
        assumption
      assumption
    · -- a + b + 7 = 0
      have h8 : a + b = -7 := by
        calc
          a + b = (a + b + 7) - 7 := by ring_nf
          _ = -7 := by rw [h5]; all_goals ring_nf
      exact h8

  have h2 : a * b = 23 := by
    have h3 : a^2 + b^2 + 7 * (a + b) + 46 = 0 := by
      calc
        a^2 + b^2 + 7 * (a + b) + 46 = (a^2 + 7*a + 23) + (b^2 + 7*b + 23) := by ring_nf
        _ = 0 + 0 := by rw [ha, hb]
        _ = (0 : ℂ) := by ring_nf

    have h4 : a^2 + b^2 = 3 := by
      rw [h1] at h3
      simp [pow_two, Complex.ext_iff] at h3 ⊢
      constructor <;> nlinarith

    have h5 : (a + b) ^ 2 = a^2 + 2 * (a * b) + b^2 := by ring
    rw [h1] at h5
    simp [pow_two, Complex.ext_iff] at h4 h5 ⊢
    constructor <;> nlinarith

  have h3 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by ring
  rw [h3]
  rw [h1, h2]
  simp [pow_three, Complex.ext_iff]
  <;> norm_num