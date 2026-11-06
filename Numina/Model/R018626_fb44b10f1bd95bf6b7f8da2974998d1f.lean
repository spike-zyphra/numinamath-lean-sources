import Mathlib

theorem algebra_228329 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : b = a + 6) (h2 : c = b + 3) (h3 : 3 / a + 4 / b = 9 / c) :
    a = 18 ∧ b = 24 ∧ c = 27 := by

  have h4 : c = a + 9 := by
    linarith [h1, h2]

  rw [show b = a + 6 by linarith [h1], show c = a + 9 by linarith [h4]] at h3

  have h5 : a ≠ 0 := by linarith
  have h6 : a + 6 ≠ 0 := by
    nlinarith [hb, h1]
  have h7 : a + 9 ≠ 0 := by
    nlinarith [hc, h4]

  field_simp [h5, h6, h7] at h3

  have h8 : 2 * a^2 - 27 * a - 162 = 0 := by
    nlinarith
  
  have ha2 : (a - 18) * (2 * a + 9) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp ha2) with ha18 ha9
  
  · -- Case where a = 18
    have ha18' : a = 18 := by linarith
    have hb24 : b = 24 := by
      linarith [h1, ha18']
    have hc27 : c = 27 := by
      linarith [h4, ha18']
    exact ⟨ha18', hb24, hc27⟩

  · -- Case where 2a + 9 = 0
    have h9 : a < 0 := by
      nlinarith
    linarith