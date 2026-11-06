import Mathlib

theorem algebra_323222 {a b : ℝ} (h : a^4 - 2 * b^4 ≠ 0) (h' : a^2 * b^2 = a^4 - 2 * b^4) :
    (a^2 - b^2) / (19 * a^2 + 96 * b^2) = 1 / 134 := by
  have h1 : (a^2)^2 - a^2 * b^2 - 2 * b^4 = 0 := by
    nlinarith
  have h2 : (a^2 - 2 * b^2) * (a^2 + b^2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case $a^2 - 2b^2 = 0$
    have ha2 : a^2 = 2 * b^2 := by linarith
    have eq1 : a^2 - b^2 = b^2 := by
      nlinarith
    have eq2 : 19 * a^2 + 96 * b^2 = 134 * b^2 := by
      nlinarith [ha2]
    have hb2 : b^2 ≠ 0 := by
      by_contra h1
      have : b^2 = 0 := by nlinarith
      have hb0 : b = 0 := by
        nlinarith [this]
      have : a^4 - 2 * b^4 = 0 := by
        rw [show b^4 = 0 by
          have : b = 0 := hb0
          nlinarith
        ]
        have ha0 : a^2 = 0 := by nlinarith [ha2, this]
        have : a = 0 := by
          nlinarith [ha0]
        nlinarith
      contradiction
    have eq3 : (a^2 - b^2) / (19 * a^2 + 96 * b^2) = (b^2) / (134 * b^2) := by
      rw [eq1, eq2]
    have eq4 : (b^2) / (134 * b^2) = 1 / 134 := by
      have : b^2 ≠ 0 := hb2
      field_simp
      <;> nlinarith
    rw [eq3, eq4]
  · -- Case $a^2 + b^2 = 0$
    have h5 : a^2 + b^2 = 0 := by linarith
    have ha0 : a^2 ≥ 0 := by nlinarith
    have hb0 : b^2 ≥ 0 := by nlinarith
    have h6 : a^2 = 0 := by nlinarith [h5, ha0, hb0]
    have h7 : b^2 = 0 := by nlinarith [h5, h6, hb0]
    have : a^4 - 2 * b^4 = 0 := by
      have ha0' : a = 0 := by
        nlinarith [h6]
      have hb0' : b = 0 := by
        nlinarith [h7]
      nlinarith [ha0', hb0']
    contradiction