import Mathlib

theorem algebra_52336 {a b c d : ℝ} (h1 : a * b + c + d = 3) (h2 : b * c + d + a = 5)
    (h3 : c * d + a + b = 2) (h4 : d * a + b + c = 6) :
    (a, b, c, d) = (2, 0, 0, 3) := by

  have eq5 : (b - 1) * (c - a) = 2 := by
    nlinarith

  have eq6 : (c - 1) * (b - d) = 3 := by
    nlinarith

  have eq7 : (d - 1) * (a - c) = 4 := by
    nlinarith

  have eq8 : (a - 1) * (b - d) = -3 := by
    nlinarith

  have eq9 : a + c = 2 := by
    have eq10 : (a + c - 2) * (b - d) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 eq10) with h10 h11
    ·
      linarith
    ·
      have eq12 : (a - 1) * (b - d) = -3 := eq8
      rw [show b - d = (0 : ℝ) by linarith] at eq12
      nlinarith

  have eq10 : c = 2 - a := by
    linarith

  have eq11 : (b - 1) * (1 - a) = 1 := by
    have eq12 : (b - 1) * (c - a) = 2 := eq5
    rw [show c = 2 - a by linarith] at eq12
    have eq13 : (b - 1) * ((2 - a : ℝ) - a) = 2 := by
      linarith
    have eq14 : (2 - a : ℝ) - a = 2 * (1 - a : ℝ) := by
      nlinarith
    rw [eq14] at eq13
    nlinarith

  have eq16 : (d - 1) * (a - 1) = 2 := by
    have eq17 : (d - 1) * (a - c : ℝ) = 4 := by
      linarith
    rw [show c = 2 - a by linarith] at eq17
    have eq18 : (a - (2 - a)) = 2 * (a - 1) := by
      nlinarith
    rw [eq18] at eq17
    nlinarith

  have eq17 : a * b + c + d = 3 := h1
  rw [show c = 2 - a by linarith] at eq17
  have eq18 : a * b - a + d = 1 := by
    nlinarith

  have eq14 : 2 * b + d = 3 := by
    nlinarith

  have eq17 : (a - 2) * (b - 1) = 0 := by
    have eq19 : a * b - a - 2 * b = -2 := by
      have eq20 : d = 3 - 2 * b := by
        nlinarith
      rw [eq20] at eq18
      nlinarith
    nlinarith

  cases' (mul_eq_zero.1 eq17) with h h
  ·
    have ha2 : a = 2 := by
      linarith
    have hc0 : c = 0 := by
      linarith
    have hb0 : b = 0 := by
      have eq22 : (b - 1) * (1 - a : ℝ) = 1 := eq11
      rw [show a = (2 : ℝ) by linarith] at eq22
      nlinarith
    have h13 : d = 3 := by
      nlinarith
    simp [ha2, hb0, hc0, h13]
  ·
    have hb1 : b = 1 := by
      linarith
    rw [hb1] at eq11
    nlinarith