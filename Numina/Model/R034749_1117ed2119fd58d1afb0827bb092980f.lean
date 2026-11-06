import Mathlib

theorem inequalities_892
    (a b c : ℝ)
    (ha : a < b)
    (hb : b < c)
    (hc : c < 0) :
    c / (a + b) < b / (c + a) ∧ b / (c + a) < a / (b + c) := by

  have h1 : a < 0 := by linarith
  have h2 : b < 0 := by linarith
  have h3 : c < 0 := by linarith

  have h4 : a + b < 0 := by linarith
  have h5 : c + a < 0 := by linarith
  have h6 : b + c < 0 := by linarith

  constructor
  · -- Show $\frac{c}{a+b} < \frac{b}{c+a}$
    have h7 : (c - b) * (c + b + a) < 0 := by
      have h8 : c - b > 0 := by linarith
      have h9 : c + b + a < 0 := by linarith
      nlinarith

    have h10 : c / (a + b) - b / (c + a) < 0 := by
      have h11 : (a + b) < 0 := h4
      have h12 : (c + a) < 0 := h5
      have h13 : c * (c + a) - b * (a + b) < 0 := by
        have : c * (c + a) - b * (a + b) = (c - b) * (c + b + a) := by
          nlinarith
        rw [this]
        linarith
      have h14 : c / (a + b) - b / (c + a) = (c * (c + a) - b * (a + b)) / ((a + b) * (c + a)) := by
        field_simp [(show (a + b : ℝ) ≠ 0 by nlinarith), (show (c + a : ℝ) ≠ 0 by nlinarith)]
        <;> ring
      rw [h14]
      have h15 : (a + b) * (c + a) > 0 := by
        have h16 : (a + b) < 0 := h4
        have h17 : (c + a) < 0 := h5
        nlinarith
      apply div_neg_of_neg_of_pos
      linarith
      linarith

    linarith

  · -- Show $\frac{b}{c+a} < \frac{a}{b+c}$
    have h8 : (b - a) * (b + a + c) < 0 := by
      have h9 : b - a > 0 := by linarith
      have h10 : b + a + c < 0 := by linarith
      nlinarith

    have h14 : b / (c + a) - a / (b + c) < 0 := by
      have h12 : (c + a) < 0 := h5
      have h13 : (b + c) < 0 := h6
      have h14 : b * (b + c) - a * (c + a) < 0 := by
        have : b * (b + c) - a * (c + a) = (b - a) * (b + a + c) := by
          nlinarith
        rw [this]
        linarith
      have h15 : b / (c + a) - a / (b + c) = (b * (b + c) - a * (c + a)) / ((c + a) * (b + c)) := by
        field_simp [(show (c + a : ℝ) ≠ 0 by nlinarith), (show (b + c : ℝ) ≠ 0 by nlinarith)]
        <;> ring
      rw [h15]
      have h16 : (c + a) * (b + c) > 0 := by
        have h17 : (c + a) < 0 := h5
        have h18 : (b + c) < 0 := h6
        nlinarith
      apply div_neg_of_neg_of_pos
      linarith
      linarith

    linarith