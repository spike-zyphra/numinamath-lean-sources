import Mathlib

theorem algebra_2089 {a b c : ℝ} (ha : 0 < a) (hb : b < 0) (hc : c < b) (h : a + b + c = 1)
    (M N P : ℝ) (hM : M = (b + c) / a) (hN : N = (a + c) / b) (hP : P = (a + b) / c) : M > P ∧ P > N := by

  have hp1 : M > P := by
    rw [hM, hP]
    have h1 : 0 < a := ha
    have h2 : c < 0 := by linarith
    have h3 : a * c < 0 := by nlinarith
    have h4 : (b + c) / a - (a + b) / c > 0 := by
      have h5 : (b + c) / a - (a + b) / c = ((b + c) * c - (a + b) * a) / (a * c) := by
        field_simp [(show 0 < a by linarith), show c ≠ 0 by nlinarith]
        <;> ring
      rw [h5]
      have h6 : (b + c) * c - (a + b) * a = (c - a) * (a + b + c) := by
        nlinarith
      rw [h6]
      have h7 : a + b + c = 1 := h
      rw [h7]
      apply div_pos_of_neg_of_neg
      · -- Show that (c - a) * 1 is negative
        nlinarith
      · -- Show that a * c is negative
        nlinarith
    linarith

  have hp2 : P > N := by
    rw [hP, hN]
    have h1 : b < 0 := hb
    have h2 : c < 0 := by linarith
    have h3 : b * c > 0 := by nlinarith
    have h4 : (a + b) / c - (a + c) / b > 0 := by
      have h5 : (a + b) / c - (a + c) / b = ((a + b) * b - (a + c) * c) / (c * b) := by
        field_simp [(show c ≠ 0 by nlinarith), show b ≠ 0 by nlinarith]
        <;> ring
      rw [h5]
      have h6 : (a + b) * b - (a + c) * c = (b - c) * (a + b + c) := by
        nlinarith
      rw [h6]
      have h7 : a + b + c = 1 := h
      rw [h7]
      apply div_pos
      · -- Show that (b - c) * 1 is positive
        have h8 : b - c > 0 := by linarith
        linarith
      · -- Show that c * b is positive
        nlinarith
    linarith

  constructor
  · linarith [hp1]
  · linarith [hp2]