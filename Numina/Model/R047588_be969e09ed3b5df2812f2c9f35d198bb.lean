import Mathlib

theorem inequalities_40226 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    3 / 8 ≤ a^2 / (b + c)^3 + b^2 / (a + c)^3 + c^2 / (a + b)^3 := by

  have h1 : b + c = 3 - a := by linarith
  have h2 : a + c = 3 - b := by linarith
  have h3 : a + b = 3 - c := by linarith

  have h4 : a^2 / (b + c)^3 - (7 / 16 * a - 5 / 16) ≥ 0 := by
    have h5 : 0 < b + c := by nlinarith
    have h6 : a^2 / (b + c)^3 - (7 / 16 * a - 5 / 16) ≥ 0 := by
      have h7 : (a^2 / (b + c)^3 - (7 / 16 * a - 5 / 16)) = (16 * a^2 - (7 * a - 5) * (b + c)^3) / (16 * (b + c)^3) := by
        field_simp
        ring
      rw [h7]
      have h8 : 0 < 16 * (b + c)^3 := by
        positivity
      have h9 : 16 * a^2 - (7 * a - 5) * (b + c)^3 ≥ 0 := by
        rw [show b + c = 3 - a by linarith]
        nlinarith [sq_nonneg (a - 1), sq_nonneg ((3 - a) - 2), sq_nonneg (a * (a - 1)), sq_nonneg ((3 - a) * (a - 1)), sq_nonneg ((3 - a) * ((3 - a) - 2)), sq_nonneg ((a) * ((3 - a) - 2)), mul_pos ha (show 0 < 3 - a by nlinarith), mul_pos (show 0 < 3 - a by nlinarith) (show 0 < 3 - a by nlinarith)]
      apply div_nonneg
      linarith
      linarith
    linarith

  have h5 : b^2 / (a + c)^3 - (7 / 16 * b - 5 / 16) ≥ 0 := by
    have h6 : 0 < a + c := by nlinarith
    have h7 : b^2 / (a + c)^3 - (7 / 16 * b - 5 / 16) ≥ 0 := by
      have h8 : (b^2 / (a + c)^3 - (7 / 16 * b - 5 / 16)) = (16 * b^2 - (7 * b - 5) * (a + c)^3) / (16 * (a + c)^3) := by
        field_simp
        ring
      rw [h8]
      have h9 : 0 < 16 * (a + c)^3 := by
        positivity
      have h10 : 16 * b^2 - (7 * b - 5) * (a + c)^3 ≥ 0 := by
        rw [show a + c = 3 - b by linarith]
        nlinarith [sq_nonneg (b - 1), sq_nonneg ((3 - b) - 2), sq_nonneg (b * (b - 1)), sq_nonneg ((3 - b) * (b - 1)), sq_nonneg ((3 - b) * ((3 - b) - 2)), sq_nonneg ((b) * ((3 - b) - 2)), mul_pos hb (show 0 < 3 - b by nlinarith), mul_pos (show 0 < 3 - b by nlinarith) (show 0 < 3 - b by nlinarith)]
      apply div_nonneg
      linarith
      linarith
    linarith

  have h6 : c^2 / (a + b)^3 - (7 / 16 * c - 5 / 16) ≥ 0 := by
    have h7 : 0 < a + b := by nlinarith
    have h8 : c^2 / (a + b)^3 - (7 / 16 * c - 5 / 16) ≥ 0 := by
      have h9 : (c^2 / (a + b)^3 - (7 / 16 * c - 5 / 16)) = (16 * c^2 - (7 * c - 5) * (a + b)^3) / (16 * (a + b)^3) := by
        field_simp
        ring
      rw [h9]
      have h10 : 0 < 16 * (a + b)^3 := by
        positivity
      have h11 : 16 * c^2 - (7 * c - 5) * (a + b)^3 ≥ 0 := by
        rw [show a + b = 3 - c by linarith]
        nlinarith [sq_nonneg (c - 1), sq_nonneg ((3 - c) - 2), sq_nonneg (c * (c - 1)), sq_nonneg ((3 - c) * (c - 1)), sq_nonneg ((3 - c) * ((3 - c) - 2)), sq_nonneg ((c) * ((3 - c) - 2)), mul_pos hc (show 0 < 3 - c by nlinarith), mul_pos (show 0 < 3 - c by nlinarith) (show 0 < 3 - c by nlinarith)]
      apply div_nonneg
      linarith
      linarith
    linarith

  nlinarith