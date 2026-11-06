import Mathlib

theorem algebra_287664 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    1 / (1 + Real.logb (a^2 * b) (c / a)) + 1 / (1 + Real.logb (b^2 * c) (a / b)) +
    1 / (1 + Real.logb (c^2 * a) (b / c)) = 3 := by

  have h1 : 1 + Real.logb (a^2 * b) (c / a) = (Real.log a + Real.log b + Real.log c) / (2 * Real.log a + Real.log b) := by
    have h2 : Real.logb (a^2 * b) (c / a) = (Real.log (c / a)) / (Real.log (a^2 * b)) := by
      field_simp [Real.logb]
    have h3 : Real.log (c / a) = Real.log c - Real.log a := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h4 : Real.log (a^2 * b) = 2 * Real.log a + Real.log b := by
      calc
        Real.log (a^2 * b) = Real.log (a^2) + Real.log b := by rw [Real.log_mul (by positivity) (by positivity)]
        _ = 2 * Real.log a + Real.log b := by
          have h7 : Real.log (a^2) = 2 * Real.log a := by
            simp [Real.log_pow]
          rw [h7]
    rw [h2, h3, h4]
    have h5 : 2 * Real.log a + Real.log b > 0 := by
      have ha2 : Real.log a > 0 := by
        apply Real.log_pos
        linarith
      have hb2 : Real.log b > 0 := by
        apply Real.log_pos
        linarith
      linarith
    have h7 : Real.log a + Real.log b + Real.log c > 0 := by
      have ha2 : Real.log a > 0 := by
        apply Real.log_pos
        linarith
      have hb2 : Real.log b > 0 := by
        apply Real.log_pos
        linarith
      have hc2 : Real.log c > 0 := by
        apply Real.log_pos
        linarith
      linarith
    field_simp [show 2 * Real.log a + Real.log b ≠ 0 by linarith]
    all_goals
      linarith

  have h2 : 1 + Real.logb (b^2 * c) (a / b) = (Real.log a + Real.log b + Real.log c) / (2 * Real.log b + Real.log c) := by
    have h3 : Real.logb (b^2 * c) (a / b) = (Real.log (a / b)) / (Real.log (b^2 * c)) := by
      field_simp [Real.logb]
    have h4 : Real.log (a / b) = Real.log a - Real.log b := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h5 : Real.log (b^2 * c) = 2 * Real.log b + Real.log c := by
      calc
        Real.log (b^2 * c) = Real.log (b^2) + Real.log c := by rw [Real.log_mul (by positivity) (by positivity)]
        _ = 2 * Real.log b + Real.log c := by
          have h7 : Real.log (b^2) = 2 * Real.log b := by
            simp [Real.log_pow]
          rw [h7]
    rw [h3, h4, h5]
    have h11 : 2 * Real.log b + Real.log c > 0 := by
      have hb2 : Real.log b > 0 := by
        apply Real.log_pos
        linarith
      have hc2 : Real.log c > 0 := by
        apply Real.log_pos
        linarith
      linarith
    have h7 : Real.log a + Real.log b + Real.log c > 0 := by
      have ha2 : Real.log a > 0 := by
        apply Real.log_pos
        linarith
      have hb2 : Real.log b > 0 := by
        apply Real.log_pos
        linarith
      have hc2 : Real.log c > 0 := by
        apply Real.log_pos
        linarith
      linarith
    field_simp [show 2 * Real.log b + Real.log c ≠ 0 by linarith]
    all_goals
      linarith

  have h3 : 1 + Real.logb (c^2 * a) (b / c) = (Real.log a + Real.log b + Real.log c) / (2 * Real.log c + Real.log a) := by
    have h4 : Real.logb (c^2 * a) (b / c) = (Real.log (b / c)) / (Real.log (c^2 * a)) := by
      field_simp [Real.logb]
    have h5 : Real.log (b / c) = Real.log b - Real.log c := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h6 : Real.log (c^2 * a) = 2 * Real.log c + Real.log a := by
      calc
        Real.log (c^2 * a) = Real.log (c^2) + Real.log a := by rw [Real.log_mul (by positivity) (by positivity)]
        _ = 2 * Real.log c + Real.log a := by
          have h7 : Real.log (c^2) = 2 * Real.log c := by
            simp [Real.log_pow]
          rw [h7]
    rw [h4, h5, h6]
    have h11 : 2 * Real.log c + Real.log a > 0 := by
      have hc2 : Real.log c > 0 := by
        apply Real.log_pos
        linarith
      have ha2 : Real.log a > 0 := by
        apply Real.log_pos
        linarith
      linarith
    have h7 : Real.log a + Real.log b + Real.log c > 0 := by
      have ha2 : Real.log a > 0 := by
        apply Real.log_pos
        linarith
      have hb2 : Real.log b > 0 := by
        apply Real.log_pos
        linarith
      have hc2 : Real.log c > 0 := by
        apply Real.log_pos
        linarith
      linarith
    field_simp [show 2 * Real.log c + Real.log a ≠ 0 by linarith]
    all_goals
      linarith

  rw [h1, h2, h3]

  have h7 : Real.log a + Real.log b + Real.log c > 0 := by
    have ha2 : Real.log a > 0 := by
      apply Real.log_pos
      linarith
    have hb2 : Real.log b > 0 := by
      apply Real.log_pos
      linarith
    have hc2 : Real.log c > 0 := by
      apply Real.log_pos
      linarith
    linarith

  have h8 : (2 * Real.log a + Real.log b) / (Real.log a + Real.log b + Real.log c) + (2 * Real.log b + Real.log c) / (Real.log a + Real.log b + Real.log c) + (2 * Real.log c + Real.log a) / (Real.log a + Real.log b + Real.log c) = 3 := by
    have h7' : Real.log a + Real.log b + Real.log c > 0 := h7
    field_simp [h7']
    linarith

  have h4 : 1 / ( (Real.log a + Real.log b + Real.log c) / (2 * Real.log a + Real.log b) ) = (2 * Real.log a + Real.log b) / (Real.log a + Real.log b + Real.log c) := by
    field_simp

  have h5 : 1 / ( (Real.log a + Real.log b + Real.log c) / (2 * Real.log b + Real.log c) ) = (2 * Real.log b + Real.log c) / (Real.log a + Real.log b + Real.log c) := by
    field_simp

  have h6 : 1 / ( (Real.log a + Real.log b + Real.log c) / (2 * Real.log c + Real.log a) ) = (2 * Real.log c + Real.log a) / (Real.log a + Real.log b + Real.log c) := by
    field_simp

  rw [h4, h5, h6]
  linarith [h8]