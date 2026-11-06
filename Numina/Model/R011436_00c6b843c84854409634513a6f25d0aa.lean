import Mathlib

theorem inequalities_59594 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c) ∧
    1 / a + 1 / b + 1 / c ≥ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) := by
  constructor
  · -- Show 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c)
    have h1 : a + b > 0 := add_pos ha hb
    have h2 : b + c > 0 := add_pos hb hc
    have h3 : c + a > 0 := add_pos hc ha
    have h4 : a + b + c > 0 := add_pos (add_pos ha hb) hc
    have h5 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) ≥ 0 := by
      have h_pos1 : a + b > 0 := h1
      have h_pos2 : b + c > 0 := h2
      have h_pos3 : c + a > 0 := h3
      have h_pos4 : a + b + c > 0 := h4
      have h6 : (a + b) * (b + c) * (c + a) > 0 := by 
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h7 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c) ≥ 0 := by
        have h_mul : (2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c)) ≥ 0 := by
          have h_pos5 : (a + b) * (b + c) * (c + a) * (a + b + c) > 0 := by
            apply mul_pos
            exact h6
            linarith
          have h_numerator : (2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c)) * ((a + b) * (b + c) * (c + a) * (a + b + c)) ≥ 0 := by
            have h1 : (2 / (a + b) + 2 / (b + c) + 2 / (c + a) - 9 / (a + b + c)) * ((a + b) * (b + c) * (c + a) * (a + b + c)) = 2 * (b + c) * (c + a) * (a + b + c) + 2 * (c + a) * (a + b) * (a + b + c) + 2 * (a + b) * (b + c) * (a + b + c) - 9 * (a + b) * (b + c) * (c + a) := by
              field_simp
              ring
            rw [h1]
            nlinarith [sq_nonneg (a + b - b - c), sq_nonneg (b + c - c - a), sq_nonneg (c + a - a - b),
                       sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                       mul_pos h_pos1 h_pos2, mul_pos h_pos2 h_pos3, mul_pos h_pos3 h_pos1,
                       h_pos4]
          nlinarith [h_numerator, mul_pos h6 h_pos4]
        linarith
      linarith
    linarith
  · -- Show 1 / a + 1 / b + 1 / c ≥ 2 / (a + b) + 2 / (b + c) + 2 / (c + a)
    have h1 : a > 0 := ha
    have h2 : b > 0 := hb
    have h3 : c > 0 := hc
    have h4 : (1 / a + 1 / b + 1 / c - 2 / (a + b) - 2 / (b + c) - 2 / (c + a)) ≥ 0 := by
      have h5 : a * b * c > 0 := by positivity
      have h6 : 0 < a * b * c := by positivity
      have h7 : (1 / a + 1 / b + 1 / c - 2 / (a + b) - 2 / (b + c) - 2 / (c + a) ) =
          ((1 / a + 1 / b - 4 / (a + b)) + (1 / b + 1 / c - 4 / (b + c)) + (1 / c + 1 / a - 4 / (c + a)) ) / 2 := by
        field_simp
        ring
      rw [h7]
      have h8 : (1 / a + 1 / b - 4 / (a + b)) ≥ 0 := by
        have h10 : 0 < a * b * (a + b) := by positivity
        have h11 : (1 / a + 1 / b - 4 / (a + b)) = ( (a - b) ^ 2 ) / ( a * b * (a + b) ) := by
          field_simp [h1, h2, show 0 < a + b from by linarith]
          <;> nlinarith
        rw [h11]
        apply div_nonneg
        · positivity 
        · positivity
      have h9 : (1 / b + 1 / c - 4 / (b + c)) ≥ 0 := by
        have h10 : 0 < b * c * (b + c) := by positivity
        have h11 : (1 / b + 1 / c - 4 / (b + c)) = ( (b - c) ^ 2 ) / ( b * c * (b + c) ) := by
          field_simp [h2, h3, show 0 < b + c from by linarith]
          <;> nlinarith
        rw [h11]
        apply div_nonneg
        · positivity 
        · positivity
      have h10 : (1 / c + 1 / a - 4 / (c + a)) ≥ 0 := by
        have h11 : 0 < c * a * (c + a) := by positivity
        have h12 : (1 / c + 1 / a - 4 / (c + a)) = ( (c - a) ^ 2 ) / ( c * a * (c + a) ) := by
          field_simp [h3, h1, show 0 < c + a from by linarith]
          <;> nlinarith
        rw [h12]
        apply div_nonneg
        · positivity 
        · positivity
      linarith [h8, h9, h10]
    linarith [h4]