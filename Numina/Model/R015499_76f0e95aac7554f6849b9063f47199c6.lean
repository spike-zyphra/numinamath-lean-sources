import Mathlib


theorem inequalities_106522 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) +
        Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) +
        Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) := by
  have h1 : 0 < a + b + c := by linarith
  have h3 : Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) ≥ (a + 2 * b + 3 * c) / (2 * (a + b + c)) := by
    have h4 : ((a + 2 * b + 3 * c) / (2 * (a + b + c))) ^ 2 ≤ (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) := by
      have h5 : 0 < 3 * a + 2 * b + c := by nlinarith
      have h6 : 0 < 2 * (a + b + c) := by nlinarith
      have h7 : 0 < (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) := by
        apply div_pos
        all_goals nlinarith
      have h8 : ((a + 2 * b + 3 * c) / (2 * (a + b + c))) ^ 2 = ((a + 2 * b + 3 * c) ^ 2) / (4 * (a + b + c) ^ 2) := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) - ((a + 2 * b + 3 * c) ^ 2) / (4 * (a + b + c) ^ 2) ≥ 0 := by
        have h10 : (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) - ((a + 2 * b + 3 * c) ^ 2) / (4 * (a + b + c) ^ 2) =
            (4 * (a + b + c) ^ 2 * (a + 2 * b + 3 * c) - (a + 2 * b + 3 * c) ^ 2 * (3 * a + 2 * b + c)) / (4 * (a + b + c) ^ 2 * (3 * a + 2 * b + c)) := by
          field_simp
          ring
        rw [h10]
        have h11 : 0 < (4 * (a + b + c) ^ 2 * (3 * a + 2 * b + c)) := by positivity
        have h12 : 4 * (a + b + c) ^ 2 * (a + 2 * b + 3 * c) - (a + 2 * b + 3 * c) ^ 2 * (3 * a + 2 * b + c) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h13 : (4 * (a + b + c) ^ 2 * (a + 2 * b + 3 * c) - (a + 2 * b + 3 * c) ^ 2 * (3 * a + 2 * b + c)) / (4 * (a + b + c) ^ 2 * (3 * a + 2 * b + c)) ≥ 0 := by
          apply div_nonneg
          all_goals linarith
        linarith
      nlinarith
    have h10 : Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) ≥ (a + 2 * b + 3 * c) / (2 * (a + b + c)) := by
      have h11 : ((a + 2 * b + 3 * c) / (2 * (a + b + c))) ^ 2 ≤ (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) := by
        linarith [h4]
      have h12 : (a + 2 * b + 3 * c) / (2 * (a + b + c)) ≤ Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) := by
        have h13 : ((a + 2 * b + 3 * c) / (2 * (a + b + c))) ^ 2 ≤ (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) := by
          linarith [h4]
        have h14 : (a + 2 * b + 3 * c) / (2 * (a + b + c)) ≤ Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) := by
          nlinarith [Real.sqrt_nonneg ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)), Real.sq_sqrt (show (0 : ℝ) ≤ (a + 2 * b + 3 * c) / (3 * a + 2 * b + c) by positivity)]
        linarith
      linarith
    linarith
  have h3' : Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) ≥ (b + 2 * c + 3 * a) / (2 * (a + b + c)) := by
    have h4 : ((b + 2 * c + 3 * a) / (2 * (a + b + c))) ^ 2 ≤ (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) := by
      have h5 : 0 < 3 * b + 2 * c + a := by nlinarith
      have h6 : 0 < 2 * (a + b + c) := by nlinarith
      have h7 : 0 < (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) := by
        apply div_pos
        all_goals nlinarith
      have h8 : ((b + 2 * c + 3 * a) / (2 * (a + b + c))) ^ 2 = ((b + 2 * c + 3 * a) ^ 2) / (4 * (a + b + c) ^ 2) := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) - ((b + 2 * c + 3 * a) ^ 2) / (4 * (a + b + c) ^ 2) ≥ 0 := by
        have h10 : (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) - ((b + 2 * c + 3 * a) ^ 2) / (4 * (a + b + c) ^ 2) =
            (4 * (a + b + c) ^ 2 * (b + 2 * c + 3 * a) - (b + 2 * c + 3 * a) ^ 2 * (3 * b + 2 * c + a)) / (4 * (a + b + c) ^ 2 * (3 * b + 2 * c + a)) := by
          field_simp
          ring
        rw [h10]
        have h11 : 0 < (4 * (a + b + c) ^ 2 * (3 * b + 2 * c + a)) := by positivity
        have h12 : 4 * (a + b + c) ^ 2 * (b + 2 * c + 3 * a) - (b + 2 * c + 3 * a) ^ 2 * (3 * b + 2 * c + a) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h13 : (4 * (a + b + c) ^ 2 * (b + 2 * c + 3 * a) - (b + 2 * c + 3 * a) ^ 2 * (3 * b + 2 * c + a)) / (4 * (a + b + c) ^ 2 * (3 * b + 2 * c + a)) ≥ 0 := by
          apply div_nonneg
          all_goals linarith
        linarith
      nlinarith
    have h10 : Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) ≥ (b + 2 * c + 3 * a) / (2 * (a + b + c)) := by
      have h11 : ((b + 2 * c + 3 * a) / (2 * (a + b + c))) ^ 2 ≤ (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) := by
        linarith [h4]
      have h12 : (b + 2 * c + 3 * a) / (2 * (a + b + c)) ≤ Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) := by
        have h13 : ((b + 2 * c + 3 * a) / (2 * (a + b + c))) ^ 2 ≤ (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) := by
          linarith [h4]
        have h14 : (b + 2 * c + 3 * a) / (2 * (a + b + c)) ≤ Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) := by
          nlinarith [Real.sqrt_nonneg ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)), Real.sq_sqrt (show (0 : ℝ) ≤ (b + 2 * c + 3 * a) / (3 * b + 2 * c + a) by positivity)]
        linarith
      linarith
    linarith
  have h3'' : Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) ≥ (c + 2 * a + 3 * b) / (2 * (a + b + c)) := by
    have h4 : ((c + 2 * a + 3 * b) / (2 * (a + b + c))) ^ 2 ≤ (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) := by
      have h5 : 0 < 3 * c + 2 * a + b := by nlinarith
      have h6 : 0 < 2 * (a + b + c) := by nlinarith
      have h7 : 0 < (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) := by
        apply div_pos
        all_goals nlinarith
      have h8 : ((c + 2 * a + 3 * b) / (2 * (a + b + c))) ^ 2 = ((c + 2 * a + 3 * b) ^ 2) / (4 * (a + b + c) ^ 2) := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) - ((c + 2 * a + 3 * b) ^ 2) / (4 * (a + b + c) ^ 2) ≥ 0 := by
        have h10 : (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) - ((c + 2 * a + 3 * b) ^ 2) / (4 * (a + b + c) ^ 2) =
            (4 * (a + b + c) ^ 2 * (c + 2 * a + 3 * b) - (c + 2 * a + 3 * b) ^ 2 * (3 * c + 2 * a + b)) / (4 * (a + b + c) ^ 2 * (3 * c + 2 * a + b)) := by
          field_simp
          ring
        rw [h10]
        have h11 : 0 < (4 * (a + b + c) ^ 2 * (3 * c + 2 * a + b)) := by positivity
        have h12 : 4 * (a + b + c) ^ 2 * (c + 2 * a + 3 * b) - (c + 2 * a + 3 * b) ^ 2 * (3 * c + 2 * a + b) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h13 : (4 * (a + b + c) ^ 2 * (c + 2 * a + 3 * b) - (c + 2 * a + 3 * b) ^ 2 * (3 * c + 2 * a + b)) / (4 * (a + b + c) ^ 2 * (3 * c + 2 * a + b)) ≥ 0 := by
          apply div_nonneg
          all_goals linarith
        linarith
      nlinarith
    have h10 : Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) ≥ (c + 2 * a + 3 * b) / (2 * (a + b + c)) := by
      have h11 : ((c + 2 * a + 3 * b) / (2 * (a + b + c))) ^ 2 ≤ (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) := by
        linarith [h4]
      have h12 : (c + 2 * a + 3 * b) / (2 * (a + b + c)) ≤ Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) := by
        have h13 : ((c + 2 * a + 3 * b) / (2 * (a + b + c))) ^ 2 ≤ (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) := by
          linarith [h4]
        have h14 : (c + 2 * a + 3 * b) / (2 * (a + b + c)) ≤ Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) := by
          nlinarith [Real.sqrt_nonneg ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)), Real.sq_sqrt (show (0 : ℝ) ≤ (c + 2 * a + 3 * b) / (3 * c + 2 * a + b) by positivity)]
        linarith
      linarith
    linarith
  have h33 : Real.sqrt ((a + 2 * b + 3 * c) / (3 * a + 2 * b + c)) + Real.sqrt ((b + 2 * c + 3 * a) / (3 * b + 2 * c + a)) + Real.sqrt ((c + 2 * a + 3 * b) / (3 * c + 2 * a + b)) ≥ (a + 2 * b + 3 * c) / (2 * (a + b + c)) + (b + 2 * c + 3 * a) / (2 * (a + b + c)) + (c + 2 * a + 3 * b) / (2 * (a + b + c)) := by
    linarith [h3, h3', h3'']
  have h34 : (a + 2 * b + 3 * c) / (2 * (a + b + c)) + (b + 2 * c + 3 * a) / (2 * (a + b + c)) + (c + 2 * a + 3 * b) / (2 * (a + b + c)) = 3 := by
    field_simp
    nlinarith
  linarith [h33, h34]