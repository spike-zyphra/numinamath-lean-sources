import Mathlib

open Real Set

theorem inequalities_302652 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
    c / (a + b) + b / c ≥ sqrt 2 - 1 / 2 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < c * (a + b) := by
    apply mul_pos
    linarith
    linarith
  have h3 : c / (a + b) + b / c - (sqrt 2 - 1 / 2) ≥ 0 := by
    have h6 : c * c + b * (a + b) ≥ (sqrt 2 - 1 / 2) * c * (a + b) := by
      have h7 : 0 < a := by linarith
      have h8 : 0 < b := by linarith
      have h9 : 0 < c := by linarith
      have h10 : 0 < a + b := by linarith
      have h11 : 0 < c * (a + b) := by nlinarith
      have h12 : Real.sqrt 2 > 0 := by positivity
      nlinarith [sq_nonneg (c - (a + b) / Real.sqrt 2), sq_nonneg (b - (c) / 2), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (c - Real.sqrt 2 * (a + b) / 2), sq_nonneg ((a + b) ^ 2 - 2 * c ^ 2), 
          sq_nonneg (c ^ 2 - (a + b) * b), sq_nonneg ((a + b - c) ^ 2), sq_nonneg ((a - b) * c), 
          sq_nonneg (c - (a + b)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
          mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
        ]
    have h5 : c / (a + b) + b / c - (sqrt 2 - 1 / 2) = (c * c + b * (a + b) - (sqrt 2 - 1 / 2) * c * (a + b) ) / (c * (a + b)) := by
      field_simp
      <;> ring
    have h7 : c * c + b * (a + b) - (sqrt 2 - 1 / 2) * c * (a + b) ≥ 0 := by
      linarith [h6]
    have h8 : (c * c + b * (a + b) - (sqrt 2 - 1 / 2) * c * (a + b) ) / (c * (a + b)) ≥ 0 := by
      apply div_nonneg 
      linarith [h7]
      all_goals positivity 
    linarith [h5, h8]
  linarith