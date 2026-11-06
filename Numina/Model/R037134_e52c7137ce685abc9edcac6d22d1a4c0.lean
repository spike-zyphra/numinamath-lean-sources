import Mathlib

open Real
open scoped BigOperators

theorem inequalities_321483 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  sqrt 3 ≤ (a + b + c) / sqrt (a * b + b * c + c * a) ∧
  (a + b + c) / sqrt (a * b + b * c + c * a) < 2 := by
  have ha1 : 0 < (a * b + b * c + c * a) := by 
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have ha2 : 0 < sqrt (a * b + b * c + c * a) := Real.sqrt_pos.mpr (by  nlinarith)
  have h1 : sqrt 3 ≤ (a + b + c) / sqrt (a * b + b * c + c * a) := by
    have h2 : sqrt (a * b + b * c + c * a) > 0 := Real.sqrt_pos.mpr ha1
    have h3 : (sqrt 3 * sqrt (a * b + b * c + c * a)) ^2 ≤ (a + b + c) ^2 := by
      have h4 : (sqrt 3 * sqrt (a * b + b * c + c * a)) ^2 = 3 * (a * b + b * c + c * a) := by
        calc
          (sqrt 3 * sqrt (a * b + b * c + c * a)) ^2 
            = (sqrt 3) ^2 * (sqrt (a * b + b * c + c * a)) ^2 := by ring
          _ = 3 * (a * b + b * c + c * a) := by
            have h5 : (sqrt 3) ^2 = 3 := Real.sq_sqrt (by norm_num)
            have h6 : (sqrt (a * b + b * c + c * a)) ^2 = a * b + b * c + c * a := Real.sq_sqrt (by positivity)
            rw [h5, h6]
      have h7 : (a + b + c) ^2 ≥ 3 * (a * b + b * c + c * a) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h, h', h'']
      nlinarith [h4, h7]
    have h9 : sqrt 3 * sqrt (a * b + b * c + c * a) ≤ a + b + c := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (a * b + b * c + c * a),
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sq_sqrt (show 0 ≤ (a * b + b * c + c * a : ℝ) by positivity),
        h3]
    have h10 : (a + b + c) / sqrt (a * b + b * c + c * a) ≥ sqrt 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [h9]
    linarith
  have ha3 : (a + b + c) / sqrt (a * b + b * c + c * a) < 2 := by
    have h11 : sqrt (a * b + b * c + c * a) > 0 := Real.sqrt_pos.mpr ha1
    have h12 : (a + b + c) ^2 < 4 * (a * b + b * c + c * a) := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        h, h', h'', mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'')
        ]
    have h13 : (a + b + c) < 2 * sqrt (a * b + b * c + c * a) := by
      have h14 : (a + b + c) ^2 < 4 * (a * b + b * c + c * a) := h12
      have h15 : (2 * sqrt (a * b + b * c + c * a)) ^2 = 4 * (a * b + b * c + c * a) := by
        calc
          (2 * sqrt (a * b + b * c + c * a)) ^2 
            = 4 * (sqrt (a * b + b * c + c * a)) ^2 := by ring
          _ = 4 * (a * b + b * c + c * a) := by
            have h5 : (sqrt (a * b + b * c + c * a)) ^2 = a * b + b * c + c * a := Real.sq_sqrt (by positivity)
            rw [h5]
      nlinarith [Real.sqrt_nonneg (a * b + b * c + c * a), Real.sq_sqrt (show (0 : ℝ) ≤ (a * b + b * c + c * a : ℝ) by positivity)]
    have h14 : (a + b + c) / sqrt (a * b + b * c + c * a) < 2 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg (a * b + b * c + c * a), h13]
    linarith
  exact ⟨h1, ha3⟩