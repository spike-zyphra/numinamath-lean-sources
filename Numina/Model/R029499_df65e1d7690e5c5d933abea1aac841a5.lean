import Mathlib

open Real

theorem inequalities_207582 (a b x : ℝ) (ha : 0 < b) (hb : b < a) (hx : a < x)
    (h : x < a + b) :
    (sqrt (a + b) - sqrt a) / b < (sqrt x - sqrt a) / (x - a) ∧
    (sqrt x - sqrt a) / (x - a) < (sqrt a - sqrt (a - b)) / b := by
  have h1 : 0 < a := by linarith
  have h2 : 0 < x - a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : 0 < a - b := by nlinarith
  have h5 : sqrt (a + b) > sqrt a := by
    apply Real.sqrt_lt_sqrt
    all_goals linarith
  have h6 : sqrt x > sqrt a := by
    apply Real.sqrt_lt_sqrt
    all_goals linarith
  have h7 : sqrt (a + b) > sqrt x := by
    apply Real.sqrt_lt_sqrt
    all_goals linarith
  have h8 : sqrt a > sqrt (a - b) := by
    apply Real.sqrt_lt_sqrt
    all_goals nlinarith
  have h12 : (sqrt (a + b) - sqrt a) / b < (sqrt x - sqrt a) / (x - a) := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg x, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          sq_nonneg (sqrt (a + b) - sqrt x), sq_nonneg (sqrt x - sqrt a), sq_nonneg (sqrt (a + b) - sqrt a),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith),
          mul_pos (show 0 < sqrt (a + b) - sqrt a by nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a]) (show 0 < x - a by linarith), 
          mul_pos (show 0 < sqrt x - sqrt a by nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg a]) (show 0 < b by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < x - a by linarith)
          ]
  have h14 : (sqrt x - sqrt a) / (x - a) < (sqrt a - sqrt (a - b)) / b := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg a, Real.sqrt_nonneg (a - b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) by nlinarith), 
          sq_nonneg (sqrt x - sqrt a), sq_nonneg (sqrt a - sqrt (a - b)), sq_nonneg (x - a),
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) by nlinarith),
          mul_pos (show 0 < sqrt x - sqrt a by nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg a]) (show 0 < b by linarith), 
          mul_pos (show 0 < sqrt a - sqrt (a - b) by nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg (a - b)]) (show 0 < x - a by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < x - a by linarith)
          ]
  constructor
  · exact h12
  · exact h14