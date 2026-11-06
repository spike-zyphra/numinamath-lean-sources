import Mathlib

theorem inequalities_37571 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) / 2 - a * b / (a + b) - b * c / (b + c) - c * a / (c + a) ≥ 0 ∧
    a * (1 + b) + b * (1 + c) + c * (1 + a) ≥ 6 * Real.sqrt (a * b * c) := by
  constructor
  · -- Prove the first inequality.
    have h1 : 0 < a + b := by nlinarith
    have h2 : 0 < b + c := by nlinarith
    have h3 : 0 < c + a := by nlinarith
    have h6 : a * b / (a + b) ≤ (a + b) / 4 := by
      have h7 : 0 < a + b := by nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (a - b)]
    have h8 : b * c / (b + c) ≤ (b + c) / 4 := by
      have h9 : 0 < b + c := by nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (b - c)]
    have h10 : c * a / (c + a) ≤ (c + a) / 4 := by
      have h11 : 0 < c + a := by nlinarith
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (c - a)]
    have h12 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≤ (a + b + c) / 2 := by
      linarith [h6, h8, h10]
    linarith [h12]
  · -- Prove the second inequality.
    have h14 : a * (1 + b) + b * (1 + c) + c * (1 + a) = a + b + c + a * b + b * c + c * a := by
      ring
    rw [h14]
    have h15 : a * b * c > 0 := by
      positivity
    have h16 : Real.sqrt (a * b * c) ≥ 0 := by
      positivity
    -- Now prove the main inequality
    have h9 : a + b + c + a * b + b * c + c * a ≥ 6 * Real.sqrt (a * b * c) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (Real.sqrt (a * b * c) ), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          Real.sqrt_nonneg (a * b * c),
          Real.sq_sqrt (show 0 ≤ a * b * c by positivity),
          sq_nonneg (a * b ), sq_nonneg (b * c ), sq_nonneg (c * a ),
          mul_nonneg (Real.sqrt_nonneg (a * b * c)) (Real.sqrt_nonneg (a * b * c)),
          sq_nonneg (a + b + c - 3 * Real.sqrt (a * b * c)),
          sq_nonneg (a * b + b * c + c * a - 3 * Real.sqrt (a * b * c)),
          sq_nonneg ( (a * b * c : ℝ) - (Real.sqrt (a * b * c)) ^2 )
         ]
    linarith [h9]