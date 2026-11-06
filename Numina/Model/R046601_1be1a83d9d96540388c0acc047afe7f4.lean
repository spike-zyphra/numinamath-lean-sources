import Mathlib

theorem inequalities_65241 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    Real.sqrt (2 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≥ 1 + a + b + c := by

  have h1 : 2 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥ (1 + a + b + c) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          habc]

  have h2 : Real.sqrt (2 * (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≥ Real.sqrt ((1 + a + b + c) ^ 2) := by 
    apply Real.sqrt_le_sqrt
    linarith [h1]

  have h3 : Real.sqrt ((1 + a + b + c) ^ 2) = (1 + a + b + c) := by
    rw [Real.sqrt_sq (show 0 ≤ 1 + a + b + c by
      nlinarith)]
  
  linarith [h2, h3]