import Mathlib

theorem inequalities_294960 (a b : ℝ) 
    (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    3 / 2 < 1 / (a ^ 3 + 1) + 1 / (b ^ 3 + 1) ∧
    1 / (a ^ 3 + 1) + 1 / (b ^ 3 + 1) ≤ 16 / 9 := by 
  have h1 : b = 1 - a := by linarith 
  rw [h1] 
  constructor
  · -- Prove the first part: $\frac{3}{2} < \frac{1}{a^3+1} + \frac{1}{(1-a)^3+1}$
    have h2 : 0 < 1 - a := by 
      nlinarith
    have h3 : 1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) > 3 / 2 := by
      have h4 : 0 < a * (1 - a) := by
        nlinarith
      have h5 : 1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) - 3 / 2 > 0 := by
        have h6 : 0 < (a ^ 3 + 1) * ((1 - a) ^ 3 + 1) := by
          positivity
        have h7 : (1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) - 3 / 2) = 
            ( ( (1 - a) ^ 3 + 1 + (a ^ 3 + 1) ) * 2 - 3 * ( (a ^ 3 + 1) * ( (1 - a) ^ 3 + 1) ) ) / ( 2 * ( (a ^ 3 + 1) * ( (1 - a) ^ 3 + 1) ) ) := by 
          field_simp
          ring
        rw [h7] at *
        apply div_pos
        nlinarith [ sq_pos_of_pos ha, sq_pos_of_pos h2, sq_nonneg (a - 1 / 2), sq_nonneg (a ^ 2 - a), sq_nonneg (a - 1), sq_nonneg (a * (a - 1)), sq_nonneg ((1 - a) * (a - 1)), sq_nonneg (a^2 - 1/4), sq_nonneg ((a - 1/2) * (a - 1/2) ) ]
        positivity
      linarith 
    linarith 
  · -- Prove the second part: $\frac{1}{a^3+1} + \frac{1}{(1-a)^3+1} \leqslant \frac{16}{9}$
    have h6 : 0 < 1 - a := by 
      nlinarith 
    have h7 : 1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) ≤ 16 / 9 := by 
      have h8 : 0 < (a ^ 3 + 1) * ((1 - a) ^ 3 + 1) := by
        positivity
      have h9 : 1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) - 16 / 9 ≤ 0 := by
        have h10 : 1 / (a ^ 3 + 1) + 1 / ((1 - a) ^ 3 + 1) - 16 / 9 = 
          (9 * ( ( (1 - a) ^ 3 + 1 + (a ^ 3 + 1) ) ) - 16 * ( (a ^ 3 + 1) * ( (1 - a) ^ 3 + 1) ) ) / ( 9 * ( (a ^ 3 + 1) * ( (1 - a) ^ 3 + 1) ) ) := by
          field_simp
          ring
        rw [h10] 
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [ sq_nonneg (a - 1 / 2), sq_nonneg (a^2 - a + 1 / 4), sq_nonneg (a^2 - a), sq_nonneg ((a - 1 / 2) * (a ^ 2 - a)), sq_nonneg ((a - 1 / 2) * (a - 1)), sq_nonneg ((a * (a - 1 / 2)) ), sq_nonneg ( ( (1 - a) - 1 / 2 ) ), mul_pos ha (show 0 < 1 - a by nlinarith), sq_nonneg (a * (1 - a) - 1 / 4) ]
        positivity 
      linarith 
    linarith