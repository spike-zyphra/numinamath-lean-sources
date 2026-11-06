import Mathlib

open Real

theorem inequalities_34428 (a b m : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (h : a > b) :
    sqrt (b + m) - sqrt b > sqrt (a + m) - sqrt a := by

  have h3 : sqrt (b + m) - sqrt b - (sqrt (a + m) - sqrt a) > 0 := by
    have h4 : sqrt (b + m) + sqrt a > sqrt b + sqrt (a + m) := by
      have h5 : (sqrt (b + m) + sqrt a)^2 > (sqrt b + sqrt (a + m))^2 := by
        have h6 : sqrt (b + m) ^ 2 = b + m := by
          rw [Real.sq_sqrt]
          nlinarith
        have h7 : sqrt a ^ 2 = a := by
          rw [Real.sq_sqrt]
          nlinarith
        have h8 : sqrt b ^ 2 = b := by
          rw [Real.sq_sqrt]
          nlinarith
        have h9 : sqrt (a + m) ^ 2 = a + m := by
          rw [Real.sq_sqrt]
          nlinarith
        have h10 : (sqrt (b + m) + sqrt a)^2 =
          (sqrt (b + m)) ^ 2 + (sqrt a) ^ 2 + 2 * (sqrt (b + m) * sqrt a) := by ring
        have h11 : (sqrt b + sqrt (a + m))^2 =
          (sqrt b) ^ 2 + (sqrt (a + m)) ^ 2 + 2 * (sqrt b * sqrt (a + m)) := by ring
        rw [h10, h11]
        rw [h6, h7, h8, h9]
        have h12 : sqrt (b + m) * sqrt a > sqrt b * sqrt (a + m) := by
          have h13 : sqrt (b + m) * sqrt a = Real.sqrt ( (b + m) * a ) := by
            rw [← Real.sqrt_mul (by nlinarith)]
          have h14 : sqrt b * sqrt (a + m) = Real.sqrt ( b * (a + m) ) := by
            rw [← Real.sqrt_mul (by nlinarith)]
          rw [h13, h14]
          have h14 : (b + m) * a > b * (a + m) := by
            nlinarith [show 0 < a - b from sub_pos_of_lt h, hm]
          have h15 : (b * (a + m)) ≥ 0 := by nlinarith
          have h16 : ((b + m) * a) ≥ 0 := by nlinarith
          apply Real.sqrt_lt_sqrt
          all_goals nlinarith
        nlinarith [sub_pos_of_lt h, sq_nonneg (sqrt (b + m) - sqrt b), sq_nonneg (sqrt (a + m) - sqrt a),
                  Real.sqrt_nonneg (b + m), Real.sqrt_nonneg b, Real.sqrt_nonneg (a + m), Real.sqrt_nonneg a]
      nlinarith [Real.sqrt_nonneg (b + m), Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg (a + m)]
    linarith
  linarith