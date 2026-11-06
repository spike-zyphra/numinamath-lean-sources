import Mathlib

open Real

theorem inequalities_288924 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) / 3 ≥ ((a + b) * (b + c) * (c + a) / 8) ^ ((1 : ℝ) / 3) ∧
    ((a + b) * (b + c) * (c + a) / 8) ^ ((1 : ℝ) / 3) ≥
    (sqrt (a * b) + sqrt (b * c) + sqrt (c * a)) / 3 := by
  constructor
  · -- Prove the first part: (a + b + c) / 3 ≥ ((a + b) * (b + c) * (c + a) / 8) ^ (1/3)
    have h1 : ((a + b) * (b + c) * (c + a) / 8) ≤ ((a + b + c) / 3) ^ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b from by nlinarith) (show 0 < a * c from by nlinarith), 
              mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
                mul_pos (show 0 < a * c from by nlinarith) (show 0 < b * c from by nlinarith)
        ]
    have h2 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ^ ((1 : ℝ) / 3) ≤ (a + b + c) / 3 := by
      have h4 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ≤ ( ( (a + b + c) / 3 ) ^ 3 ) := h1
      have h5 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ^ ((1 : ℝ) / 3) ≤ ( ( ( (a + b + c) / 3 ) ^ 3 ) ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow
        all_goals nlinarith [show 0 ≤ (a + b) * (b + c) * (c + a) / 8 by positivity, show 0 ≤ ( (a + b + c) / 3 ) ^ 3 by positivity, h4]
      have h6 : ( ( (a + b + c) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) = (a + b + c) / 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals nlinarith
      linarith [h5, h6]
    linarith [h2]
  · -- Prove the second part: ((a + b) * (b + c) * (c + a) / 8) ^ (1/3) ≥ (sqrt (a * b) + sqrt (b * c) + sqrt (c * a)) / 3
    have h5 : ((a + b) * (b + c) * (c + a) / 8) ≥ ((sqrt (a * b) + sqrt (b * c) + sqrt (c * a)) / 3) ^ 3 := by
      have h41 : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by positivity)]
      have h42 : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
        rw [Real.sqrt_mul (by positivity)]
      have h43 : sqrt (c * a) = Real.sqrt c * Real.sqrt a := by
        rw [Real.sqrt_mul (by positivity)]
      rw [h41, h42, h43]
      have h81 : 0 < Real.sqrt a := by positivity
      have h82 : 0 < Real.sqrt b := by positivity
      have h83 : 0 < Real.sqrt c := by positivity
      have h65 : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
        calc 
          (Real.sqrt a * Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2 := by ring 
          _ = a * b := by
            have h92 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
            have h93 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
            rw [h92, h93]
      have h66 : (Real.sqrt b * Real.sqrt c) ^ 2 = b * c := by
        calc 
          (Real.sqrt b * Real.sqrt c) ^ 2 = (Real.sqrt b) ^ 2 * (Real.sqrt c) ^ 2 := by ring 
          _ = b * c := by
            have h94 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
            have h95 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
            rw [h94, h95]
      have h67 : (Real.sqrt c * Real.sqrt a) ^ 2 = c * a := by
        calc 
          (Real.sqrt c * Real.sqrt a) ^ 2 = (Real.sqrt c) ^ 2 * (Real.sqrt a) ^ 2 := by ring 
          _ = c * a := by
            have h96 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
            have h97 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
            rw [h96, h97]
      have h68 : ( (Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt c + Real.sqrt c * Real.sqrt a) / 3 ) ^ 3 ≤ ( (a + b) * (b + c) * (c + a) / 8 ) := by
        nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt c - Real.sqrt a), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, 
              Real.sq_sqrt (show 0 ≤ a by positivity), 
                Real.sq_sqrt (show 0 ≤ b by positivity), 
                  Real.sq_sqrt (show 0 ≤ c by positivity), 
                    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                      h65, h66, h67, 
                        mul_pos (show 0 < Real.sqrt a by positivity) (show 0 < Real.sqrt b by positivity), 
                          mul_pos (show 0 < Real.sqrt b by positivity) (show 0 < Real.sqrt c by positivity), 
                            mul_pos (show 0 < Real.sqrt c by positivity) (show 0 < Real.sqrt a by positivity)
                  ]
      linarith [h68]
    have h4 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ^ ((1 : ℝ) / 3) ≥ ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) := by
      have h6 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ≥ ( ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) ) ^ 3 := h5
      have h7 : (( (a + b) * (b + c) * (c + a) / 8 ) ) ^ ((1 : ℝ) / 3) ≥ ( ( ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) ) ^ 3 ) ^ ((1 : ℝ) / 3) := by 
        apply Real.rpow_le_rpow 
        all_goals 
          -- For positivity lemma applications.
          nlinarith [show 0 ≤ (a + b) * (b + c) * (c + a) / 8 by positivity, show 0 ≤ ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) ^ 3 by positivity, h6]
      have h8 : ( ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) ^ 3 ) ^ ((1 : ℝ) / 3) = ( (sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ) / 3 ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals 
          have h81' : (sqrt (a * b) + sqrt (b * c) + sqrt (c * a)) ≥ 0 := by 
            positivity
          nlinarith [show (sqrt (a * b) + sqrt (b * c) + sqrt (c * a)) ≥ 0 by positivity]
      linarith [h7, h8]
    linarith [h4]