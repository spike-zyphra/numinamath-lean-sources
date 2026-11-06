import Mathlib

theorem inequalities_168163 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ≥ ((a * b * c + a * b * d + a * c * d + b * c * d) / 4) ^ ((1 : ℝ) / 3) := by 
  have h1 : 0 < a * b * c := by positivity
  have h2 : 0 < a * b * d := by positivity
  have h3 : 0 < a * c * d := by positivity
  have h4 : 0 < b * c * d := by positivity

  have h5 : 0 < (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by
    positivity

  have h6 : ((a * b * c + a * b * d + a * c * d + b * c * d) / 4) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h7 : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ≥ 0 := by positivity

  have h8 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := Real.sq_sqrt (show (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 ≥ 0 by positivity)
  -- Manipulating left side: (x^1/2)^6 = x^3
  have h12 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 6 = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 3 := by
    calc
      (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 6 
          = ((Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 2) ^ 3 := by ring_nf
      _ = ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 3 := by rw [h8]

  -- Manipulating right side: (x^1/3)^6 = x^2
  have h14 : (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ^ 6 = ( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ 2 := by 
    calc 
      (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ^ 6 
          = ( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3 * (6 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
      _ = ( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ 2 := by
          norm_num

  -- Let L = sqrt((a^2+b^2+c^2+d^2)/4), R = ((abc+abd+acd+bcd)/4)^(1/3). We know L^6 >= R^6 from previous steps. Let's apply transitivity.
  have h15 : ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ^ 3 ≥ ( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2), 
          sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
          sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), 
          mul_pos (show 0 < a * b by positivity) (show 0 < c * d by positivity), 
          mul_pos (show 0 < a * c by positivity) (show 0 < b * d by positivity), 
          mul_pos (show 0 < a * d by positivity) (show 0 < b * c by positivity)
        ]

  -- Now since f(x) = x^6 is strictly monotonic on non-negative part, so preserving inequality
  have h16 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 6 ≥ (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ^ 6 := by 
    rw [h12, h14]
    nlinarith

  -- Now that we have L ^ 6 >= R ^ 6 and L >= 0, R >= 0, we can deduce L >= R.
  have h17 : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ≥ ((a * b * c + a * b * d + a * c * d + b * c * d) / 4) ^ ((1 : ℝ) / 3) := by 
    by_contra h
    push_neg at h
    -- Now given that sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) < ((a * b * c + a * b * d + a * c * d + b * c * d) / 4) ^ ((1 : ℝ) / 3), which contradicts with h16.
    -- The function f(x) = x ^ 6 preserves strict order.
    have h18 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) < (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) := h
    have h19 : (Real.sqrt ((a ^ 2 + b ^ 2 + c  ^ 2 + d ^ 2) / 4)) ^ 6 < (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ^ 6 := by 
      have h20 : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) ≥ 0 := by positivity 
      have h21 : (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ≥ 0 := by positivity
      have h22 : Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4) < (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) := h18
      have h23 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4)) ^ 6 < (( (a * b * c + a * b * d + a * c * d + b * c * d) / 4 ) ^ ((1 : ℝ) / 3) ) ^ 6 := by
        apply pow_lt_pow_left
        all_goals linarith
      linarith

    linarith [h16, h19]

  exact h17