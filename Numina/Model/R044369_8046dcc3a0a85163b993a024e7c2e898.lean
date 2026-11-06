import Mathlib


theorem inequalities_601737 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * Real.sqrt (a * b + b * c + c * a) ≤
    Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by

  have h2 : (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 ≤ (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 := by

    have h3 : (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 = 64 * (a * b + b * c + c * a) ^ 3 := by
      calc
        (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6
          = (2 ^ 6) * (Real.sqrt (a * b + b * c + c * a) ^ 6) := by ring
        _ = 64 * ((Real.sqrt (a * b + b * c + c * a) ) ^ 2) ^ 3 := by ring
        _ = 64 * (a * b + b * c + c * a) ^ 3 := by
          have h31 : (Real.sqrt (a * b + b * c + c * a) ) ^ 2 = a * b + b * c + c * a := Real.sq_sqrt (by positivity)
          rw [h31]

    have h4 : (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 =
        27 * ((b + c) * (c + a) * (a + b)) ^ 2 := by
      calc
        (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6
          = (Real.sqrt 3) ^ 6 * (((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 := by ring
        _ = (Real.sqrt 3) ^ 6 * ((b + c) * (c + a) * (a + b)) ^ (6 * (1 / 3 : ℝ)) := by
          have h8 : (((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 =
              ((b + c) * (c + a) * (a + b)) ^ (6 * (1 / 3 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring_nf
            all_goals
              positivity
          rw [h8]

        _ = (Real.sqrt 3) ^ 6 * ((b + c) * (c + a) * (a + b)) ^ (2 : ℝ) := by
          have h9 : (6 * (1 / 3 : ℝ)) = (2 : ℝ) := by
            norm_num
          rw [h9]

        _ = (Real.sqrt 3) ^ 6 * ((b + c) * (c + a) * (a + b)) ^ 2 := by
          have h10 : ((b + c) * (c + a) * (a + b)) ^ (2 : ℝ) = ((b + c) * (c + a) * (a + b)) ^ 2 := by
            norm_cast
          rw [h10]

        _ = 27 * ((b + c) * (c + a) * (a + b)) ^ 2 := by
          have h32 : (Real.sqrt 3) ^ 2 = 3 := by
            rw [Real.sq_sqrt]
            all_goals
              linarith
          have h33 : (Real.sqrt 3) ^ 6 = 27 := by
            calc
              (Real.sqrt 3) ^ 6 = ((Real.sqrt 3) ^ 2) ^ 3 := by ring
              _ = (3) ^ 3 := by rw [h32]
              _ = (27 : ℝ) := by norm_num
          rw [h33]

    rw [h3, h4]

    have h7 : 64 * (a * b + b * c + c * a) ^ 3 ≤ 27 * ((b + c) * (c + a) * (a + b)) ^ 2 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (mul_pos ha hb) hc
        ]
    linarith

  have h10 : 2 * Real.sqrt (a * b + b * c + c * a) ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by
    have h11 : (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 ≤ (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 := h2
    have h12 : 0 ≤ (2 * Real.sqrt (a * b + b * c + c * a)) := by
      positivity
    have h13 : 0 ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by
      positivity
    have h14 : 2 * Real.sqrt (a * b + b * c + c * a) ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) := by
      by_contra h
      push_neg at h
      have h15 : (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 > (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 := by
        have h16 : (2 * Real.sqrt (a * b + b * c + c * a)) > (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) := by linarith [h]
        have h17 : (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 > (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 := by
          apply pow_lt_pow_left
          all_goals nlinarith [h16, show 0 ≤ Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3) by positivity]
        linarith
      linarith [show (2 * Real.sqrt (a * b + b * c + c * a)) ^ 6 ≤ (Real.sqrt 3 * ((b + c) * (c + a) * (a + b)) ^ ((1 : ℝ) / 3)) ^ 6 by linarith [h11], h15]
    linarith
  linarith