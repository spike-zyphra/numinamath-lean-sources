import Mathlib

open Real

theorem inequalities_280196 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    sqrt ((a + c) * (b + d)) ≥ sqrt (a * b) + sqrt (c * d) ∧ (a*d = b*c → sqrt ((a + c) * (b + d)) = sqrt (a * b) + sqrt (c * d)):= by 
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < c * d := mul_pos hc hd
  have h3 : 0 < (a + c) * (b + d) := by
    positivity
  have h4 : sqrt ((a + c) * (b + d)) ≥ sqrt (a * b) + sqrt (c * d) := by
    have h5 : sqrt ((a + c) * (b + d)) ^ 2 ≥ (sqrt (a * b) + sqrt (c * d)) ^ 2 := by
      have h6 : sqrt ((a + c) * (b + d)) ^ 2 = (a + c) * (b + d) := by
        rw [Real.sq_sqrt]
        positivity
      have h7 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by
        ring
      have h8 : (sqrt (a * b)) ^ 2 = a * b := by
        rw [Real.sq_sqrt]
        positivity
      have h9 : (sqrt (c * d)) ^ 2 = c * d := by
        rw [Real.sq_sqrt]
        positivity
      have h10 : sqrt (a * b) * sqrt (c * d) = sqrt (a * b * (c * d)) := by 
        rw [← Real.sqrt_mul (by positivity)]
        all_goals ring_nf 
      have h11 : a * b * (c * d) = a * b * c * d := by ring
      have h12 : sqrt (a * b * (c * d)) = sqrt (a * b * c * d) := by
        rw [h11]
      nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (sqrt (a * b) - sqrt (c * d)), 
        mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg (c * d)), 
        Real.sq_sqrt (show 0 ≤ (a * b * c * d) by positivity), 
        sq_nonneg (sqrt (a * b * c * d) ^ 2 - (a * b * c * d)), 
        mul_nonneg ha.le hb.le, mul_nonneg ha.le hc.le, 
        mul_nonneg ha.le hd.le, mul_nonneg hb.le hc.le, 
        mul_nonneg hb.le hd.le, mul_nonneg hc.le hd.le
      ]
    have h11 : sqrt ((a + c) * (b + d)) ≥ 0 := by positivity
    have h12 : sqrt (a * b) + sqrt (c * d) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg ((a + c) * (b + d)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), sq_nonneg (sqrt ((a + c) * (b + d)) - (sqrt (a * b) + sqrt (c * d))
    )
    ]
  constructor
  · -- Show the first part of the hypothesis
    exact h4
  · -- Show the equality occurs when a * d = b * c
    intro heq
    have heq1 : sqrt ((a + c) * (b + d)) ^ 2 = (sqrt (a * b) + sqrt (c * d)) ^ 2 := by 
      have e1 : sqrt ((a + c) * (b + d)) ^ 2 = (a + c) * (b + d) := by
        rw [Real.sq_sqrt]
        positivity
      have e2 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by 
        ring
      have e3 : (sqrt (a * b)) ^ 2 = a * b := by
        rw [Real.sq_sqrt]
        positivity
      have e4 : (sqrt (c * d)) ^ 2 = c * d := by
        rw [Real.sq_sqrt]
        positivity
      have heq2 : (a + c) * (b + d) = (a * b + c * d) + (a * d + b * c) := by 
        nlinarith 
      have heq3 : sqrt (a * b) * sqrt (c * d) = sqrt (a * b * c * d) := by
        calc 
          sqrt (a * b) * sqrt (c * d) = sqrt ((a * b) * (c * d)) := by 
            rw [← Real.sqrt_mul (by positivity)]
          _ = sqrt (a * b * c * d) := by 
            have h_eq7 : (a * b) * (c * d) = a * b * c * d := by 
              ring 
            rw [h_eq7]
      have heq4 : sqrt (a * b * c * d) = (a * d) := by
        have h_eq18 : sqrt (a * b * c * d) = sqrt ((a * d) ^ 2) := by 
          have h_eq19 : (a * d) ^ 2 = a * b * c * d := by
            nlinarith [sq_nonneg (a * d - b * c), heq, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
          rw [h_eq19]
          all_goals norm_num 
        have h_eq19 : sqrt ((a * d) ^ 2) = a * d := by 
          rw [Real.sqrt_sq (show 0 ≤ a * d by positivity)]
        rw [h_eq18, h_eq19]
      rw [e1, e2, e3, e4, heq2, heq3, heq4] at *
      all_goals nlinarith 
    have heq2 : sqrt ((a + c) * (b + d)) ≥ 0 := by positivity 
    have heq3 : sqrt (a * b) + sqrt (c * d) ≥ 0 := by positivity 
    nlinarith [Real.sqrt_nonneg ((a + c) * (b + d)), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d),
      heq1
    ]