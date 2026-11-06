import Mathlib

theorem algebra_306976 (t1 t2 : ℝ) (ht1 : t1 ≠ t2) (h : (1 + Real.sqrt 3 / 2 * t1) ^ 2 = 4 * (2 + 1 / 2 * t1)) (h' : (1 + Real.sqrt 3 / 2 * t2) ^ 2 = 4 * (2 + 1 / 2 * t2)) :
    Real.sqrt ((2 + 1 / 2 * t2 - (2 + 1 / 2 * t1)) ^ 2 + (1 + Real.sqrt 3 / 2 * t2 - (1 + Real.sqrt 3 / 2 * t1)) ^ 2) = 8 / 3 * Real.sqrt (7 - Real.sqrt 3) := by

  have eq1 : 3 * t1 ^ 2 + 4 * Real.sqrt 3 * t1 - 8 * t1 - 28 = 0 := by
    nlinarith [h, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have eq2 : 3 * t2 ^ 2 + 4 * Real.sqrt 3 * t2 - 8 * t2 - 28 = 0 := by
    nlinarith [h', Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have h3 : 3 * (t1 ^ 2 - t2 ^ 2) + 4 * Real.sqrt 3 * (t1 - t2) - 8 * (t1 - t2) = 0 := by 
    nlinarith [eq1, eq2]
  have eq4 : (t1 - t2) * (3 * (t1 + t2) + 4 * Real.sqrt 3 - 8) = 0 := by 
    nlinarith [h3]
  have h4 : 3 * (t1 + t2) + 4 * Real.sqrt 3 - 8 = 0 := by 
    cases (mul_eq_zero.mp eq4) with
    | inl h5 =>
      exfalso 
      apply ht1 
      linarith
    | inr h6 => linarith 
  have h5 : (t1 + t2) = (8 - 4 * Real.sqrt 3) / 3 := by 
    linarith 
  have eq6 : (t2 - t1) ^ 2 = 64 / 9 * (7 - Real.sqrt 3) := by 
    have eq7 : 3 * (t1 * t2) = -28 := by 
      nlinarith [ sq_pos_of_ne_zero (show (t1 - t2 : ℝ) ≠ 0 by 
        by_contra h0 
        have h0' : t1 = t2 := by linarith 
        contradiction 
      ), 
      h4, 
      sq_nonneg (t1 - t2), 
      Real.sqrt_nonneg 3, 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      ]
    nlinarith [ h4, h5, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_pos_of_ne_zero (show (t1 - t2 : ℝ) ≠ 0 by 
      by_contra h0 
      have h0' : t1 = t2 := by linarith 
      contradiction 
    ), sq_nonneg (t1 - t2)
    ]
  have hdist1 : Real.sqrt ((2 + 1 / 2 * t2 - (2 + 1 / 2 * t1)) ^ 2 + (1 + Real.sqrt 3 / 2 * t2 - (1 + Real.sqrt 3 / 2 * t1)) ^ 2) = Real.sqrt ((t2 - t1) ^ 2) := by 
    have h8 : (2 + 1 / 2 * t2 - (2 + 1 / 2 * t1)) ^ 2 + (1 + Real.sqrt 3 / 2 * t2 - (1 + Real.sqrt 3 / 2 * t1)) ^ 2 = (t2 - t1) ^ 2 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    rw [h8]
  have hdist2 : Real.sqrt ((t2 - t1) ^ 2) = abs (t2 - t1) := by 
    rw [Real.sqrt_sq_eq_abs]
  have hdist3 : abs (t2 - t1) = 8 / 3 * Real.sqrt (7 - Real.sqrt 3) := by
    have h5_pos : (7 - Real.sqrt 3) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have eq6_pos : (t2 - t1) ^ 2 = (8 / 3 * Real.sqrt (7 - Real.sqrt 3)) ^ 2 := by 
      nlinarith [eq6, Real.sqrt_nonneg 3, Real.sqrt_nonneg (7 - Real.sqrt 3), 
        Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (Real.sqrt (7 - Real.sqrt 3)), 
        Real.sq_sqrt (show 0 ≤ (7 - Real.sqrt 3 : ℝ) by nlinarith)
        ]
    have h4_pos : abs (t2 - t1) = Real.sqrt ((t2 - t1) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h5_pos2 : Real.sqrt ((t2 - t1) ^ 2) = Real.sqrt ((8 / 3 * Real.sqrt (7 - Real.sqrt 3)) ^ 2) := by 
      rw [eq6_pos]
    have h6_pos : Real.sqrt ((8 / 3 * Real.sqrt (7 - Real.sqrt 3)) ^ 2) = (8 / 3 * Real.sqrt (7 - Real.sqrt 3)) := by 
      have h7_pos : (8 / 3 * Real.sqrt (7 - Real.sqrt 3)) ≥ 0 := by 
        have h8_pos0 : Real.sqrt (7 - Real.sqrt 3) ≥ 0 := Real.sqrt_nonneg (7 - Real.sqrt 3)
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (7 - Real.sqrt 3), h5_pos]
      rw [Real.sqrt_sq (h7_pos)]
    rw [h4_pos, h5_pos2, h6_pos]
  rw [hdist1, hdist2, hdist3]