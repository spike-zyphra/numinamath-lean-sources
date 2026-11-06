import Mathlib


theorem inequalities_126245 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    (b * c * d / (1 - a) ^ 2) +
    (c * d * a / (1 - b) ^ 2) +
    (d * a * b / (1 - c) ^ 2) +
    (a * b * c / (1 - d) ^ 2) ≤ 1 / 9 := by


  have h1 : 1 - a = b + c + d := by
    nlinarith
  have h2 : 1 - b = a + c + d := by
    nlinarith
  have h3 : 1 - c = a + b + d := by
    nlinarith
  have h4 : 1 - d = a + b + c := by
    nlinarith

  have h5 : b * c * d / (1 - a) ^ 2 ≤ (b + c + d) / 27 := by
    rw [show 1 - a = b + c + d by linarith]
    have h10 : 0 < b + c + d := by
      nlinarith
    have h11 : b * c * d ≤ (b + c + d) ^ 3 / 27 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - b),
          sq_nonneg (b + c + d), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * b), sq_nonneg (d * b - b * c),
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
        ]
    have h12 : b * c * d / (b + c + d) ^ 2 ≤ (b + c + d) / 27 := by
      have h10 : 0 < (b + c + d) ^ 2 := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h11]
    linarith

  have h6 : c * d * a / (1 - b) ^ 2 ≤ (a + c + d) / 27 := by
    rw [show 1 - b = a + c + d by linarith]
    have h10 : 0 < a + c + d := by
      nlinarith
    have h11 : c * d * a ≤ (a + c + d) ^ 3 / 27 := by
      nlinarith [sq_nonneg (c - d), sq_nonneg (d - a), sq_nonneg (a - c),
          sq_nonneg (a + c + d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * c), sq_nonneg (a * c - c * d),
          mul_pos ha hc, mul_pos ha hd, mul_pos hc hd
        ]
    have h12 : c * d * a / (a + c + d) ^ 2 ≤ (a + c + d) / 27 := by
      have h10 : 0 < (a + c + d) ^ 2 := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h11]
    linarith

  have h7 : d * a * b / (1 - c) ^ 2 ≤ (a + b + d) / 27 := by
    rw [show 1 - c = a + b + d by linarith]
    have h10 : 0 < a + b + d := by
      nlinarith
    have h11 : d * a * b ≤ (a + b + d) ^ 3 / 27 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - d), sq_nonneg (d - a),
          sq_nonneg (a + b + d), sq_nonneg (a * b - b * d), sq_nonneg (b * d - d * a), sq_nonneg (d * a - a * b),
          mul_pos ha hb, mul_pos ha hd, mul_pos hb hd
        ]
    have h12 : d * a * b / (a + b + d) ^ 2 ≤ (a + b + d) / 27 := by
      have h10 : 0 < (a + b + d) ^ 2 := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h11]
    linarith

  have h8 : a * b * c / (1 - d) ^ 2 ≤ (a + b + c) / 27 := by
    rw [show 1 - d = a + b + c by linarith]
    have h10 : 0 < a + b + c := by
      nlinarith
    have h11 : a * b * c ≤ (a + b + c) ^ 3 / 27 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    have h12 : a * b * c / (a + b + c) ^ 2 ≤ (a + b + c) / 27 := by
      have h10 : 0 < (a + b + c) ^ 2 := by
        positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h11]
    linarith

  have h9 : (b * c * d / (1 - a) ^ 2) +
      (c * d * a / (1 - b) ^ 2) +
      (d * a * b / (1 - c) ^ 2) +
      (a * b * c / (1 - d) ^ 2) ≤ 1 / 9 := by
    have h10 : (b * c * d / (1 - a) ^ 2) +
        (c * d * a / (1 - b) ^ 2) +
        (d * a * b / (1 - c) ^ 2) +
        (a * b * c / (1 - d) ^ 2) ≤ (b + c + d) / 27 + (a + c + d) / 27 + (a + b + d) / 27 + (a + b + c) / 27 := by
      linarith [h5, h6, h7, h8]
    have h11 : (b + c + d) / 27 + (a + c + d) / 27 + (a + b + d) / 27 + (a + b + c) / 27 = 1 / 9 := by
      have h10 : a + b + c + d = 1 := h
      have h11 : (b + c + d) / 27 + (a + c + d) / 27 + (a + b + d) / 27 + (a + b + c) / 27 =
          (3 * (a + b + c + d)) / 27 := by
        ring
      rw [h11]
      rw [show a + b + c + d = 1 by linarith]
      norm_num
    linarith [h10, h11]
  exact h9