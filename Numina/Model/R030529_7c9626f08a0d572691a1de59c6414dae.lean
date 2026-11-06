import Mathlib

theorem my_favorite_theorem (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 ≥
    512 * (1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4) := by

  have h4 (d : ℝ) (hd : 0 < d) : (1 + d ^ 3) ^ 4 ≥ 8 * d ^ 4 * (1 + d ^ 4) := by
    have h6 : (1 + d ^ 3) ^ 4 - 8 * d ^ 4 * (1 + d ^ 4) ≥ 0 := by
      nlinarith [sq_nonneg (d ^ 3 - 1), sq_nonneg (d ^ 4 - 1), sq_nonneg (d ^ 3 - d), sq_nonneg (d ^ 4 - d), sq_nonneg (d ^ 2 - 1), sq_nonneg (d - 1), 
    mul_pos hd hd, mul_pos hd (show 0 < d ^ 2 by positivity), mul_pos (show 0 < d ^ 2 by positivity) (show 0 < d by exact hd)]
    linarith

  have h7 : (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 ≥ (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) := by
    have h1a : (1 + a ^ 3) ^ 4 ≥ 8 * a ^ 4 * (1 + a ^ 4) := by
      apply h4 a ha
    have h1b : (1 + b ^ 3) ^ 4 ≥ 8 * b ^ 4 * (1 + b ^ 4) := by
      apply h4 b hb
    have h1c : (1 + c ^ 3) ^ 4 ≥ 8 * c ^ 4 * (1 + c ^ 4) := by
      apply h4 c hc

    have h8 : 0 ≤ (1 + a ^ 3) ^ 4 := by positivity
    have h9 : 0 ≤ (1 + b ^ 3) ^ 4 := by positivity
    have h10 : 0 ≤ (1 + c ^ 3) ^ 4 := by positivity
    have h11 : 0 ≤ 8 * a ^ 4 * (1 + a ^ 4) := by positivity
    have h12 : 0 ≤ 8 * b ^ 4 * (1 + b ^ 4) := by positivity
    have h13 : 0 ≤ 8 * c ^ 4 * (1 + c ^ 4) := by positivity

    have h14 : (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 ≥ (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) := by
      have h8 : (1 + a ^ 3) ^ 4 ≥ 8 * a ^ 4 * (1 + a ^ 4) := h1a
      have h9 : (1 + b ^ 3) ^ 4 ≥ 8 * b ^ 4 * (1 + b ^ 4) := h1b
      have h10 : 0 ≤ (1 + a ^ 3) ^ 4 := by positivity
      have h11 : 0 ≤ (1 + b ^ 3) ^ 4 := by positivity
      have h12 : 0 ≤ 8 * a ^ 4 * (1 + a ^ 4) := by positivity
      have h13 : 0 ≤ 8 * b ^ 4 * (1 + b ^ 4) := by positivity
      nlinarith [mul_nonneg (show 0 ≤ (1 + a ^ 3) ^ 4 by positivity) (show 0 ≤ (1 + b ^ 3) ^ 4 by positivity), 
        mul_nonneg (show 0 ≤ (8 * a ^ 4 * (1 + a ^ 4)) by positivity) (show 0 ≤ (8 * b ^ 4 * (1 + b ^ 4)) by positivity)]

    have h15 : (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 ≥ (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) := by
      have h16 : (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 = ((1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4) * (1 + c ^ 3) ^ 4 := by ring
      rw [h16]
      have h17 : ( (8 * a ^ 4 * (1 + a ^ 4) ) * (8 * b ^ 4 * (1 + b ^ 4) ) ) * (8 * c ^ 4 * (1 + c ^ 4) ) = (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) := by ring 
      rw [h17]
      apply mul_le_mul
      · exact h14
      · exact h1c
      all_goals
        try { positivity }
        all_goals try { nlinarith } 
    exact h15

  have h2 : (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) = 512 * (1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4) := by
    calc
      (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) 
        = 8^3 * (a ^ 4 * b ^ 4 * c ^ 4) * ((1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4)) := by ring
      _ = 8^3 * 1 * ((1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4)) := by
        have h0 : a ^ 4 * b ^ 4 * c ^ 4 = 1 := by
          calc
            a ^ 4 * b ^ 4 * c ^ 4 = (a * b * c) ^ 4 := by ring
            _ = 1 ^ 4 := by rw [habc]
            _ = 1 := by norm_num
        rw [h0]
        all_goals ring 
      _ = 512 * (1 + a ^ 4) * (1 + b ^ 4) * (1 + c ^ 4) := by ring_nf

  have h6 : (1 + a ^ 3) ^ 4 * (1 + b ^ 3) ^ 4 * (1 + c ^ 3) ^ 4 ≥ (8 * a ^ 4 * (1 + a ^ 4)) * (8 * b ^ 4 * (1 + b ^ 4)) * (8 * c ^ 4 * (1 + c ^ 4)) := h7
  linarith [h6, h2]