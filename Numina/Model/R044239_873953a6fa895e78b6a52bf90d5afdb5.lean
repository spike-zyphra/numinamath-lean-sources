import Mathlib

theorem inequalities_63833 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = a * b * c) :
    4 ≤ Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) +
        Real.sqrt ((1 + b ^ 2) * (1 + c ^ 2)) +
        Real.sqrt ((1 + a ^ 2) * (1 + c ^ 2)) -
        Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) := by

  have h1 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) ≥ 1 + a * b := by 
    have h1 : (1 + a ^ 2) * (1 + b ^ 2) ≥ (1 + a * b) ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    have h2 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) ≥ Real.sqrt ((1 + a * b) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h3 : Real.sqrt ((1 + a * b) ^ 2) = 1 + a * b := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith [h3, h2]

  have h2 : Real.sqrt ((1 + b ^ 2) * (1 + c ^ 2)) ≥ 1 + b * c := by 
    have h1 : (1 + b ^ 2) * (1 + c ^ 2) ≥ (1 + b * c) ^ 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h2 : Real.sqrt ((1 + b ^ 2) * (1 + c ^ 2)) ≥ Real.sqrt ((1 + b * c) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h3 : Real.sqrt ((1 + b * c) ^ 2) = 1 + b * c := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith [h3, h2]

  have h3 : Real.sqrt ((1 + a ^ 2) * (1 + c ^ 2)) ≥ 1 + a * c := by 
    have h1 : (1 + a ^ 2) * (1 + c ^ 2) ≥ (1 + a * c) ^ 2 := by
      nlinarith [sq_nonneg (a - c)]
    have h2 : Real.sqrt ((1 + a ^ 2) * (1 + c ^ 2)) ≥ Real.sqrt ((1 + a * c) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h3 : Real.sqrt ((1 + a * c) ^ 2) = 1 + a * c := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith [h3, h2]

  have h4 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2)) +
      Real.sqrt ((1 + b ^ 2) * (1 + c ^ 2)) +
      Real.sqrt ((1 + a ^ 2) * (1 + c ^ 2)) ≥ 3 + (a * b + b * c + a * c) := by 
    linarith [h1, h2, h3]

  have h7 : (a * b + b * c + a * c) ≥ a + b + c := by 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        h]

  have h8 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≤ (a * b + b * c + a * c) - 1 := by
    have h9 : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≤ ((a * b + b * c + a * c) - 1) ^ 2 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          h, sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
          h7]
    have h10 : Real.sqrt ((1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)) ≤ Real.sqrt (((a * b + b * c + a * c) - 1) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h11 : Real.sqrt (((a * b + b * c + a * c) - 1) ^ 2) = (a * b + b * c + a * c) - 1 := by
      rw [Real.sqrt_sq]
      nlinarith
    linarith

  linarith [h4, h8]