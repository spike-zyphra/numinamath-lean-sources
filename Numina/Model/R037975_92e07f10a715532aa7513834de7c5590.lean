import Mathlib

theorem inequalities_147506 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a ^ 2 + 1) * (b ^ 3 + 2) * (c ^ 6 + 5) ≥ 36 := by
  have h1 : a ^ 2 + 1 ≥ 2 * a := by
    nlinarith [sq_nonneg (a - 1)]
  
  have h2 : b ^ 3 + 2 ≥ 3 * b := by
    have h2' : b ^ 3 + 2 - 3 * b ≥ 0 := by
      have h8 : b ^ 3 + 2 - 3 * b = (b - 1) ^ 2 * (b + 2) := by
        nlinarith 
      have h9 : (b - 1) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      have h10 : (b + 2) > 0 := by 
        nlinarith [hb]
      have h11 : (b - 1) ^ 2 * (b + 2) ≥ 0 := by 
        apply mul_nonneg 
        exact h9 
        linarith 
      linarith [h8, h11]
    linarith
  
  have h3 : c ^ 6 + 5 ≥ 6 * c := by 
    have h3' : c ^ 6 + 5 - 6 * c ≥ 0 := by
      nlinarith [sq_nonneg (c ^ 3 - 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c - 1), 
        sq_nonneg (c ^ 3), sq_nonneg (c ^ 2), sq_nonneg (c - 1), 
        sq_nonneg (c ^ 2 - c), sq_nonneg (c ^ 2 + c - 1), 
        mul_pos hc (show 0 < c by linarith), 
        mul_pos (show 0 < c by linarith) (show 0 < c ^ 2 by positivity)]
    linarith
  
  have h4 : (a ^ 2 + 1) * (b ^ 3 + 2) * (c ^ 6 + 5) ≥ (2 * a) * (3 * b) * (6 * c) := by
    have h20 : 0 < (a ^ 2 + 1 : ℝ) := by positivity
    have h21 : 0 < (b ^ 3 + 2 : ℝ) := by positivity
    have h22 : 0 < (c ^ 6 + 5 : ℝ) := by positivity
    have h23 : 0 < (2 * a : ℝ) := by positivity
    have h24 : 0 < (3 * b : ℝ) := by positivity
    have h25 : 0 < (6 * c : ℝ) := by positivity
    have h61 : (a ^ 2 + 1) * (b ^ 3 + 2) ≥ (2 * a) * (3 * b) := by 
      nlinarith [h1, h2, mul_nonneg (show 0 ≤ a ^ 2 + 1 - 2 * a by linarith [h1]) (show 0 ≤ b ^ 3 + 2 - 3 * b by linarith [h2]), sq_nonneg (a - 1), sq_nonneg (b - 1)]
    have h62 : (a ^ 2 + 1) * (b ^ 3 + 2) * (c ^ 6 + 5) ≥ (2 * a) * (3 * b) * (6 * c) := by 
      have h63 : (a ^ 2 + 1) * (b ^ 3 + 2) * (c ^ 6 + 5) = ((a ^ 2 + 1) * (b ^ 3 + 2)) * (c ^ 6 + 5) := by ring
      rw [h63]
      have h64 : (2 * a) * (3 * b) * (6 * c) = ((2 * a) * (3 * b)) * (6 * c) := by ring
      rw [h64]
      have h140 : 0 ≤ (a ^ 2 + 1) * (b ^ 3 + 2) := by positivity
      have h141 : 0 ≤ (2 * a) * (3 * b) := by positivity
      have h142 : 0 ≤ (c ^ 6 + 5) := by positivity
      have h143 : 0 ≤ (6 * c) := by positivity
      have h144 : ((a ^ 2 + 1) * (b ^ 3 + 2)) * (c ^ 6 + 5) ≥ ((2 * a) * (3 * b)) * (6 * c) := by
        apply mul_le_mul
        all_goals
          try nlinarith [h61, h3, mul_nonneg (show 0 ≤ (a ^ 2 + 1) * (b ^ 3 + 2) - (2 * a) * (3 * b) by nlinarith [h61]) (show 0 ≤ c ^ 6 + 5 - 6 * c by linarith [h3]), sq_nonneg (a^2 +1 - 2*a), sq_nonneg (b^3+2 - 3*b), sq_nonneg (c^6+5 - 6*c)]
          try positivity
      linarith
    linarith
  
  have h5 : (2 * a) * (3 * b) * (6 * c) = 36 * (a * b * c) := by
    ring
  
  have h6 : (a ^ 2 + 1) * (b ^ 3 + 2) * (c ^ 6 + 5) ≥ 36 * (a * b * c) := by 
    nlinarith [h4, h5]

  have h7 : 36 * (a * b * c) = 36 := by
    rw [habc]
    all_goals nlinarith
  
  linarith [h6, h7]