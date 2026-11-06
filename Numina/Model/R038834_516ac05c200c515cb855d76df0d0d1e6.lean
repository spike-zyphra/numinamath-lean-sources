import Mathlib

theorem inequalities_89483 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) +
        1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by

  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < c := by linarith
  have h4 : 0 < d := by linarith

  have h5 : 0 < 4 * a + 3 * b + c := by nlinarith
  have h6 : 0 < 3 * a + b + 4 * d := by nlinarith
  have h7 : 0 < a + 4 * c + 3 * d := by nlinarith
  have h8 : 0 < 4 * b + 3 * c + d := by nlinarith

  have h9 : 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) ≥ 4 / (7 * a + 4 * b + c + 4 * d) := by
    have h10 : 0 < (4 * a + 3 * b + c : ℝ) := by positivity
    have h11 : 0 < (3 * a + b + 4 * d : ℝ) := by positivity
    have h13 : 0 < (4 * a + 3 * b + c + (3 * a + b + 4 * d) : ℝ) := by nlinarith
    have h14 : (4 * a + 3 * b + c + (3 * a + b + 4 * d) : ℝ) = 7 * a + 4 * b + c + 4 * d := by 
      nlinarith 
    have h16 : (1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) : ℝ) - 4 / (7 * a + 4 * b + c + 4 * d) ≥ 0 := by 
      have h10 : 0 < (4 * a + 3 * b + c : ℝ) := by positivity
      have h11 : 0 < (3 * a + b + 4 * d : ℝ) := by positivity
      have h17 : 0 < (7 * a + 4 * b + c + 4 * d : ℝ) := by 
        nlinarith 
      have h18 : (1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) - 4 / (7 * a + 4 * b + c + 4 * d) : ℝ) = 
        ( ((3 * a + b + 4 * d) + (4 * a + 3 * b + c)) * (7 * a + 4 * b + c + 4 * d) - 4 * ((4 * a + 3 * b + c) * (3 * a + b + 4 * d)) ) / ((4 * a + 3 * b + c) * (3 * a + b + 4 * d) * (7 * a + 4 * b + c + 4 * d)) := by 
        field_simp 
        <;> ring 
      rw [h18]
      apply div_nonneg
      nlinarith [sq_nonneg ((4 * a + 3 * b + c) - (3 * a + b + 4 * d)), sq_nonneg ((a - c)), sq_nonneg ((b - d)), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
      positivity 
    linarith 
  have h10 : 1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) ≥ 4 / (a + 4 * b + 7 * c + 4 * d) := by
    have h11 : 0 < (a + 4 * c + 3 * d : ℝ) := by positivity
    have h12 : 0 < (4 * b + 3 * c + d : ℝ) := by positivity
    have h13 : (a + 4 * c + 3 * d + (4 * b + 3 * c + d) : ℝ) = a + 4 * b + 7 * c + 4 * d := by 
      nlinarith 
    have h16 : (1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) : ℝ) - 4 / (a + 4 * b + 7 * c + 4 * d) ≥ 0 := by 
      have h11 : 0 < (a + 4 * c + 3 * d : ℝ) := by positivity
      have h12 : 0 < (4 * b + 3 * c + d : ℝ) := by positivity
      have h18 : 0 < (a + 4 * b + 7 * c + 4 * d : ℝ) := by 
        nlinarith 
      have h19 : (1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) - 4 / (a + 4 * b + 7 * c + 4 * d) : ℝ) = 
        ( ((4 * b + 3 * c + d) + (a + 4 * c + 3 * d)) * (a + 4 * b + 7 * c + 4 * d) - 4 * ((a + 4 * c + 3 * d) * (4 * b + 3 * c + d)) ) / ((a + 4 * c + 3 * d) * (4 * b + 3 * c + d) * (a + 4 * b + 7 * c + 4 * d)) := by 
        field_simp 
        <;> ring 
      rw [h19]
      apply div_nonneg 
      nlinarith [sq_nonneg ((a + 4 * c + 3 * d) - (4 * b + 3 * c + d)), sq_nonneg ((a - c)), sq_nonneg ((b - d)), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
      positivity 
    linarith 
  have h11 : (4 / (7 * a + 4 * b + c + 4 * d) + 4 / (a + 4 * b + 7 * c + 4 * d) : ℝ) ≥ 2 := by
    have h12 : (7 * a + 4 * b + c + 4 * d : ℝ) = 4 + 3 * (a - c) := by 
      have h13 : a + b + c + d = 1 := h 
      nlinarith 
    have h13 : (a + 4 * b + 7 * c + 4 * d : ℝ) = 4 - 3 * (a - c) := by 
      have h14 : a + b + c + d = 1 := h 
      nlinarith 
    rw [h12, h13]
    have h14 : 0 < (4 + 3 * (a - c) : ℝ) := by 
      nlinarith 
    have h15 : 0 < (4 - 3 * (a - c) : ℝ) := by 
      nlinarith 
    have h16 : (4 / (4 + 3 * (a - c)) + 4 / (4 - 3 * (a - c)) : ℝ) ≥ 2 := by 
      have h17 : (4 / (4 + 3 * (a - c)) + 4 / (4 - 3 * (a - c)) : ℝ) - 2 ≥ 0 := by 
        have h18 : (4 / (4 + 3 * (a - c)) + 4 / (4 - 3 * (a - c)) - 2 : ℝ) = (32 - 2 * (16 - 9 * (a - c) ^ 2) ) / ( (4 + 3 * (a - c)) * (4 - 3 * (a - c)) ) := by 
          field_simp [(show (4 + 3 * (a - c) : ℝ) ≠ 0 by nlinarith), (show (4 - 3 * (a - c) : ℝ) ≠ 0 by nlinarith)]
          <;> ring 
        rw [h18]
        apply div_nonneg 
        nlinarith [sq_nonneg (a - c), mul_pos ha hc]
        positivity 
      linarith 
    linarith 
  linarith [h9, h10, h11]