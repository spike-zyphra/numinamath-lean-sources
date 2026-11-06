import Mathlib

open Real

theorem inequalities_298307 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    sqrt (a^2 + b^2) + sqrt (b^2 + c^2) + sqrt (c^2 + a^2) ≥ sqrt 2 * (a + b + c) ∧
    (sqrt (a^2 + b^2) + sqrt (b^2 + c^2) + sqrt (c^2 + a^2) = sqrt 2 * (a + b + c) ↔
      a = b ∧ b = c) := by 
  have h1 : sqrt (a^2 + b^2) ≥ Real.sqrt 2 / 2 * (a + b) := by
    have h2 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 ≤ a^2 + b^2 := by
      have h3 : 0 < a + b := by linarith
      have h4 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 = (Real.sqrt 2 ^ 2) / 4 * (a + b) ^ 2 := by 
        ring_nf
      rw [h4]
      have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
      rw [h5]
      nlinarith [sq_nonneg (a - b)]
    have h6 : Real.sqrt 2 / 2 * (a + b) ≤ Real.sqrt (a^2 + b^2) := by
      have h7 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 ≤ a^2 + b^2 := h2
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (a + b) := by
        positivity
      have h9 : Real.sqrt ((Real.sqrt 2 / 2 * (a + b)) ^ 2) ≤ Real.sqrt (a^2 + b^2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h10 : Real.sqrt ((Real.sqrt 2 / 2 * (a + b)) ^ 2) = Real.sqrt 2 / 2 * (a + b) := by
        rw [Real.sqrt_sq]
        positivity
      linarith
    linarith
  have h2 : sqrt (b^2 + c^2) ≥ Real.sqrt 2 / 2 * (b + c) := by
    have h2 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 ≤ b^2 + c^2 := by
      have h3 : 0 < b + c := by linarith
      have h4 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 = (Real.sqrt 2 ^ 2) / 4 * (b + c) ^ 2 := by 
        ring_nf
      rw [h4]
      have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
      rw [h5]
      nlinarith [sq_nonneg (b - c)]
    have h6 : Real.sqrt 2 / 2 * (b + c) ≤ Real.sqrt (b^2 + c^2) := by
      have h7 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 ≤ b^2 + c^2 := h2
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (b + c) := by
        positivity
      have h9 : Real.sqrt ((Real.sqrt 2 / 2 * (b + c)) ^ 2) ≤ Real.sqrt (b^2 + c^2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h10 : Real.sqrt ((Real.sqrt 2 / 2 * (b + c)) ^ 2) = Real.sqrt 2 / 2 * (b + c) := by
        rw [Real.sqrt_sq]
        positivity
      linarith
    linarith
  have h3 : sqrt (c^2 + a^2) ≥ Real.sqrt 2 / 2 * (c + a) := by
    have h2 : (Real.sqrt 2 / 2 * (c + a)) ^ 2 ≤ c^2 + a^2 := by
      have h3 : 0 < c + a := by linarith
      have h4 : (Real.sqrt 2 / 2 * (c + a)) ^ 2 = (Real.sqrt 2 ^ 2) / 4 * (c + a) ^ 2 := by 
        ring_nf
      rw [h4]
      have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
      rw [h5]
      nlinarith [sq_nonneg (c - a)]
    have h6 : Real.sqrt 2 / 2 * (c + a) ≤ Real.sqrt (c^2 + a^2) := by
      have h7 : (Real.sqrt 2 / 2 * (c + a)) ^ 2 ≤ c^2 + a^2 := h2
      have h8 : 0 ≤ Real.sqrt 2 / 2 * (c + a) := by
        positivity
      have h9 : Real.sqrt ((Real.sqrt 2 / 2 * (c + a)) ^ 2) ≤ Real.sqrt (c^2 + a^2) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h10 : Real.sqrt ((Real.sqrt 2 / 2 * (c + a)) ^ 2) = Real.sqrt 2 / 2 * (c + a) := by
        rw [Real.sqrt_sq]
        positivity
      linarith
    linarith
  constructor
  · nlinarith [h1, h2, h3, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith : (2 : ℝ) ≥ 0)]
  constructor
  · -- Assume sqrt(a^2 + b^2) + sqrt(b^2 + c^2) + sqrt(c^2 + a^2) = sqrt 2 * (a + b + c), prove a = b ∧ b = c
    intro heq
    have heq1 : sqrt (a^2 + b^2) = Real.sqrt 2 / 2 * (a + b) := by
      nlinarith [h1, h2, h3, heq, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith : (2 : ℝ) ≥ 0)]
    have heq10 : (a - b) ^ 2 = 0 := by
      have heq4 : (sqrt (a^2 + b^2)) ^ 2 = (Real.sqrt 2 / 2 * (a + b)) ^ 2 := by 
        rw [heq1]
      have heq5 : (sqrt (a^2 + b^2)) ^ 2 = a^2 + b^2 := by 
        apply Real.sq_sqrt
        positivity
      have heq050 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 = (2 : ℝ) / 4 * (a + b) ^ 2 := by 
        have heq8 : Real.sqrt 2 ^ 2 = 2 := by
          exact Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (2 : ℝ))
        calc 
          (Real.sqrt 2 / 2 * (a + b)) ^ 2 = (Real.sqrt 2 ^ 2) / 4 * (a + b) ^ 2 := by
            ring
          _ = (2 : ℝ) / 4 * (a + b) ^ 2 := by 
            rw [heq8]
      rw [heq5, heq050] at heq4
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have heq11 : a - b = 0 := by
      nlinarith
    have heq15 : a = b := by
      linarith
    have heq13 : sqrt (b^2 + c^2) = Real.sqrt 2 / 2 * (b + c) := by
      nlinarith [h1, h2, h3, heq, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith : (2 : ℝ) ≥ 0)]
    have heq05 : (b - c) ^ 2 = 0 := by
      have heq300 : (sqrt (b^2 + c^2)) ^ 2 = (Real.sqrt 2 / 2 * (b + c)) ^ 2 := by 
        rw [heq13]
      have heq31 : (sqrt (b^2 + c^2)) ^ 2 = b^2 + c^2 := by 
        apply Real.sq_sqrt
        positivity
      have heq050 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 = (2 : ℝ) / 4 * (b + c) ^ 2 := by 
        have heq8 : Real.sqrt 2 ^ 2 = 2 := by
          exact Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (2 : ℝ))
        calc 
          (Real.sqrt 2 / 2 * (b + c)) ^ 2 = (Real.sqrt 2 ^ 2) / 4 * (b + c) ^ 2 := by
            ring
          _ = (2 : ℝ) / 4 * (b + c) ^ 2 := by 
            rw [heq8]
      rw [heq31, heq050] at heq300
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have heq16 : b = c := by
      have heq051 : b - c = 0 := by
        nlinarith [heq05]
      linarith
    constructor
    · linarith [heq15]
    · linarith [heq16]
  · -- Assume a = b ∧ b = c, prove sqrt(a^2 + b^2) + sqrt(b^2 + c^2) + sqrt(c^2 + a^2) = sqrt 2 * (a + b + c)
    rintro ⟨rfl, rfl⟩
    have h8 : sqrt (a^2 + a^2) = Real.sqrt 2 * a := by
      have heq7 : (sqrt (a^2 + a^2)) ^ 2 = (Real.sqrt 2 * a) ^ 2 := by
        have heq6 : (sqrt (a^2 + a^2)) ^ 2 = a^2 + a^2 := by
          apply Real.sq_sqrt
          positivity
        have heq5 : (Real.sqrt 2 * a) ^ 2 = 2 * a^2 := by
          calc
            (Real.sqrt 2 * a) ^ 2 = Real.sqrt 2 ^ 2 * a^2 := by ring
            _ = 2 * a^2 := by 
              have heq4 : Real.sqrt 2 ^ 2 = 2 := by
                exact Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (2 : ℝ))
              rw [heq4]
            _ = 2 * a^2 := by ring
        nlinarith [heq5, heq6]
      have ha3 : 0 ≤ Real.sqrt 2 * a := by 
        positivity
      have heq678 : sqrt ((sqrt (a^2 + a^2)) ^ 2) = sqrt ((Real.sqrt 2 * a) ^ 2) := by 
        rw [heq7]
      have ha345 : sqrt ((sqrt (a^2 + a^2)) ^ 2) = sqrt (a^2 + a^2) := by 
        apply Real.sqrt_sq 
        positivity
      have ha346 : sqrt ((Real.sqrt 2 * a) ^ 2) = Real.sqrt 2 * a := by 
        rw [Real.sqrt_sq] 
        positivity
      nlinarith
    nlinarith [h8, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith : (2 : ℝ) ≥ 0)]