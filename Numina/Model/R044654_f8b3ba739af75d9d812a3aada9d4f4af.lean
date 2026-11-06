import Mathlib

theorem algebra_1516 {x : ℝ} (hx : x^2 = 5 - 2 * √6) :
    (x^3 = 9 * √3 - 11 * √2 ∨ x^3 = 11 * √2 - 9 * √3) := by
  have h1 : (√3 - √2 : ℝ) ^ 2 = 5 - 2 * √6 := by
    have h2 : √3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
    have h3 : √2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
    have h4 : √3 * √2 = √6 := by 
      calc 
        √3 * √2 = √(3 * 2) := by rw [Real.sqrt_mul (by linarith)]
        _ = √6 := by norm_num
    calc 
      (√3 - √2 : ℝ) ^ 2 = (√3) ^ 2 - 2 * (√3 * √2) + (√2) ^ 2 := by ring
      _ = 3 - 2 * (√3 * √2) + 2 := by rw [h2, h3]
      _ = 3 - 2 * (√6) + 2 := by rw [h4]
      _ = 5 - 2 * √6 := by ring
  have h2 : x^2 = (√3 - √2 : ℝ) ^ 2 := by 
    linarith [h1, hx]
  have h3 : x = (√3 - √2 : ℝ) ∨ x = - (√3 - √2 : ℝ) := by
    have h4 : x^2 - ((√3 - √2 : ℝ) ^ 2) = 0 := by linarith [h2]
    have h5 : (x - (√3 - √2 : ℝ)) * (x + (√3 - √2 : ℝ)) = 0 := by
      nlinarith [h4]
    cases' (mul_eq_zero.1 h5) with h6 h7
    · 
      left 
      linarith 
    · 
      right 
      linarith 
  cases h3 with 
  | inl h4 =>
    -- Let's compute: x^3 = (√3 - √2)³
    -- (√3 - √2)³ = 9√3 - 11√2
    have h5 : x^3 = 9 * √3 - 11 * √2 := by
      rw [show x = √3 - √2 by linarith [h4]]
      have h51 : (√3 - √2 : ℝ) ^ 3 = 9 * √3 - 11 * √2 := by
        have h2 : √3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
        have h3 : √2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
        have h4 : √3 * √2 = √6 := by 
          calc 
            √3 * √2 = √(3 * 2) := by rw [Real.sqrt_mul (by linarith)]
            _ = √6 := by norm_num
        calc 
          (√3 - √2 : ℝ) ^ 3 = √3 ^ 3 - 3 * (√3 ^ 2) * √2 + 3 * √3 * (√2 ^ 2) - √2 ^ 3 := by ring
          _ = √3 * (√3 ^ 2) - 3 * (√3 ^ 2) * √2 + 3 * √3 * (√2 ^ 2) - √2 * (√2 ^ 2) := by ring
          _ = √3 * (3) - 3 * (3) * √2 + 3 * √3 * (2) - √2 * (2) := by 
            rw [h2, h3]
          _ = 3 * √3 - 9 * √2 + 6 * √3 - 2 * √2 := by 
            ring_nf
          _ = 9 * √3 - 11 * √2 := by 
            ring
      linarith [h51]
    left 
    linarith [h5] 
  | inr h4 =>
    have h5 : x^3 = 11 * √2 - 9 * √3 := by
      rw [show x = - (√3 - √2) by linarith [h4]]
      have h7 : (- (√3 - √2) : ℝ) ^3 = 11 * √2 - 9 * √3 := by 
        have h2 : √3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
        have h3 : √2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
        have h4 : √3 * √2 = √6 := by 
          calc 
            √3 * √2 = √(3 * 2) := by rw [Real.sqrt_mul (by linarith)]
            _ = √6 := by norm_num 
        calc 
          (- (√3 - √2) : ℝ) ^3 = -((√3 - √2) ^ 3) := by ring 
          _ = -(9 * √3 - 11 * √2) := by 
            have h51 : (√3 - √2) ^3 = 9 * √3 - 11 * √2 := by 
              calc 
                (√3 - √2) ^ 3 = √3 ^ 3 - 3 * (√3 ^ 2) * √2 + 3 * √3 * (√2 ^ 2) - √2 ^ 3 := by ring 
                _ = √3 * (√3 ^ 2) - 3 * (√3 ^ 2) * √2 + 3 * √3 * (√2 ^ 2) - √2 * (√2 ^ 2) := by ring 
                _ = √3 * (3) - 3 * (3) * √2 + 3 * √3 * (2) - √2 * (2) := by 
                  rw [h2, h3] 
                _ = 3 * √3 - 9 * √2 + 6 * √3 - 2 * √2 := by 
                  ring_nf 
                _ = 9 * √3 - 11 * √2 := by 
                  ring 
            rw [h51] 
          _ = 11 * √2 - 9 * √3 := by 
            ring 
      linarith [h7]
    right 
    linarith [h5]