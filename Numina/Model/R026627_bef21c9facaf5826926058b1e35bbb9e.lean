import Mathlib

open Real

theorem algebra_223768 {a b : ℕ → ℝ}
    (ha0 : a 0 = 2) (hb0 : b 0 = 2)
    (han : ∀ n, a (n + 1) = a n * sqrt (1 + a n ^ 2 + b n ^ 2) - b n)
    (hbn : ∀ n, b (n + 1) = b n * sqrt (1 + a n ^ 2 + b n ^ 2) + a n) :
    a 2017 ^ 2 + b 2017 ^ 2 = 3 ^ (2 ^ 2018) - 1 := by 
  have h1 : ∀ (n : ℕ), a n ^ 2 + b n ^ 2 = 3 ^ (2 ^ (n + 1)) - 1 := by 
    intro n 
    induction n with 
    | zero =>
      have ha1 : a 0 = 2 := ha0
      have hb1 : b 0 = 2 := hb0
      rw [ha1, hb1]
      norm_num 
    | succ n ih =>
      have ha2 : a (n + 1) = a n * sqrt (1 + a n ^ 2 + b n ^ 2) - b n := han n 
      have hb2 : b (n + 1) = b n * sqrt (1 + a n ^ 2 + b n ^ 2) + a n := hbn n 
      calc 
        a (n + 1) ^ 2 + b (n + 1) ^ 2 = (a (n + 1)) ^ 2 + (b (n + 1)) ^ 2 := by ring 
        _ = (a n * sqrt (1 + a n ^ 2 + b n ^ 2) - b n) ^ 2 + (b n * sqrt (1 + a n ^ 2 + b n ^ 2) + a n) ^ 2 := by rw [ha2, hb2] 
        _ = (a n ^ 2 + b n ^ 2) * ( (sqrt (1 + a n ^ 2 + b n ^ 2)) ^ 2 + 1 ) := by 
          nlinarith [Real.sqrt_nonneg (1 + a n ^ 2 + b n ^ 2), sq_nonneg (sqrt (1 + a n ^ 2 + b n ^ 2) ^ 2 - 1) ]
        _ = (a n ^ 2 + b n ^ 2) * (1 + a n ^ 2 + b n ^ 2 + 1 ) := by 
          have h2 : (sqrt (1 + a n ^ 2 + b n ^ 2)) ^ 2 = 1 + a n ^ 2 + b n ^ 2 := by
            apply Real.sq_sqrt 
            positivity
          rw [h2]
        _ = (a n ^ 2 + b n ^ 2) * ( (a n ^ 2 + b n ^ 2) + 2 ) := by ring 
        _ = (3 ^ (2 ^ (n + 1)) - 1) * ( (3 ^ (2 ^ (n + 1)) - 1) + 2 ) := by 
          rw [ih] 
        _ = 3 ^ (2 ^ (n + 1 + 1)) - 1 := by 
          ring_nf 
  have h2017 : a 2017 ^ 2 + b 2017 ^ 2 = 3 ^ (2 ^ (2017 + 1)) - 1 := by 
    specialize h1 2017 
    simpa using h1 
  rw [h2017]
  <;> norm_num