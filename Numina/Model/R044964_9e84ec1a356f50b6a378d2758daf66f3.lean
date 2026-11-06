import Mathlib

theorem algebra_304839 {a b : ℕ → ℝ} (ha0 : a 0 = 2) (hb0 : b 0 = 2)
    (han : ∀ n, a (n + 1) = a n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) - b n)
    (hbn : ∀ n, b (n + 1) = b n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) + a n) :
    a 2017 ^ 2 + b 2017 ^ 2 = 3 ^ (2 ^ 2018) - 1 := by
  have h1 : ∀ (n : ℕ), (a n) ^ 2 + (b n) ^ 2 = 3 ^ (2 ^ (n + 1)) - 1 := by 
    intro n 
    induction n with 
    | zero => 
      have ha0' : a 0 = 2 := ha0 
      have hb0' : b 0 = 2 := hb0 
      rw [ha0', hb0'] 
      norm_num 
    | succ n ih => 
      have h2 : a (n + 1) = a n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) - b n := han n 
      have h3 : b (n + 1) = b n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) + a n := hbn n 
      have h4 : a (n + 1) ^ 2 + b (n + 1) ^ 2 = (a n ^ 2 + b n ^ 2) * (a n ^ 2 + b n ^ 2 + 2) := by
        rw [h2, h3] 
        have h5 : Real.sqrt (1 + a n ^ 2 + b n ^ 2) ≥ 0 := Real.sqrt_nonneg (1 + a n ^ 2 + b n ^ 2)
        have h6 : (Real.sqrt (1 + a n ^ 2 + b n ^ 2)) ^ 2 = 1 + a n ^ 2 + b n ^ 2 := Real.sq_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (1 + a n ^ 2 + b n ^ 2), Real.sq_sqrt (show 0 ≤ (1 + a n ^ 2 + b n ^ 2 : ℝ) by positivity), sq_nonneg (a n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) - b n), sq_nonneg (b n * Real.sqrt (1 + a n ^ 2 + b n ^ 2) + a n)]
      rw [h4] 
      rw [ih] 
      ring_nf
  specialize h1 2017 
  simpa using h1