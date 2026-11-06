import Mathlib

theorem algebra_223830 {x : ℝ} :
    (x^2 + x + 1) * (x^2 - x + 1) * (x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1) =
    x^8 + x^4 + 1 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have h2 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num
  calc
    (x^2 + x + 1) * (x^2 - x + 1) * (x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1)
        = (x^4 + x^2 + 1) * ((x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1)) := by 
          -- Prove (x^2 + x + 1) * (x^2 - x + 1) = x^4 + x^2 + 1 first
          have h7 : (x^2 + x + 1) * (x^2 - x + 1) = x^4 + x^2 + 1 := by 
            ring
          -- Then, to get the desired form: A * B * C * D = (A*B) * (C*D)
          -- Calculate A*B and place it in front
          -- (A * B) * C * D
          rw [show (x^2 + x + 1) * (x^2 - x + 1) * (x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1) =
              (x^4 + x^2 + 1) * ((x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1)) by 
                rw [h7]; ring]
          all_goals ring
    _ = (x^4 + x^2 + 1) * (x^4 - x^2 + 1) := by 
      -- Prove (x^2 + sqrt 3 * x + 1) * (x^2 - sqrt 3 * x + 1) = x^4 - x^2 + 1
      have h8 : (x^2 + Real.sqrt 3 * x + 1) * (x^2 - Real.sqrt 3 * x + 1) = x^4 - x^2 + 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x * Real.sqrt 3), sq_nonneg (x), sq_nonneg (x^2)]
      rw [h8]
      all_goals ring
    _ = x^8 + x^4 + 1 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x^2), sq_nonneg (x^4)]