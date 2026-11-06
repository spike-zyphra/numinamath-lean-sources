import Mathlib

open Real

theorem inequalities_209846 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 / (2 * (a + b)) ≤ sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b) ∧
    sqrt ((a ^ 2 + b ^ 2) / 2) - sqrt (a * b) ≤ (a - b) ^ 2 / (sqrt 2 * (a + b)) := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : Real.sqrt (a * b) ≥ 0 := by positivity
  have h3 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
  have h4 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
  have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)
  have h6 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
    have h7 : (a ^ 2 + b ^ 2) / 2 ≥ a * b := by 
      nlinarith [sq_nonneg (a - b)]
    have h8 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
      apply Real.sqrt_le_sqrt
      linarith
    exact h8
  constructor
  · -- Prove the left side of the inequality.
    have h8 : (a - b) ^ 2 / (2 * (a + b)) ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) := by
      have h10 : (a - b) ^ 2 ≤ 2 * (a + b) * (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)) := by
        have h14 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := h6
        have h140 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) ≥ 0 := by linarith
        nlinarith [sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) - (a - b) ^ 2 / (2 * (a + b))), 
          sq_nonneg (a - b), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - (a ^ 2 + b ^ 2) / 2), 
          sq_nonneg (Real.sqrt (a * b) ^ 2 - a * b), 
          Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), 
          Real.sqrt_nonneg (a * b), 
          sq_nonneg (a ^ 2 + b ^ 2 - 2 * a * b), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)) (Real.sqrt_nonneg (a * b)), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)), 
          sq_nonneg (a + b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity) 
        ]
      have h11 : (a - b) ^ 2 / (2 * (a + b)) ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) := by
        have h12 : 0 < (2 * (a + b) : ℝ) := by positivity
        apply (div_le_iff₀ (by positivity)).mpr
        all_goals linarith
      linarith
    exact h8
  · -- Now the right side.
    have h4 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (Real.sqrt 2 * (a + b)) := by
      have h19 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
        have h18 : (a ^ 2 + b ^ 2) / 2 ≥ a * b := by 
          nlinarith [sq_nonneg (a - b)]
        have h20 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
          apply Real.sqrt_le_sqrt
          linarith
        linarith
      have h19a : (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)) * (Real.sqrt 2 * (a + b)) ≤ (a - b) ^ 2 := by
        have h30 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have h31 : 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)
        have h32 : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
        have h37 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 = (a ^ 2 + b ^ 2) / 2 := by 
          rw [Real.sq_sqrt]
          positivity
        have h38 : Real.sqrt (a * b) ^ 2 = a * b := by 
          rw [Real.sq_sqrt]
          positivity
        have h39 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith [sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - Real.sqrt (a * b) ^ 2), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)), 
          sq_nonneg (a - b), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - (a + b) / Real.sqrt 2), 
          sq_nonneg (Real.sqrt (a * b) - (a + b) / 2), 
          mul_nonneg (show 0 ≤ Real.sqrt 2 by positivity) (show 0 ≤ Real.sqrt 2 by positivity), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) * Real.sqrt 2 - Real.sqrt (a * b) * Real.sqrt 2), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - 2 * Real.sqrt (a * b) ^ 2), 
          mul_nonneg (show 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) by positivity) (show 0 ≤ Real.sqrt (a * b) by positivity), 
          sq_nonneg (a + b - 2 * Real.sqrt (a * b)), 
          Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), 
          Real.sqrt_nonneg (a * b), 
          sq_nonneg (Real.sqrt ((a ^ 2 + b ^ 2) / 2) ^ 2 - Real.sqrt (a * b) ^ 2), 
          mul_nonneg (show 0 ≤ Real.sqrt 2 by positivity) (show 0 ≤ (a + b) by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) by positivity) (show 0 ≤ Real.sqrt 2 by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) by positivity) (show 0 ≤ (a + b) by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt (a * b) by positivity) (show 0 ≤ Real.sqrt 2 by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt (a * b) by positivity) (show 0 ≤ (a + b) by positivity)
        ]
      have h30 : (Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b)) ≤ (a - b) ^ 2 / (Real.sqrt 2 * (a + b)) := by
        have h27 : Real.sqrt 2 * (a + b) > 0 := by positivity
        apply (le_div_iff₀ (by positivity)).mpr 
        nlinarith [h19a, Real.sqrt_nonneg 2, Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b)]
      linarith
    exact h4