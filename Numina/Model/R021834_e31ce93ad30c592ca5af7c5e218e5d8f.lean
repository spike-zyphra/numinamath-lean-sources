import Mathlib

theorem algebra_145938 (a b c : ℝ) (ha : a ≠ 0) (hroots : ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ 0)
    (hsum : a + b + c > 0) : c > 0 := by 
  by_contra h
  push_neg at h
  have h1 : c ≤ 0 := by linarith
  have h2 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
    by_cases ha1 : a > 0
    · 
      -- Let's assume ha1, that a > 0.
      have h3 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
        use (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
        field_simp [show a ≠ 0 by exact ha]
        have h10 : b ^ 2 - 4 * a * c ≥ 0 := by
          nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ -c by linarith)]
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ -c by linarith)] )
        ]
      assumption
    · 
      -- Now ha1 is ¬ a > 0.
      have ha2 : a ≤ 0 := by linarith
      have ha3 : a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        contradiction
      have h4 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
        use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
        field_simp [show a ≠ 0 by exact ha]
        have h10 : b ^ 2 - 4 * a * c ≥ 0 := by
          nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -c by linarith), sq_nonneg (a), sq_nonneg (c)]
        nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sq_sqrt (show (b ^ 2 - 4 * a * c) ≥ 0 by nlinarith [sq_nonneg (b + 2 * a), sq_nonneg (b - 2 * a), mul_nonneg (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -c by linarith), sq_nonneg (a), sq_nonneg (c)]
        )
        ]
      assumption
  rcases h2 with ⟨x, hx⟩
  have h3 : a * x ^ 2 + b * x + c = 0 := by 
    nlinarith
  have h3' : a * x ^ 2 + b * x + c ≠ 0 := hroots x
  contradiction