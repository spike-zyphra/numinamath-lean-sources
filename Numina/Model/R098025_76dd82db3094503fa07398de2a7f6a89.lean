import Mathlib

theorem algebra_183464 (a b c : ℝ) :
    ∃ x : ℝ, x^2 + (a - b)*x + (b - c) = 0 ∨
                  x^2 + (b - c)*x + (c - a) = 0 ∨
                  x^2 + (c - a)*x + (a - b) = 0 := by
  by_cases h₁ : (a - b) ^ 2 - 4 * (b - c) ≥ 0
  · -- First equation has real roots
    use (- (a - b) + Real.sqrt ((a - b) ^ 2 - 4 * (b - c))) / 2
    left
    nlinarith [Real.sqrt_nonneg ((a - b) ^ 2 - 4 * (b - c)), Real.sq_sqrt ((show (a - b) ^ 2 - 4 * (b - c) ≥ 0 by linarith))]
  
  · -- First equation doesn't have real roots, check second
    by_cases h₂ : (b - c) ^ 2 - 4 * (c - a) ≥ 0
    · -- Second equation has real roots
      use (- (b - c) + Real.sqrt ((b - c) ^ 2 - 4 * (c - a))) / 2
      right
      left
      nlinarith [Real.sqrt_nonneg ((b - c) ^ 2 - 4 * (c - a)), Real.sq_sqrt ((show (b - c) ^ 2 - 4 * (c - a) ≥ 0 by linarith))]
    
    · -- Second equation doesn't have real roots, check third
      have h₃ : (c - a) ^ 2 - 4 * (a - b) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      -- Third equation has real roots
      use (- (c - a) + Real.sqrt ((c - a) ^ 2 - 4 * (a - b))) / 2
      right
      right
      nlinarith [Real.sqrt_nonneg ((c - a) ^ 2 - 4 * (a - b)), Real.sq_sqrt ((show (c - a) ^ 2 - 4 * (a - b) ≥ 0 by linarith))]