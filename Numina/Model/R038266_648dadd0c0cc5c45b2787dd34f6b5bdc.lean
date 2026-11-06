import Mathlib

theorem algebra_190704 (a b c : ℝ) :
    ∃ x, x^2 + (a - b) * x + (b - c) = 0 ∨
    x^2 + (b - c) * x + (c - a) = 0 ∨
    x^2 + (c - a) * x + (a - b) = 0 := by
  by_cases h₁ : (a - b) ^ 2 - 4 * (b - c) ≥ 0
  · use (- (a - b) + Real.sqrt ((a - b) ^2 - 4 * (b - c))) / 2
    left 
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    linarith
  · -- Assume not, then check second equation
    by_cases h₂ : (b - c) ^ 2 - 4 * (c - a) ≥ 0
    · use (- (b - c) + Real.sqrt ((b - c) ^2 - 4 * (c - a))) / 2
      right 
      left 
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      linarith 
    · -- Assume none of the first two discriminant is non-negative 
      have h₃ : (c - a) ^ 2 - 4 * (a - b) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg ((a - b) + (b - c) + (c - a)), sq_nonneg ((a - b) - (b - c)), sq_nonneg ((b - c) - (c - a)), sq_nonneg ((c - a) - (a - b))]
      use (- (c - a) + Real.sqrt ((c - a) ^2 - 4 * (a - b))) / 2
      right 
      right
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      linarith