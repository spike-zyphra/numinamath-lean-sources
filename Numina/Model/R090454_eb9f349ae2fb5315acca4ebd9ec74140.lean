import Mathlib

theorem algebra_241602 {a b c : ℝ} (h : a^3 * b^3 + b^3 * c^3 + c^3 * a^3 = a * b * c * (a^3 + b^3 + c^3)) :
    IsSquare (a * b) ∨ IsSquare (b * c) ∨ IsSquare (a * c) := by
  by_cases h₁ : a * b ≥ 0
  · -- If $a * b \geq 0$, then $IsSquare(a * b)$
    left
    use Real.sqrt (a * b)
    nlinarith [Real.sq_sqrt (show 0 ≤ a * b by linarith)]
  · -- If $a * b < 0$, consider the other cases
    by_cases h₂ : b * c ≥ 0
    · -- If $b * c \geq 0$, then $IsSquare(b * c)$
      right
      left
      use Real.sqrt (b * c)
      nlinarith [Real.sq_sqrt (show 0 ≤ b * c by linarith)]
    · -- If $b * c < 0$, consider the last case
      by_cases h₃ : a * c ≥ 0
      · -- If $a * c \geq 0$, then $IsSquare(a * c)$
        right
        right
        use Real.sqrt (a * c)
        nlinarith [Real.sq_sqrt (show 0 ≤ a * c by linarith)]
      · -- If $a * c < 0$, derive a contradiction
        have h₄ : a * b < 0 := by linarith
        have h₅ : b * c < 0 := by linarith
        have h₆ : a * c < 0 := by linarith
        nlinarith [sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (a * c), 
          sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]