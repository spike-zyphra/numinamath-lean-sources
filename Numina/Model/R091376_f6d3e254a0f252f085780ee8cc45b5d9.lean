import Mathlib

theorem algebra_405 {a b c d : ℝ}
    (h₀ : a^2 + c^2 = 1) (h₁ : b^2 + d^2 = 1) (h₂ : a * d - b * c = 1) :
    a * b + c * d = 0 := by 
  -- Prove (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) = 1
  have h₃ : (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) = 1 := by
    rw [h₀, h₁]
    norm_num
  -- Prove (a * d - b * c) ^ 2 = 1
  have h₄ : (a * d - b * c) ^ 2 = 1 := by 
    rw [h₂]
    norm_num
  -- Prove (a * b + c * d) ^ 2 = 0
  have h₅ : (a * b + c * d) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c), sq_nonneg (a * b + c * d),
          h₃, h₄]
  -- From $(ab + cd)^2 = 0$, we get $ab + cd = 0$
  have h₆ : a * b + c * d = 0 := by 
    nlinarith [sq_nonneg (a * b + c * d)]
  exact h₆