import Mathlib

theorem algebra_259807 (a b c d : ℝ) (h : a * b + b * c + c * d + d * a = 16) :
    (a + b ≤ 4 ∨ a + c ≤ 4 ∨ a + d ≤ 4 ∨ b + c ≤ 4 ∨ b + d ≤ 4 ∨ c + d ≤ 4) ∧
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 16 := by
  constructor
  · -- Assume that all pairs sum to more than 4, derive a contradiction
    by_contra h1
    push_neg at h1
    nlinarith [sq_nonneg (a + b - 4), sq_nonneg (a + c - 4), sq_nonneg (a + d - 4),
              sq_nonneg (b + c - 4), sq_nonneg (b + d - 4), sq_nonneg (c + d - 4),
              sq_nonneg (a + c - (b + d)), sq_nonneg (a + d - (b + c)), sq_nonneg (b + a - (c + d))]
  · -- Prove that $a^2 + b^2 + c^2 + d^2 \geq 16$
    have h1 : (a + c) * (b + d) = 16 := by 
      nlinarith
    nlinarith [sq_nonneg (a + b - (c + d)), sq_nonneg (a - b + c - d),
              sq_nonneg (a - c), sq_nonneg (b - d),
              sq_nonneg (a + c - (b + d)), sq_nonneg (a + b + c + d)
            ]