import Mathlib
 
 theorem algebra_113766 {x : ℕ} (hl : 1900 ≤ x^2 ∧ x^2 ≤ 2017) (h : Nat.sqrt (x^2 - 1900) = (x / 4 - 4) - Nat.sqrt (2017 - x^2)) : x = 44 := by
  have h1 : x ≤ 44 := by
    nlinarith [hl.right, show 45 ^ 2 > 2017 by norm_num]
  have h2 : x ≥ 44 := by
    by_contra h2
    push_neg at h2
    have h3 : x ≤ 43 := by
      omega
    have h4 : x ^ 2 ≤ 1849 := by
      have : x ≤ 43 := h3
      nlinarith [sq_nonneg (x : ℕ), sq_nonneg ((43 : ℕ) : ℕ)]
    nlinarith [hl.left, h4]
  have h3 : x = 44 := by
    omega
  exact h3