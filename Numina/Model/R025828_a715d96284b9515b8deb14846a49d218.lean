import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem algebra_5136 {x y : ℝ} (h₀ : 3 * x^3 + x * y^2 = 93) (h₁ : y^3 + 27 * x^2 * y = 494) :
    x^2 + y^2 = 13 := by

  have h2 : (x - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (x + 3), sq_nonneg (y + 2), 
      sq_nonneg (x * y - 6), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (x * (x - 3)), sq_nonneg (y * (y - 2))
    ]
  have hx1 : x - 3 = 0 := by 
    nlinarith 
  have hx2 : x = 3 := by 
    linarith 
  have h4 : y = 2 := by 
    rw [hx2] at h₁ 
    have h5 : y ^ 2 = 4 := by 
      rw [hx2] at h₀ 
      nlinarith 
    have h6 : y = 2 ∨ y = -2 := by 
      have h7 : y ^ 2 - 4 = 0 := by
        nlinarith 
      have h8 : (y - 2) * (y + 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h8) with h9 h10 
      · left 
        linarith 
      · right 
        linarith 
    cases h6 with 
    | inl h => 
      linarith 
    | inr h => 
      nlinarith 
  have h5 : x ^ 2 + y ^ 2 = 13 := by 
    rw [hx2, h4]
    norm_num 
  linarith