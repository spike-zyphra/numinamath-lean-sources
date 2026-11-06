import Mathlib

theorem algebra_266495 (x y z w : ℤ) (h₁ : x * y = 6) (h₂ : x * z = 12)
    (h₃ : z * w = 50) (h₄ : 12 * 25 = x * w) :
    x * w = 150 := by
  have h5 : x * w = 300 := by 
    linarith
  have h6 : x * w * z ^ 2 = 600 := by
    calc
      x * w * z ^ 2 = (x * z) * (z * w) := by
        ring
      _ = 12 * 50 := by
        rw [h₂, h₃]
      _ = 600 := by
        norm_num
  have h7 : z ^ 2 = 2 := by
    rw [h5] at h6
    have h8 : (300 : ℤ) * z ^ 2 = 600 := by 
      nlinarith
    have h9 : z ^ 2 = 2 := by
      nlinarith
    exact h9
  have h14 : z ^ 2 < 3 := by 
    omega
  have h15 : z ≤ 1 := by
    nlinarith [sq_nonneg (z - 1 : ℤ)]
  have h16 : z ≥ -1 := by
    nlinarith [sq_nonneg (z + 1 : ℤ)]
  interval_cases z <;> omega -- contradiction