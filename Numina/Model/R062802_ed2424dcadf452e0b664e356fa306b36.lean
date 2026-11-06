import Mathlib

theorem algebra_195995 (x y : ℝ) :
    (x - 6)^2 + (y - 7)^2 + (x - y)^2 = 1 / 3 ↔
    x = 6 + 1 / 3 ∧ y = 6 + 2 / 3 := by 
  constructor
  · -- Forward direction: If (x-6)^2 + (y-7)^2 + (x-y)^2 = 1/3, then x = 6 + 1/3 ∧ y = 6 + 2/3
    intro h_eq
    have h_eq1 : (x - 19 / 3) ^ 2 + (y - 20 / 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 19 / 3), sq_nonneg (y - 20 / 3), sq_nonneg (x - (y)), sq_nonneg (x + y - 15 / 3)
      ]
    have hx1 : x - 19 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 19 / 3), sq_nonneg (y - 20 / 3)
      ]
    have hy1 : y - 20 / 3 = 0 := by
      nlinarith [sq_nonneg (x - 19 / 3), sq_nonneg (y - 20 / 3)
      ]
    constructor 
    · -- Prove x = 6 + 1/3
      linarith 
    · -- Prove y = 6 + 2/3
      linarith 
  · -- Backward direction: If x = 6 + 1/3 ∧ y = 6 + 2/3, then (x-6)^2 + (y-7)^2 + (x-y)^2 = 1/3
    rintro ⟨rfl, rfl⟩
    norm_num