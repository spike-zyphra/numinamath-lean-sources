import Mathlib

theorem algebra_221349 (a b c d : ℝ) :
    a^2 + b^2 + c^2 + d^2 - a * b - b * c - c * d - d + 2 / 5 = 0 ↔
    a = 1 / 5 ∧ b = 2 / 5 ∧ c = 3 / 5 ∧ d = 4 / 5 := by

  constructor
  · -- Forward direction: if the equation holds, then a,b,c,d have the given values.
    intro h

    have h1 : (a - 1 / 5) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), 
        sq_nonneg (c - 3 / 5), sq_nonneg (d - 4 / 5), 
        sq_nonneg (a - b + 1 / 5), sq_nonneg (b - c + 1 / 5), 
        sq_nonneg (c - d + 1 / 5)
      ]
    
    have ha : a = 1 / 5 := by
      nlinarith

    have hb : b = 2 / 5 := by
      nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), 
        sq_nonneg (c - 3 / 5), sq_nonneg (d - 4 / 5), 
        sq_nonneg (a - b + 1 / 5), sq_nonneg (b - c + 1 / 5), 
        sq_nonneg (c - d + 1 / 5)
      ]

    have hc : c = 3 / 5 := by 
      nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), 
        sq_nonneg (c - 3 / 5), sq_nonneg (d - 4 / 5), 
        sq_nonneg (a - b + 1 / 5), sq_nonneg (b - c + 1 / 5), 
        sq_nonneg (c - d + 1 / 5)
      ]

    have hd : d = 4 / 5 := by
      nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), 
        sq_nonneg (c - 3 / 5), sq_nonneg (d - 4 / 5), 
        sq_nonneg (a - b + 1 / 5), sq_nonneg (b - c + 1 / 5), 
        sq_nonneg (c - d + 1 / 5)
      ]

    exact ⟨ha, hb, hc, hd⟩

  · -- Backward direction: if a,b,c,d have the given values, then the equation holds.
    rintro ⟨ha, hb, hc, hd⟩
    rw [ha, hb, hc, hd]
    norm_num