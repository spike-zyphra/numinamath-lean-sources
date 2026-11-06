import Mathlib

theorem algebra_165592 (a : Fin 4 → ℝ)
    (h₀ : 0 ≤ a 0) (h₁ : 0 ≤ a 1 - 1) (h₂ : 0 ≤ a 2 - 2) (h₃ : 0 ≤ a 3 - 3)
    (h₄ : Real.sqrt (a 0) + Real.sqrt (a 1 - 1) + Real.sqrt (a 2 - 2) + Real.sqrt (a 3 - 3) =
      (a 0 + a 1 + a 2 + a 3) / 2 - 1) :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 := by

  have h5 : 2 * (Real.sqrt (a 0) + Real.sqrt (a 1 - 1) + Real.sqrt (a 2 - 2) + Real.sqrt (a 3 - 3)) =
    a 0 + a 1 + a 2 + a 3 - 2 := by
    linarith

  have h6 : 2 * Real.sqrt (a 0) = a 0 + 1 := by
    nlinarith [h5, sq_nonneg (Real.sqrt (a 0) - 1), sq_nonneg (Real.sqrt (a 1 - 1) - 1), sq_nonneg (Real.sqrt (a 2 - 2) - 1), sq_nonneg (Real.sqrt (a 3 - 3) - 1),
      Real.sq_sqrt h₀, Real.sq_sqrt h₁, Real.sq_sqrt h₂, Real.sq_sqrt h₃
    ]

  have ha0 : a 0 = 1 := by
    nlinarith [sq_nonneg (Real.sqrt (a 0) - 1), Real.sq_sqrt h₀
    ]
  
  have h7 : 2 * Real.sqrt (a 1 - 1) = a 1 := by
    nlinarith [h5, sq_nonneg (Real.sqrt (a 0) - 1), sq_nonneg (Real.sqrt (a 1 - 1) - 1), sq_nonneg (Real.sqrt (a 2 - 2) - 1), sq_nonneg (Real.sqrt (a 3 - 3) - 1),
      Real.sq_sqrt h₀, Real.sq_sqrt h₁, Real.sq_sqrt h₂, Real.sq_sqrt h₃
    ]

  have ha1 : a 1 = 2 := by
    nlinarith [sq_nonneg (Real.sqrt (a 1 - 1) - 1), Real.sq_sqrt h₁
    ]
  
  have h8 : 2 * Real.sqrt (a 2 - 2) = a 2 - 1 := by
    nlinarith [h5, sq_nonneg (Real.sqrt (a 0) - 1), sq_nonneg (Real.sqrt (a 1 - 1) - 1), sq_nonneg (Real.sqrt (a 2 - 2) - 1), sq_nonneg (Real.sqrt (a 3 - 3) - 1),
      Real.sq_sqrt h₀, Real.sq_sqrt h₁, Real.sq_sqrt h₂, Real.sq_sqrt h₃
    ]

  have ha2 : a 2 = 3 := by
    nlinarith [sq_nonneg (Real.sqrt (a 2 - 2) - 1), Real.sq_sqrt h₂
    ]
  
  have h9 : 2 * Real.sqrt (a 3 - 3) = a 3 - 2 := by
    nlinarith [h5, sq_nonneg (Real.sqrt (a 0) - 1), sq_nonneg (Real.sqrt (a 1 - 1) - 1), sq_nonneg (Real.sqrt (a 2 - 2) - 1), sq_nonneg (Real.sqrt (a 3 - 3) - 1),
      Real.sq_sqrt h₀, Real.sq_sqrt h₁, Real.sq_sqrt h₂, Real.sq_sqrt h₃
    ]

  have ha3 : a 3 = 4 := by
    nlinarith [sq_nonneg (Real.sqrt (a 3 - 3) - 1), Real.sq_sqrt h₃
    ]
  
  exact ⟨ha0, ha1, ha2, ha3⟩