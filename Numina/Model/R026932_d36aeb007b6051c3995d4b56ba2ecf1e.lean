import Mathlib

theorem algebra_7812 (x y z : ℤ) (h₀ : 0 < x) (h₁ : 0 < y) (h₂ : 0 < z)
    (h₃ : 7 * x ^ 2 - 3 * y ^ 2 + 4 * z ^ 2 = 8) (h₄ : 16 * x ^ 2 - 7 * y ^ 2 + 9 * z ^ 2 = -3) :
    x ^ 2 + y ^ 2 + z ^ 2 = 165 := by
  have h5 : y^2 = x^2 + 84 := by
    nlinarith
  have h6 : z^2 = 65 - x^2 := by
    nlinarith [h₃, h₄, h5]
  have h7 : x ≤ 8 := by
    nlinarith [show x ^ 2 < 65 by nlinarith [h6, sq_nonneg (z : ℤ), sq_nonneg (y : ℤ)]]
  have h8 : x ≥ 1 := by
    linarith
  interval_cases x <;> try { 
    norm_num at h5 h6 h₃ h₄
    all_goals
      have h9 : y ≤ 30 := by
        nlinarith [sq_nonneg (y : ℤ)]
      have h10 : y ≥ 1 := by
        linarith
      interval_cases y <;> try { 
        norm_num at h5 h₃ h₄
        all_goals 
          have h11 : z ≤ 30 := by
            nlinarith [sq_nonneg (z : ℤ)]
          have h12 : z ≥ 1 := by 
            linarith
          interval_cases z <;> omega 
      }
  }
  all_goals
    omega