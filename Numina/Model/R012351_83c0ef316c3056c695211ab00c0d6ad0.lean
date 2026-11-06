import Mathlib

theorem algebra_213785 {x y : ℝ} (h1 : x^2 + x^2 * y^2 + x^2 * y^4 = 525) (h2 : x + x * y + x * y^2 = 35) :
    (x = 5 ∧ y = 2) ∨ (x = 20 ∧ y = 1 / 2) := by
  have eq1 : x * (1 + y + y^2) = 35 := by
    ring_nf at h2 ⊢
    linarith 
  have eq2 : x^2 * (1 + y^2 + y^4) = 525 := by
    ring_nf at h1 ⊢
    nlinarith 
  have eq3 : (1 + y^2 + y^4) = (1 + y + y^2) * (1 - y + y^2) := by 
    ring 
  rw [eq3] at eq2 
  have eq4 : x * (1 - y + y^2) = 15 := by
    nlinarith [sq_nonneg (x * (1 + y + y^2) - 35), sq_nonneg (x * y - 10), 
        sq_nonneg (y - 2), sq_nonneg (y - 1 / 2), 
        sq_nonneg (x - 5), sq_nonneg (x - 20)
    ]
  have eq5 : x * y = 10 := by
    nlinarith [eq1, eq4]
  have h3 : (y - 2) * (y - 1 / 2) = 0 := by
    nlinarith [sq_nonneg (x * y - 10), sq_nonneg (x - 5), sq_nonneg (x - 20), 
        sq_nonneg (y - 2), sq_nonneg (y - 1 / 2)
    ]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case y = 2
    have hy : y = 2 := by
      linarith 
    have hx : x = 5 := by 
      nlinarith [eq5, hy]
    left 
    constructor 
    · -- Show x = 5
      linarith 
    · -- Show y = 2
      linarith 
  · -- Case y = 1/2
    have hy : y = 1 / 2 := by 
      linarith 
    have hx : x = 20 := by
      nlinarith [eq5, hy]
    right 
    constructor 
    · -- Show x  = 20 
      linarith 
    · -- Show y = 1 / 2 
      linarith