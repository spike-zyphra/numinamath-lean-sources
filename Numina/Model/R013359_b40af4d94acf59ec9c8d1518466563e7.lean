import Mathlib

theorem algebra_2059 (x y : ℝ) :
    (x - y)^2 + (x^2 + y^2 - 12 * y + 35)^4 = 17 ↔ (x = 1 ∧ y = 5) := by
  constructor
  · -- Assume the equation holds, prove (x = 1 ∧ y = 5)
    intro h_eq
    have h3 : (x - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((x - 1) ), sq_nonneg ((y - 5) ), sq_nonneg ((x - y ) - 4), sq_nonneg ((x^2 + y^2 - 12 * y + 35) - 1), 
        sq_nonneg ((x + y) - 6), sq_nonneg (x - 1 + (y - 5)), sq_nonneg (x - y),
          sq_nonneg ((x^2 + y^2 - 12 * y + 35) ^ 2 - 1)
        ]
    have h4 : x - 1 = 0 := by
      apply pow_eq_zero 
      exact h3
    have h4' : x = 1 := by linarith
    have h5 : (y - 5) ^ 2 = 0 := by
      rw [h4'] at h_eq
      nlinarith [sq_nonneg ((y - 5) ), sq_nonneg ((y - 6) ), sq_nonneg ((y - 6) ^ 2 - 1), sq_nonneg ((y - 5) ^ 2 - 0), sq_nonneg ((y) - 5)]
    have h6 : y - 5 = 0 := by
      apply pow_eq_zero 
      exact h5
    have h7' : y = 5 := by linarith
    exact ⟨h4', h7'⟩
  · -- Assume (x = 1 ∧ y = 5), prove the equation
    rintro ⟨rfl, rfl⟩
    norm_num