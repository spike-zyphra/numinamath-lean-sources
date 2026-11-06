import Mathlib

theorem algebra_3755
    (x : ℝ)
    (hx : 2 * Real.sqrt (-2 * x ^ 2 + 5 * x + 7) = x ^ 3 - 3 * x ^ 2 - x + 12 ∧ 0 ≤ -(2*x^2-5*x-7)) :
    x = 2 := by
  rcases hx with ⟨h1, h2⟩
  have h3 : -2 * x^2 + 5 * x + 7 ≥ 0 := by
    linarith
  have h4 : Real.sqrt (-2 * x ^ 2 + 5 * x + 7) ≥ 0 := by positivity
  have h5 : (Real.sqrt (-2 * x ^ 2 + 5 * x + 7)) ^ 2 = -2 * x^2 + 5 * x + 7 := by
    rw [Real.sq_sqrt]
    linarith
  have h6 : 2 * Real.sqrt (-2 * x ^ 2 + 5 * x + 7) = x ^ 3 - 3 * x ^ 2 - x + 12 := h1
  have h7 : (2 * Real.sqrt (-2 * x ^ 2 + 5 * x + 7)) ^ 2 = (x ^ 3 - 3 * x ^ 2 - x + 12) ^ 2 := by
    rw [h6]
  have h8 : (2 * Real.sqrt (-2 * x ^ 2 + 5 * x + 7)) ^ 2 = 4 * (-2 * x^2 + 5 * x + 7) := by
    calc
      (2 * Real.sqrt (-2 * x ^ 2 + 5 * x + 7)) ^ 2
          = 4 * (Real.sqrt (-2 * x ^ 2 + 5 * x + 7) )^ 2 := by ring
      _ = 4 * (-2 * x ^ 2 + 5 * x + 7) := by 
        rw [h5]
  rw [h8] at h7
  have h9 : (x - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - 2 * x - 3), sq_nonneg (x - 2), sq_nonneg (Real.sqrt (-2 * x ^ 2 + 5 * x + 7) - 3), Real.sqrt_nonneg (-2 * x ^ 2 + 5 * x + 7)]
  have h99 : x - 2 = 0 := by
    nlinarith
  linarith