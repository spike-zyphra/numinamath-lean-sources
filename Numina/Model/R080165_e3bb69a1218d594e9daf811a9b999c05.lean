import Mathlib

theorem algebra_4564 {p q : ℝ} (h : ∀ x : ℝ, x^4 + 256 = (x^2 + p * x + 16) * (x^2 + q * x + 16)) :
    p^2 + q^2 = 64 := by 
  have eq1 := h 1
  have eq2 := h (-1 : ℝ)
  have eq3 := h 2
  have eq4 := h (-2 : ℝ)
  have eq5 := h 3
  have eq6 := h (-3 : ℝ)
  ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + q), sq_nonneg (p * q), sq_nonneg (p ^ 2), sq_nonneg (q ^ 2)]