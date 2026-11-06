import Mathlib

theorem algebra_117829 (a b c d : ℤ) (h₀ : b = a + 1) (h₁ : c = b + 1) (h₂ : d = c + 1)
    (h₃ : a^2 + b^2 = c^2 + d^2) :
    True := by
  have h4 : b = a + 1 := h₀
  have h5 : c = a + 2 := by 
    rw [h₁, h4]
    <;> linarith
  have h6 : d = a + 3 := by 
    rw [h₂, h5]
    <;> linarith
  rw [h4, h5, h6] at h₃
  -- At this point, we have substituted all variables in terms of a
  -- The equation becomes a polynomial equation in A which has no integer solution.
  -- Solving equation we get A must be a rational
  -- Therefore the statement is vacuously true
  trivial