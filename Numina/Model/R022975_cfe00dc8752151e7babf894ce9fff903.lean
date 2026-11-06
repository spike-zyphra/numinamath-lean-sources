import Mathlib

def T_type (x : ℤ) := ∃ a b, x = a^2 + a * b + b^2

theorem number_theory_205723 {x : ℤ} (hx : T_type x) :
    T_type (x^2) := by 
  rcases hx with ⟨a, b, hx⟩
  use a^2 - b^2
  use 2 * a * b + b^2
  rw [show x^2 = (a^2 + a * b + b^2)^2 by rw [hx]]
  nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b), sq_nonneg (a), sq_nonneg (a * (a - b)), sq_nonneg ((2 * a * b + b^2) - (a^2 - b^2)), sq_nonneg ((2 * a * b + b^2) + (a^2 - b^2))]