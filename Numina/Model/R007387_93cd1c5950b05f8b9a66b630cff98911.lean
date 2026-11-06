import Mathlib

theorem algebra_18721 (f g X : Polynomial ℤ) (hX : X = Polynomial.X) (hf : f = 7 * X ^ 4 - 3 * X ^ 3 - 3 * X ^ 2 - 8 * X + 1)
    (hg : g = 8 * X ^ 4 + 2 * X ^ 3 - 7 * X ^ 2 + 3 * X + 4) :
    (f * g).coeff 3 = 37 := by 
  rw [hf, hg, hX]
  ring_nf
  <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt]
  <;> rfl