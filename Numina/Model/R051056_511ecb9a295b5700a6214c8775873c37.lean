import Mathlib

theorem algebra_295832 {P : Polynomial ℤ} (a b : ℤ) :
    (b - a) ∣ P.eval b - P.eval a := by
  apply Polynomial.sub_dvd_eval_sub