import Mathlib

theorem number_theory_132184 {P : Polynomial ℤ} (a b : ℤ) :
    (a - b) ∣ P.eval a - P.eval b := by
  apply Polynomial.sub_dvd_eval_sub